(** The entrypoint for the pplcore executable. Handles command line argument
    open Utest
    parsing, unit testing, and lexing/parsing. *)

open Ast
open Printf
open Sprint
open Utils
open Debug
open Infer
open Utest

type output =
  | None
  | Debug
  | Dist
  | Norm

let output = ref Debug

(** Add a slash at the end of a path if not already available *)
let add_slash s =
  if String.length s = 0 || (String.sub s (String.length s - 1) 1) <> "/"
  then s ^ "/" else s

(** Expand a list of files and folders into a list of file names *)
let files_of_folders lst = List.fold_left (fun a v ->
    if Sys.is_directory v then
      (Sys.readdir v
       |> Array.to_list
       |> List.filter (fun x ->
           not (String.length x >= 1 && String.get x 0 = '.'))
       |> List.map (fun x -> (add_slash v) ^ x)
       |> List.filter (fun x -> not (Sys.is_directory x))
      ) @ a
    else v::a
  ) [] lst

(** Function for lexing and parsing a file, parameterized by a parser as
    generated by ocamlyacc and ocamllex *)
let parse par filename =
  let file = open_in filename in
  let lexbuf = Lexing.from_channel file in
  begin try
      lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
      let tm = par lexbuf in
      close_in file; tm
    with | Parsing.Parse_error ->
      if !utest then (
        printf "\n** Parse error at %s **"
          (string_of_position (lexbuf.lex_curr_p));
        utest_fail := !utest_fail + 1;
        utest_fail_local := !utest_fail_local + 1;
        nop)
      else
        failwith (sprintf "Parse error at %s"
                    (string_of_position (lexbuf.lex_curr_p)))
  end

(** Function for running inference on a program. *)
let exec filename =

  (* If running unit testing, set the inference to SMC so that the CPS
     transformation is also tested *)
  if !utest then begin
    printf "%s: " filename;
    inference := SMCDirect; (* TODO *)
    samples   := 1;
    output    := None;
  end;
  utest_fail_local := 0;

  (* Parse the program *)
  let tm = match Filename.extension filename with
    | ".ppl"  -> parse (Parser.main Lexer.main) filename
    | ".tppl" -> parse (Tpplparser.main Tppllexer.main) filename
    | s       -> failwith ("Unsupported file type: " ^ s) in

  debug debug_input "Input term" (fun () -> string_of_tm tm);

  (* Run inference *)
  let normconst,res = infer tm in

  (* TODO Add a plot function using some nice library *)
  (* Print output of inference *)
  begin match !output with
    | None -> ()
    | Debug ->
      debug true "Inference result"
        (fun () -> string_of_empirical res);
      debug true "Log Normalizing constant"
        (fun () -> sprintf "%f" normconst)
    | Dist ->
      print_endline (string_of_empirical res)
    | Norm ->
      printf "%f" normconst
  end;

  (* Print unit testing information for this file *)
  utest_local_print()

(** Main function. Parses command line arguments *)
let main =
  let speclist = [

    "--test",
    Arg.Unit(fun _ -> utest := true),
    " Enable unit tests.";

    "--inference",
    Arg.String(fun s -> match s with
        | "is"          -> inference := Importance
        | "smc-direct"  -> inference := SMCDirect
        | "smc-manual"  -> inference := SMCManual
        | "smc-dynamic" -> inference := SMCDynamic
        | "smc-static"  -> inference := SMCStatic
        | "eval"        -> inference := Eval
        | _             -> failwith "Incorrect inference algorithm"
      ),
    " Specifies inference method. Options are: eval, is,\
     smc-direct, smc-manual, smc-dynamic, and smc-static.";

    "--output",
    Arg.String(fun s -> match s with
        | "none"  -> output := None
        | "debug" -> output := Debug
        | "dist"  -> output := Dist
        | "norm"  -> output := Norm
        | _       -> failwith "Incorrect output format"
      ),
    " Specifies output format. Options are: none, debug, dist, norm.";

    "--samples",
    Arg.Int(fun i -> match i with
        | i when i < 1 -> failwith "Number of samples must be positive"
        | i            -> samples := i),
    " Specifies the number of samples in affected inference algorithms.";

  ] in

  let speclist = Arg.align speclist in
  let lst = ref [] in
  let anon_fun arg = lst := arg :: !lst in
  let usage_msg = "" in

  Arg.parse speclist anon_fun usage_msg;

  List.iter exec (files_of_folders !lst);

  utest_print ();

