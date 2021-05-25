include "pgm.mc"

type Env = Map Name Expr

lang Transformation = ProbabilisticGraphicalModel

  sem collect (ctx:{assumeMap:Map Name Expr, observeAssumeMap:Map Name Name, env:Env}) =
  | TmLet ({body = TmAssume a} & t) -> let assumeMap =
    match a.dist with TmDist {dist = DBeta b} then
      mapInsert t.ident t.body ctx.assumeMap
    else ctx.assumeMap in
    collect {ctx with assumeMap=assumeMap} t.inexpr
  | TmLet ({body = TmObserve o} & t) ->
    let updatedCtx =
      match o.dist with TmDist {dist = DBern b} then
        match b.p with TmVar v then
          match mapLookup v.ident ctx.assumeMap with Some (TmAssume a) then -- update assume
            {{ctx with assumeMap= (mapInsert v.ident (TmAssume {a with dist=(updateAssume (getValue ctx.env (o.value)) a.dist)}) ctx.assumeMap)} with
            /-getValue because if var is used as value then need to carry that too-/
            observeAssumeMap = mapInsert t.ident v.ident ctx.observeAssumeMap}
          else ctx
        else ctx
      else ctx
    in collect updatedCtx t.inexpr
  /-| TmLet ({body = TmPlate p} & t) ->
      /-
      two cases: 
      1) in plate observe list contains observed values 
      let obs = [true, false, true, false] in
      let rv = assume (Beta a b) in
      plate (lam x. observe x (Bern rv)) obs
      assume Beta (foldl (lam x. lam acc. if x then addf acc 1.0 else acc) a obs) (foldl (lam x. lam acc. if x then acc else addi acc 1.0) b obs) 
      2) in plate observe list contains random variables
    transformed:
      let rvs = plate (lam x. assume (Beta x.0 x.1)) params in
      plate (lam x. observe val (Bern x)) rvs
      -/
    match p.fun with TmLam l then
      (match l.body with TmAssume {dist = (TmDist {dist = DBeta b})} then
        collect {ctx with assumeMap=mapInsert t.ident t.body ctx.assumeMap} t.inexpr
      else
        match l.body with TmObserve {value= val, dist = (TmDist {dist = DBern b})} then
          -- Case 1
          match val with TmVar {ident=l.ident} then
            match b.p with TmVar v then
              match mapLookup v.ident ctx.assumeMap with Some (TmAssume a) then
                -- p.lst contains the observed values
                let updatedDist =  foldl (lam acc. lam o. updateAssume o acc) a.dist p.lst in
                collect {{ctx with assumeMap= (mapInsert v.ident {a with dist=updatedDist} ctx.assumeMap)} with
                observeAssumeMap = mapInsert t.ident v.ident ctx.observeAssumeMap} t.inexpr
              else collect ctx t.inexpr
            else  collect ctx t.inexpr
          else -- Case 2
        else never -- lambda body can only be assume or observe
        )
    else never -- fun of plate should be a lambda
  -/
  | TmLet t -> collect {ctx with env = (mapInsert t.ident t.body ctx.env)} t.inexpr
  | t -> sfold_Expr_Expr collect ctx t


  sem getValue (env:Env) =
  | TmVar t -> match mapLookup t.ident env with Some v then
                getValue env v
               else never
  | t -> smap_Expr_Expr (getValue env) t

  sem updateAssume (val:Expr) =
  | TmDist ({dist = DBeta t} & d)-> TmDist {d with dist = (DBeta ({{t with a = (if_ val (addf_ t.a (float_ 1.0)) t.a)} with b=(if_ val t.b (addf_ t.b (float_ 1.0)))}))}
  | t -> t

  sem reconstruct (ctx:{assumeMap:Map Name Expr, observeAssumeMap:Map Name Name, env:Env}) =
  | TmLet t -> match mapLookup t.ident ctx.observeAssumeMap with Some _ then
                  reconstruct ctx t.inexpr
               else match mapLookup t.ident ctx.assumeMap with Some a then
                TmLet {{t with body = a} with inexpr = reconstruct ctx t.inexpr}
              else TmLet {t with inexpr = reconstruct ctx t.inexpr}
  | t -> smap_Expr_Expr (reconstruct ctx) t

  sem getReturn (env:Env) =
  | TmLet t -> getReturn (mapInsert t.ident t.body env) t.inexpr
  | TmAssume t -> Some (TmAssume t)
  | TmVar t -> match (mapLookup t.ident env) with Some v then
                getReturn env v
              else None ()
  | TmSeq t -> smap_Expr_Expr (getReturn env) (TmSeq t)
  | TmPlate t -> match t.fun with TmLam l then
                   getReturn env l.body
                else None ()
  | _ -> None ()
end

lang TestLang = Transformation + MExprPPL

mexpr

use TestLang in

recursive let getSome = lam o. match o with Some t then t else match o with None () then None () else smap_Expr_Expr getSome o
in
let simple1example = use MExprPPL in
  bindall_
  [ ulet_ "X" (assume_ (beta_ (float_ 10.0) (float_ 5.0)))
  , ulet_ "obs" true_
  , ulet_ "" (observe_ (var_ "obs") (bern_ (var_ "X")))
  , var_ "X"
  ] in

let tsimple1example = use MExprPPL in
  bindall_
  [ ulet_ "X" (assume_ (beta_ (if_ true_ (addf_ (float_ 10.0) (float_ 1.0)) (float_ 10.0)) (if_ true_ (float_ 5.0) (addf_ (float_ 5.0) (float_ 1.0)))))
  , ulet_ "obs" true_
  , var_ "X"
  ] in

let tsimple2example = use MExprPPL in
  bindall_
  [ ulet_ "Y" (assume_ (bern_ (divi_ (float_ 10.0) (addi_ (float_ 10.0) (float_ 5.0)))))
  ] in


let example1expanded = use MExprPPL in
  bindall_
  [ ulet_ "theta" (assume_ (beta_ (float_ 10.0) (float_ 10.0)))
  , ulet_ "" (observe_ true_ (bern_ (var_ "theta")))
 -- , ulet_ "" (observe_ false_ (bern_ (var_ "theta")))
 -- , ulet_ "" (observe_ true_ (bern_ (var_ "theta")))
  , (var_ "theta")
  ] in

let texample1expanded = use MExprPPL in
  bindall_
  [ ulet_ "theta" (assume_ (beta_ (if_ true_ (addf_ (float_ 10.0) (float_ 1.0)) (float_ 10.0)) (if_ true_ (float_ 10.0) (addf_ (float_ 10.0) (float_ 1.0))) ))
  , var_ "theta"
  ] in

let example1plate = use MExprPPL in
  bindall_
  [ ulet_ "theta" (assume_ (beta_ (float_ 10.0) (float_ 10.0)))
  , ulet_ "obs" (seq_ [true_, false_, true_])
  , ulet_ "" (plate_ (ulam_ "x" (observe_ (var_ "x") (bern_ (var_ "theta")))) (var_ "obs"))
  , (var_ "theta")
  ] in

let texample1plate = use MExprPPL in
  bindall_
  [ ulet_ "theta" (assume_ (beta_ (addi_ (addi_ (float_ 10.0) (float_ 1.0)) (float_ 1.0)) (addi_ (float_ 10.0) (float_ 1.0))))
  , var_ "theta"
  ] in

let example2expanded = use MExprPPL in
  bindall_
  [ ulet_ "r1" (assume_ (beta_ (float_ 10.0) (float_ 10.0)))
  , ulet_ "r2" (assume_ (beta_ (float_ 15.0) (float_ 1.0)))
  , ulet_ "r3" (assume_ (beta_ (float_ 21.0) (float_ 10.0)))
  , ulet_ "" (observe_ true_ (bern_ (var_ "r1")))
  , ulet_ "" (observe_ false_ (bern_ (var_ "r2")))
  , ulet_ "" (observe_ true_ (bern_ (var_ "r3")))
  , seq_ [var_ "r1", var_ "r2", var_ "r3"]
  ] in

let texample2expanded = use MExprPPL in
 bindall_
  [ ulet_ "r1" (assume_ (beta_ (if_ true_ (addf_ (float_ 10.0) (float_ 1.0)) (float_ 10.0)) (if_ true_ (float_ 10.0) (addf_ (float_ 10.0) (float_ 1.0))) ))
  , ulet_ "r2" (assume_ (beta_ (if_ false_ (addf_ (float_ 15.0) (float_ 1.0)) (float_ 15.0)) (if_ false_ (float_ 1.0) (addf_ (float_ 1.0) (float_ 1.0)))))
  , ulet_ "r3"  (assume_ (beta_ (if_ true_ (addf_ (float_ 21.0) (float_ 1.0)) (float_ 21.0)) (if_ true_ (float_ 10.0) (addf_ (float_ 10.0) (float_ 1.0)))))
  , seq_ [var_ "r1", var_ "r2", var_ "r3"]
  ] in

let example2plate = use MExprPPL in
  bindall_
  [ ulet_ "params" (seq_ [(tuple_ [float_ 10.0,float_ 10.0]), (tuple_ [float_ 15.0,float_ 1.0]), (tuple_ [float_ 21.0,float_ 10.0])])
  , ulet_ "obs" true_
  , ulet_ "rvs" (plate_ (ulam_ "x" (assume_ (beta_ (tupleproj_ 0 (var_ "x")) (tupleproj_ 1 (var_ "x"))))) (var_ "params"))
  , ulet_ "" (plate_ (ulam_ "x" (observe_ (var_ "obs") (bern_ (var_ "x")))) (var_ "rvs"))
  , var_ "rvs"
  ] in

let texample2plate = use MExprPPL in
  bindall_
  [  ulet_ "params" (seq_ [(tuple_ [float_ 10.0,float_ 10.0]), (tuple_ [float_ 15.0,float_ 1.0]), (tuple_ [float_ 21.0,float_ 10.0])])
  , ulet_ "rvs" (plate_ (ulam_ "x" (assume_ (beta_ (tupleproj_ 0 (var_ "x")) (tupleproj_ 1 (var_ "x"))))) (var_ "params"))
  , var_ "rvs"
  ] in

let coinmodel = use MExprPPL in
  bindall_
  [ ulet_ "theta" (assume_ (beta_ (float_ 10.0) (float_ 10.0)))
  , ulet_ "n" (int_ 10)
  , ulet_ "observation" (int_ 1)
  , ulet_ "" (observe_ true (bern_ (var_ "theta")))
  , var_ "theta"
  ] in

let lda = use MExprPPL in
  bindall_
  [ ulet_ "numtopics" (int_ 2) -- the number of topics
  , ulet_ "numdocs" (int_ 3)
  , ulet_ "vocabsize" (int_ 4)
  , ulet_ "vocabulary" (seq_ [int_ 0, int_ 1, int_ 2, int_ 3]) -- word ids
  , ulet_ "docs" (seq_ [int_ 2, int_ 1, int_ 1, int_ 3, int_ 0, int_ 3, int_ 0, int_ 1, int_ 2, int_ 2]) -- word ids for the corpus
  , ulet_ "docids" (seq_ [int_ 0, int_ 0, int_ 0, int_ 1, int_ 1, int_ 1, int_ 1, int_ 2, int_ 2, int_ 2]) -- doc id for each word in the corpus
  , ulet_ "alpha" (appf2_ (var_ "make") (var_ "numtopics") (float_ 0.1)) --topic prior distributions hyperparameter
  , ulet_ "beta" (appf2_ (var_ "make") (var_ "vocabsize") (float_ 0.1)) --word prior distributions hyperparameter
  , ulet_ "phi" (plate_ (ulam_ "x" (assume_ (dirichlet_ (var_ "beta_")))) (appf3_ (var_ "range") (int_ 1) (var_ "numtopics") (int_ 1)))
  , ulet_ "theta" (plate_ (ulam_ "x" (assume_ (dirichlet_ (var_ "alpha_")))) (appf3_ (var_ "range") (int_ 1) (var_ "numdocs") (int_ 1)))
  , ulet_ "z" (plate_ (ulam_ "w" (assume_ (categorical_ (get_ (var_ "theta") (get_ (var_ "docids") (var_ "w")))))) (range (int_ 0) (length_ (var_ "docs"))))
  , ulet_ "" (plate_ (ulam_ "w" (observe_ (get_ (var_ "docs") (var_ "w")) (categorical_ (get_ (var_ "phi") (get_ (var_ "w") (var_ "z")))))) (range (int_ 0) (length_ (var_ "docs"))))
  , seq_ [var_ "phi", var_ "theta", var_ "z"]
  ]
in
/-
utest expr2str (getSome (getReturn _emptyEnv example1expanded))
with strJoin "\n" [
  "assume",
  "  (Beta",
  "     1.0e+1",
  "     1.0e+1)"
] in

utest expr2str (getSome (getReturn _emptyEnv example1plate))
with strJoin "\n" [
  "assume",
  "  (Beta",
  "     1.0e+1",
  "     1.0e+1)"
] in

utest expr2str (getSome (getReturn _emptyEnv example2expanded))
with strJoin "\n" [
 "[ assume",
  "    (Beta",
  "       1.0e+1",
  "       1.0e+1),",
  "  assume",
  "    (Beta",
  "       1.50e+1",
  "       1.0e-0),",
  "  assume",
  "    (Beta",
  "       2.100000e+1",
  "       1.0e+1) ]"
] in

utest expr2str (getSome (getReturn _emptyEnv example2plate))
with strJoin "\n" [
  "assume",
  "  (Beta",
  "     (x.#label\"0\")",
  "     (x.#label\"1\"))"

] in
-/


let transform = lam x. reconstruct (collect {assumeMap=_emptyEnv, observeAssumeMap=_emptyEnv, env=_emptyEnv} x) x
in

-- tests without plate
utest (transform example1expanded) with texample1expanded using eqExpr in
utest (transform simple1example) with tsimple1example using eqExpr in
utest (transform example2expanded) with texample2expanded using eqExpr in
printLn (expr2str (transform simple1example)) ;
--printLn (expr2str (transform example1plate));

--printLn (expr2str (mapBindings (transform  example1plate)));

--printLn (expr2str (mapBindings (transform simple1example).observeAssumeMap));


--printLn (expr2str texample1expanded);
--utest transform example1plate with texample1plate using eqExpr in
--utest transform example1extended with texample1extended using eqExpr in
--utest transform example1extended with texample1extended using eqExpr in

()
