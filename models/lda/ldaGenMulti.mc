include "string.mc"
include "map.mc"
mexpr
let vocabsize:Int = 100 in
let numdocs:Int = 25 in
let numWordsPerDoc:Int = 20 in
let numtopics:Int = 10 in

let a:Float = 0.1 in
let b:Float = 0.2 in
let alpha:[Float] = make numtopics a in
let beta:[Float] = make vocabsize b in
let phi = create numtopics (lam. assume (Dirichlet beta)) in
let theta = create numdocs (lam. assume (Dirichlet alpha)) in

/-
let phi1 = [0.99,0.01] in
let phi2 =  [0.01,0.99] in
let theta1 = [0.95, 0.05] in
let theta2 = [0.05, 0.95] in
let theta3 = [0.5, 0.5] in
let phi = [phi1,phi2] in
let theta = [theta1, theta2, theta3] in
-/
let a:Float = 1. in
let b:Float = 1. in
let docWords = create numdocs (lam docid.
  foldl (lam m. lam .
    let z = assume (Categorical (get theta docid)) in
    let w = assume (Categorical (get phi z)) in
    match mapLookup w m with Some val then
      mapInsert w (addi 1 val.0, val.1) m
    else
      mapInsert w (1, docid) m
  ) (mapEmpty subi) (create numWordsPerDoc (lam x. x))) in
let bagOfWords = map mapBindings docWords in
let mcprogram = join ["include \"string.mc\"\ninclude \"seq.mc\"\ninclude \"ext/dist-ext.mc\"\nmexpr\n",
                      "-- let thetas = [",
                      foldl (lam acc. lam t. join [acc,"--[",
                        (foldl (lam s. lam e. join [s,
                                                  float2string e,","]) "" t),
                                                  "]\n"]) "\n" theta,
                      "--]\n",
                      "-- let phis = [",
                      foldl (lam acc. lam t. join [acc,"--[",
                        (foldl (lam s. lam e. join [s,
                                                  float2string e,","]) "" t),
                                                  "]\n"]) "\n" phi,
                      "--]\n",
                      "let vocabsize:Int = " ,int2string vocabsize, " in\n",
                      "let numdocs:Int = " ,int2string numdocs," in\n",
                      "let numtopics:Int = ", int2string numtopics, " in\n",
                      "let alpha:[Float] = [",
                      foldl (lam acc. lam e. concat (concat acc (float2string a)) ",") "" (range 1 numtopics 1),float2string a, "] in\n",
                      "let beta:[Float] = [",
                      foldl (lam acc. lam . concat (concat acc (float2string b)) ",") "" (range 1 vocabsize 1),                      float2string b, "] in
",
                      "let phi = create numtopics (lam. assume (Dirichlet beta)) in\n",
                      "let theta = create numdocs (lam. assume (Dirichlet alpha)) in\n",
                      "let docs:[(Int,Int)] = [",
                      foldl (lam acc. lam doc. (foldl (lam s. lam binding. join [s, "(", int2string (binding.0), ",", int2string (binding.1).0, "),"] ) acc doc )) "" (init bagOfWords),
                      foldl (lam s. lam binding. join [s,"(", int2string (binding.0), ",", int2string (binding.1).0, "),"] ) "" (init (last bagOfWords)),
                      let w = last (last bagOfWords) in join ["(",int2string w.0,",", int2string (w.1).0, ")] in\n"],
                      "let docids:[Int] = [",
                      foldl (lam acc. lam doc. (foldl (lam s. lam binding. join [s, int2string (binding.1).1, ","] ) acc doc )) "" (init bagOfWords),
                      foldl (lam s. lam binding. join [s,int2string (binding.1).1, ","] ) "" (init (last bagOfWords)),
                      let w = last (last bagOfWords) in join [int2string (w.1).1, "] in\n"],
                       "let zCounts = create (length docs) (lam w.\n",
                       "\tlet word = get docs w in\n",
                       "\tlet counts = assume (Multinomial word.1 (get theta (get docids w))) in\n",
                       "\titeri (lam z. lam e. weight (mulf (int2float e) (bernoulliLogPmf (get (get phi z) word.0) true))) counts;",
                       " counts) in \n",
                       "let str = foldl (lam acc. lam e. join [acc,float2string e,\" \"]) \"\" (get theta 0) in\n
                       let str = foldl (lam acc. lam e. join [acc,float2string e,\" \"]) str (get theta 1) in\n
                       let str = foldl (lam acc. lam e. join [acc,float2string e,\" \"]) str (get theta 2) in\n
                       let str = foldl (lam acc. lam e. join [acc,float2string e,\" \"]) str (get phi 0) in\n
                       foldl (lam acc. lam e. join [acc,float2string e,\" \"]) str (get phi 1) \n"] in mcprogram
