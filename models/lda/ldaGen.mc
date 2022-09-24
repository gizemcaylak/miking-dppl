include "string.mc"
mexpr
let vocabsize:Int = 2 in
let numdocs:Int = 3 in
let numWordsPerDoc:Int = 10 in
let numtopics:Int = 2 in
let a:Float = 1.0 in
let b:Float = 1.0 in
let phi1 = [0.99,0.01] in
let phi2 =  [0.01,0.99] in
let phi = [phi1,phi2] in
let theta1 = [0.95, 0.05] in
let theta2 = [0.05, 0.95] in
let theta3 = [0.5, 0.5] in
let theta = [theta1, theta2, theta3] in
let docWords = create numdocs (lam docid.
let words = create numWordsPerDoc (lam.
let z = assume (Categorical (get theta docid)) in
let w = assume (Categorical (get phi z)) in
(z,w))
in words) in
let mcprogram = join ["include \"string.mc\"\ninclude \"seq.mc\"
mexpr\n","let vocabsize:Int = " ,int2string vocabsize, " in\n",
                      "let numdocs:Int = " ,int2string numdocs," in\n",
                      "let numtopics:Int = ", int2string numtopics, " in\n",
                      "let alpha:[Float] = [",                      foldl (lam acc. lam e. concat (concat acc (float2string a)) ",") "" (range 1 numtopics 1),float2string a, "] in\n",
                      "let beta:[Float] = [",                      foldl (lam acc. lam . concat (concat acc (float2string b)) ",") "" (range 1 vocabsize 1),                      float2string b, "] in
",
                      "let phi = create numtopics (lam. assume (Dirichlet beta)) in\n",
                      "let theta = create numdocs (lam. assume (Dirichlet alpha)) in\n",
                      "let docs:[Int] = [",
                      foldl (lam acc. lam doc. (foldl (lam s. lam w. join [s, int2string w.1, ","] ) acc doc )) "" (init docWords),
                      foldl (lam s. lam w. join [s, int2string w.1, ","]) "" (init (last docWords)),
                      join [int2string ((last (last docWords)).1), "] in\n"],
                      "let docids:[Int] = [",
                       foldl (lam acc. lam doc. (foldl (lam s. lam. join [s, int2string doc, ","] ) acc (range 0 numWordsPerDoc 1) )) "" (range 0 (subi numdocs 1) 1),
                       (foldl (lam s. lam . join [s, int2string (subi numdocs 1), ","] ) "" (range 1 numWordsPerDoc 1) ),
                       join [int2string (subi numdocs 1), "] in \n"],
                       "let topicassignments:[Int] = [",
                      foldl (lam acc. lam doc. (foldl (lam s. lam w. join [s, int2string w.0, ","] ) acc doc )) "" (init docWords),
                      foldl (lam s. lam w. join [s, int2string w.0, ","]) "" (init (last docWords)),
                      join [int2string ((last (last docWords)).0), "] in\n"],
                       "let z = create (length docs) (lam w.\n",
                       "let z = assume (Categorical (get theta (get docids w))) in\n",
                       "observe (get docs w) (Categorical (get phi z));\n z)",
                       "in \n",
"let str = foldl (lam acc. lam e. join [acc,float2string e,\" \"]) \"\" (get theta 0) in\n
let str = foldl (lam acc. lam e. join [acc,float2string e,\" \"]) str (get theta 1) in\n
let str = foldl (lam acc. lam e. join [acc,float2string e,\" \"]) str (get theta 2) in\n
let str = foldl (lam acc. lam e. join [acc,float2string e,\" \"]) str (get phi 0) in\n
foldl (lam acc. lam e. join [acc,float2string e,\" \"]) str (get phi 1) \n"] in mcprogram
