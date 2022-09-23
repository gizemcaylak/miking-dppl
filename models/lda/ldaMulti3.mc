include "string.mc"
include "seq.mc"
mexpr
let vocabsize:Int = 2 in
let numdocs:Int = 3 in
let numtopics:Int = 2 in
let alpha:[Float] = [1.,1.] in
let beta:[Float] = [1.,1.] in
let phi = map (lam. assume (Dirichlet beta)) (range 0 numtopics 1) in
let theta = map (lam. assume (Dirichlet alpha)) (range 0 numdocs 1) in
let oneHotEncoding = lam size. lam ind. lam count.
mapi (lam i. lam e. if eqi i ind then count else 0) (range 0 size 1) in
let docs:[(Int,Int)] = [(0,10),(1,10),(0,6),(1,4)] in
let docids:[Int] = [0,1,2,2] in
let z = map (lam w.
	let word = get docs w in
	let z = assume (Multinomial word.1 (get theta (get docids w))) in
	iteri (lam z. lam e. observe (oneHotEncoding vocabsize word.0 e) (Multinomial e (get phi z))) z;
 z)(range 0 (length docs) 1) in 
let str = foldl (lam acc. lam e. join [acc,float2string e," "]) "" (get theta 0) in

                       let str = foldl (lam acc. lam e. join [acc,float2string e," "]) str (get theta 1) in

                       let str = foldl (lam acc. lam e. join [acc,float2string e," "]) str (get theta 2) in

                       let str = foldl (lam acc. lam e. join [acc,float2string e," "]) str (get phi 0) in

                       foldl (lam acc. lam e. join [acc,float2string e," "]) str (get phi 1) 
