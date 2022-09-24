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
let docs:[Int] = [0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,0,0,0,0,0,0,1,0,1,0,1] in
let docids:[Int] = [0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2] in 
let topicassignments:[Int] = [0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,0,0,0,0,0,0,1,0,1,0,1] in
let z = map (lam w.
let z = assume (Categorical (get theta (get docids w))) in
observe (get docs w) (Categorical (get phi z));
 z) (range 0 (length docs) 1)in 
let str = foldl (lam acc. lam e. join [acc,float2string e," "]) "" (get theta 0) in

let str = foldl (lam acc. lam e. join [acc,float2string e," "]) str (get theta 1) in

let str = foldl (lam acc. lam e. join [acc,float2string e," "]) str (get theta 2) in

let str = foldl (lam acc. lam e. join [acc,float2string e," "]) str (get phi 0) in

foldl (lam acc. lam e. join [acc,float2string e," "]) str (get phi 1) 
