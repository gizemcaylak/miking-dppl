include "string.mc"
include "seq.mc"
include "ext/dist-ext.mc"
mexpr
-- let thetas = [
--[0.95,0.05,]
--[0.05,0.95,]
--[0.5,0.5,]
--]
-- let phis = [
--[0.99,0.01,]
--[0.01,0.99,]
--]
let vocabsize:Int = 2 in
let numdocs:Int = 3 in
let numtopics:Int = 2 in
let alpha:[Float] = [1.,1.] in
let beta:[Float] = [1.,1.] in
let phi = create numtopics (lam. assume (Dirichlet beta)) in
let theta = create numdocs (lam. assume (Dirichlet alpha)) in
let docs:[(Int,Int)] = [(0,10),(1,10),(0,5),(1,5)] in
let docids:[Int] = [0,1,2,2] in
let zCounts = create (length docs) (lam w.
	let word = get docs w in
	let counts = assume (Multinomial word.1 (get theta (get docids w))) in
	iteri (lam z. lam e. weight (mulf (int2float e) (bernoulliLogPmf (get (get phi z) word.0) true))) counts; counts) in 
let str = foldl (lam acc. lam e. join [acc,float2string e," "]) "" (get theta 0) in

                       let str = foldl (lam acc. lam e. join [acc,float2string e," "]) str (get theta 1) in

                       let str = foldl (lam acc. lam e. join [acc,float2string e," "]) str (get theta 2) in

                       let str = foldl (lam acc. lam e. join [acc,float2string e," "]) str (get phi 0) in

                       foldl (lam acc. lam e. join [acc,float2string e," "]) str (get phi 1) 
