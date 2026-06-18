include "ext/dist-ext.mc"
include "../../helper/helper.mc"
include "../../helper/pairdist.mc"

let slice = lam seq. lam beg. lam mend.
    subsequence seq beg (subi mend beg)

let log1mexp = lam x. if ltf x 1e-6 then log x else log (subf 1. (exp (negf x)))
let log1p = lam u. log (addf 1. u)
let logProposeFun = lam beta. lam seqLenF. lam c.
    let x = mulf (divf 4. 3.) (divf c seqLenF) in -- x = 4c/(3L)
    let termDiff = mulf (mulf c beta) (log1mexp x) in
    let termSame = mulf (mulf (subf seqLenF c) beta) (log1p (mulf 3. (exp (negf x)))) in
    (addf termDiff termSame)

recursive
let cluster = lam q. lam trees. lam partitions. lam maxAge. lam seqLen. lam n. lam d. lam n_0. --lam mergeOrder.
  if eqi n 1 then trees else
  let seqLenF = int2float seqLen in
  let k = 4.0 in
  --let beta = divf k seqLenF in--mulf (divf k seqLenF) (divf (int2float n) (int2float n_0)) in
  let dVals = flattenSymmetricFlatArr n d (lam x. x) in
  let dMean = divf (foldl (lam a. lam v. addf a v.1) 0.0 dVals) (int2float (length dVals)) in
  let dVar = divf (foldl (lam a. lam v. addf a (mulf (subf v.1 dMean)(subf v.1 dMean))) 0.0 dVals) (int2float (length dVals)) in
  let beta = if gtf dVar 1e-10 then divf 1.0 (sqrt dVar) else divf k seqLenF in
  -- ((1-exp(-4*v/3))**(c*beta))*((1+3*exp(-4*v/3))**((L-c)*beta))
  let logf2 = logProposeFun beta seqLenF in
  match propose d partitions logf2 n with (idxPair, newPartitions, dNew) in
  --let idxPair = get mergeOrder (subi n_0 n) in 
  --printLn (strJoin " " [(int2string idxPair.0),(int2string idxPair.1)]);
  let leftChild = get trees idxPair.0 in
  let rightChild = get trees idxPair.1 in
  let children = [leftChild, rightChild] in
  let aL = getAge leftChild in
  let aR = getAge rightChild in
  let a1 = if gtf aL aR then aL else aR in
  let a2 = if gtf aL aR then aR else aL in
  let c = dGet d n idxPair.0 idxPair.1 in
  -- tuning param
  let kShape = 0.1 in 
  -- theta = max(eps, ((c/L) - (a1-a2))/2)
  let deltaA = subf a1 a2 in
  let rhs = divf (subf (divf c seqLenF) deltaA) 2.0 in
  let theta = maxf rhs 1e-3 in
  let t = assume (Gamma kShape theta) in
  (cancel (observe t (Gamma kShape theta)));
  (observe t (Exponential 10.0));
  let age = addf t maxAge in
  
  let parent = Node {age=age, msg = getMsg leftChild,left = leftChild, right = rightChild, lastWeight=0.} in
  --let dNew = newDistanceMatrixMessage n d idxPair parent trees seqLength in 
  let min = mini idxPair.0 idxPair.1 in
  let max = maxi idxPair.0 idxPair.1 in
  let new_trees = join ([slice trees 0 min, slice trees (addi min 1) max, slice trees (addi max 1) n, [parent]]) in
  cluster q new_trees newPartitions age seqLen (subi n 1) dNew n_0-- mergeOrder
end
--(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11)
--(0,1,2,3,4,5,6,9,10,11,7-8)
--(0,1,2,3,4,5,6,10,11,7-8-9)
--(0,1,2,3,4,5,6,11,7-8-9-10)
--(0,1,4,5,6,11,7-8-9-10,2-3)
--(0,1,5,6,11,7-8-9-10,2-3-4)
--(0,1,6,11,7-8-9-10,2-3-4-5)
--(0,1,11,7-8-9-10,2-3-4-5-6)
--(0,1,11-7-8-9-10-2-3-4-5-6)
--(0-1,11-7-8-9-10-2-3-4-5-6)
/-
(7, 8), (7, 8, 9), (7, 8, 9, 10), (2, 3), (2, 3, 4), (2, 3, 4, 5), (2, 3, 4, 5, 6),
 (2, 3, 4, 5, 6, 7, 8, 9, 10), (2, 3, 4, 5, 6, 7, 8, 9, 10, 11), (0, 1), (0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11)]-/
let model = lam trees. lam seqLength. lam q. lam partitions. lam distanceMatrix.
  --let mergeOrder = [(7,8),(10,7),(9,7),(2,3),(2,7),(2,6),(2,5),(3,4),(2,3),(0,1),(0,1)] in
  --let mergeOrder = [(7,8),(10,7),(9,7),(2,3),(2,7),(2,6),(2,5),(3,4),(2,3),(1,2),(0,1)] in
  cluster q trees partitions 0.0 seqLength (length trees) distanceMatrix  (length trees)--mergeOrder
