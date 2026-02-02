include "ext/dist-ext.mc"
include "../../helper/helper.mc"
include "../../helper/pairdist.mc"

let slice = lam seq. lam beg. lam mend.
    subsequence seq beg (subi mend beg)

-- sum_i log(col[i,0])
recursive let sumLog = lam arr:ExtArr Float. lam i:Int. lam m:Int. lam acc:Float.
  if eqi i m then acc
  else sumLog arr (addi i 1) m (addf acc (log (externalExtArrGet arr i)))
end

let totalw = lam nodeMsg:Mat Float. lam n:Int.
  let s = nodeMsg.n in
  let w = if gti n 2 then 1.0 else divf 1.0 (int2float s) in
  let vec = matMake extArrKindFloat64 s 1 w in
  let col = matMulExn nodeMsg vec in
  -- col is m×1 row-major, so element (i,0) is at index i in col.arr
  sumLog col.arr 0 col.m 0.0

let log1mexp = lam x. if ltf x 1e-6 then log x else log (subf 1. (exp (negf x)))
let log1p = lam u. log (addf 1. u)
let logProposeFun = lam beta. lam seqLenF. lam c.
    let x = mulf (divf 4. 3.) (divf c seqLenF) in -- x = 4c/(3L)
    let termDiff = mulf (mulf c beta) (log1mexp x) in
    let termSame = mulf (mulf (subf seqLenF c) beta) (log1p (mulf 3. (exp (negf x)))) in
    (addf termDiff termSame)

recursive
let cluster = lam q. lam trees. lam partitions. lam maxAge. lam seqLen. lam n. lam d. lam n_0.
  if eqi n 1 then trees else
  let seqLenF = int2float seqLen in
  let k = 4.0 in
  let beta = mulf (divf k seqLenF) (divf (int2float n) n_0) in
  -- ((1-exp(-4*v/3))**(c*beta))*((1+3*exp(-4*v/3))**((L-c)*beta))
  let logf2 = logProposeFun beta seqLenF in
  match propose d partitions logf2 n with (idxPair, newPartitions, dNew) in
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
  let theta = maxf rhs 1e-6 in
  -- sample increment and offset by a1
  let t = assume (Gamma kShape theta) in
  (cancel (observe t (Gamma kShape theta)));
  (observe t (Exponential 10.0));
  let age = addf t maxAge in
  let ps = map (lam c. matTranspose (matExpExn (matScale (subf age (getAge c)) q))) children in
  iter (lam c.match c with Node n then weight (negf n.lastWeight) else ())  children;
  let leftPost  = matMulExn (getMsg leftChild)(get ps 0) in -- if q is not symmetric, (matTranspose (get ps 0))
  let rightPost = matMulExn (getMsg rightChild) (get ps 1) in   
  let node_msg = matElemMulExn leftPost rightPost in  
  let lastW = totalw node_msg n in
  weight lastW;
  resample;
  let parent = Node {age=age, msg = node_msg,left = leftChild, right = rightChild, lastWeight=lastW} in
  --let dNew = newDistanceMatrixMessage n d idxPair parent trees seqLength in 
  let min = mini idxPair.0 idxPair.1 in
  let max = maxi idxPair.0 idxPair.1 in
  let new_trees = join ([slice trees 0 min, slice trees (addi min 1) max, slice trees (addi max 1) n, [parent]]) in
  cluster q new_trees newPartitions age seqLen (subi n 1) dNew n_0
end

let model = lam trees. lam seqLength. lam q. lam partitions. lam distanceMatrix.
  cluster q trees partitions 0.0 seqLength (length trees) distanceMatrix (int2float (length trees))
