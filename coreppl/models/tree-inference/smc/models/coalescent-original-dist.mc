include "ext/dist-ext.mc"
include "../../helper/helper.mc"
include "../../helper/pairdist.mc"

let slice = lam seq. lam beg. lam mend.
    subsequence seq beg (subi mend beg)
    
let applyPRows = lam p:Mat Float. lam m:Mat Float.
  matMulExn m (matTranspose p)

-- sum_i log(col[i,0])
-- sum_i log(col[i,0])
recursive let sumLog = lam arr:ExtArr Float. lam i:Int. lam m:Int. lam acc:Float.
  if eqi i m then acc
  else sumLog arr (addi i 1) m (addf acc (log (externalExtArrGet arr i)))
end

let total_loglikes = lam nodeMsg:Mat Float.
  let s = nodeMsg.n in
  let vec = matMake extArrKindFloat64 s 1 0.25 in
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
let pickpair = lam n.
  let i = assume (UniformDiscrete 0 (subi n 1)) in
  let j = assume (UniformDiscrete 0 (subi n 2)) in
  if lti j i then (i,j) else (i,addi j 1)

recursive
let cluster = lam q. lam trees. lam partitions. lam maxAge. lam seqLen. lam n. lam d. lam n_0.
  if eqi n 1 then trees else
  let seqLenF = int2float seqLen in
  let k = 4.0 in
  let dVals = flattenSymmetricFlatArr n d (lam x. x) in
  let dMean = divf (foldl (lam a. lam v. addf a v.1) 0.0 dVals) (int2float (length dVals)) in
  let dVar = divf (foldl (lam a. lam v. addf a (mulf (subf v.1 dMean)(subf v.1 dMean))) 0.0 dVals) (int2float (length dVals)) in
  let beta = if gtf dVar 1e-10 then divf 1.0 (sqrt dVar) else divf k seqLenF in
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
  let thetaClamped = maxf rhs 1e-3 in
  let t = assume (Gamma kShape thetaClamped) in
  (cancel (observe t (Gamma kShape thetaClamped)));
  (observe t (Exponential 10.0));
  let age = addf t maxAge in
  let ps = map (lam c. matTranspose (matExpExn (matScale (subf age (getAge c)) q))) children in
  let leftPost  = applyPRows (get ps 0) (getMsg leftChild)  in 
  let rightPost = applyPRows (get ps 1) (getMsg rightChild) in   
  let node_msg = matElemMulExn leftPost rightPost in  
  let lw_left  = total_loglikes (getMsg leftChild) in
  let lw_right = total_loglikes (getMsg rightChild) in
  let lw_node  = total_loglikes node_msg in
  weight (negf lw_left);
  weight (negf lw_right);
  weight lw_node;
  resample;
  /- (match leftChild with Leaf _ then print "leaf" else print "node" );
  print "lc weight:";
  printLn (float2string (lw_left));
   (match rightChild with Leaf _ then print "leaf" else print "node" );
  print "rc weight:";
  printLn (float2string (lw_right));
  print "last weight:";
  printLn (float2string lw_node);-/
  let parent = Node {age=age, msg = node_msg,left = leftChild, right = rightChild, lastWeight=0.} in
  let min = mini idxPair.0 idxPair.1 in
  let max = maxi idxPair.0 idxPair.1 in
  let new_trees = join ([slice trees 0 min, slice trees (addi min 1) max, slice trees (addi max 1) n, [parent]]) in
  cluster q new_trees newPartitions age seqLen (subi n 1) dNew n_0
end
let model = lam trees. lam seqLength. lam q. lam partitions. lam distanceMatrix. lam initWeight.
  weight initWeight;
  cluster q trees partitions 0.0 seqLength (length trees) distanceMatrix (length trees)

