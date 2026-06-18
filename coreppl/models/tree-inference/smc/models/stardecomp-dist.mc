-- Distance-applied star decomposition (no lookahead).
-- Star-decomposition SMC (bush-likelihood weighting) where the pair to merge is
-- proposed from the NJ distance matrix (helper/pairdist.mc) and the branch length
-- is proposed from a Gamma tuned by the distance, with an importance correction
-- back to the Exponential(10) prior. Mirrors coalescent-nj's proposal while keeping
-- star decomposition's bush-likelihood weighting.
include "matrix.mc"
include "ext/mat-ext.mc"
include "ext/dist-ext.mc"
include "../../helper/helper.mc"
include "../../helper/pairdist.mc"

let slice = lam seq. lam beg. lam mend.
    subsequence seq beg (subi mend beg)

let applyPRows = lam p:Mat Float. lam m:Mat Float.
  matMulExn m (matTranspose p)

recursive let sumLog = lam arr:ExtArr Float. lam i:Int. lam m:Int. lam acc:Float.
  if eqi i m then acc
  else sumLog arr (addi i 1) m (addf acc (log (externalExtArrGet arr i)))
end

let total_loglikes = lam nodeMsg:Mat Float.
  let s = nodeMsg.n in
  let vec = matMake extArrKindFloat64 s 1 0.25 in
  let col = matMulExn nodeMsg vec in
  sumLog col.arr 0 col.m 0.0

let propagate = lam q. lam t. lam msg.
  let p = matTranspose (matExpExn (matScale t q)) in
  applyPRows p msg

let bushMsg = lam q. lam epsilon. lam node.
  propagate q epsilon (getMsg node)

let bushLogLike = lam propagatedMsgs. lam numStates.
  let combined = foldl matElemMulExn (head propagatedMsgs) (tail propagatedMsgs) in
  total_loglikes combined

-- Distance-based proposal helpers (identical to coalescent-nj)
let log1mexp = lam x. if ltf x 1e-6 then log x else log (subf 1. (exp (negf x)))
let log1p = lam u. log (addf 1. u)
let logProposeFun = lam beta. lam seqLenF. lam c.
    let x = mulf (divf 4. 3.) (divf c seqLenF) in -- x = 4c/(3L)
    let termDiff = mulf (mulf c beta) (log1mexp x) in
    let termSame = mulf (mulf (subf seqLenF c) beta) (log1p (mulf 3. (exp (negf x)))) in
    (addf termDiff termSame)

recursive
let starCluster =
  lam q. lam epsilon. lam components. lam oldBushLogLike. lam n. lam maxAge.
  lam seqLen. lam partitions. lam d. lam n_0.
  if eqi n 1 then
    let finalNode   = head components in
    let trueLogLike = total_loglikes (getMsg finalNode) in
    weight (subf trueLogLike oldBushLogLike);  -- always 0 by identity; kept for clarity
    components
  else
    let seqLenF = int2float seqLen in
    let k = 4.0 in
    let dVals = flattenSymmetricFlatArr n d (lam x. x) in
    let dMean = divf (foldl (lam a. lam v. addf a v.1) 0.0 dVals) (int2float (length dVals)) in
    let dVar = divf (foldl (lam a. lam v. addf a (mulf (subf v.1 dMean)(subf v.1 dMean))) 0.0 dVals) (int2float (length dVals)) in
    let beta = if gtf dVar 1e-10 then divf 1.0 (sqrt dVar) else divf k seqLenF in
    let logf2 = logProposeFun beta seqLenF in
    match propose d partitions logf2 n with (idxPair, newPartitions, dNew) in

    let leftChild  = get components idxPair.0 in
    let rightChild = get components idxPair.1 in

    -- Branch-length proposal from a distance-tuned Gamma, corrected back to Exp(10).
    let aL = getAge leftChild in
    let aR = getAge rightChild in
    let a1 = if gtf aL aR then aL else aR in
    let a2 = if gtf aL aR then aR else aL in
    let c = dGet d n idxPair.0 idxPair.1 in
    let kShape = 0.1 in
    let deltaA = subf a1 a2 in
    let rhs = divf (subf (divf c seqLenF) deltaA) 2.0 in
    let theta = maxf rhs 1e-3 in
    let t = assume (Gamma kShape theta) in
    (cancel (observe t (Gamma kShape theta)));
    (observe t (Exponential 10.0));
    let age = addf maxAge t in

    let pLeft  = matTranspose (matExpExn (matScale (subf age (getAge leftChild))  q)) in
    let pRight = matTranspose (matExpExn (matScale (subf age (getAge rightChild)) q)) in

    let leftPost  = applyPRows pLeft  (getMsg leftChild)  in
    let rightPost = applyPRows pRight (getMsg rightChild) in

    let subtreeMsg = matElemMulExn leftPost rightPost in

    let newNode = Node {
      age = age,
      msg = subtreeMsg,
      left = leftChild,
      right = rightChild,
      lastWeight = 0.0
    } in
    let minIdx = mini idxPair.0 idxPair.1 in
    let maxIdx = maxi idxPair.0 idxPair.1 in
    let newComponents = join ([
      slice components 0 minIdx,
      slice components (addi minIdx 1) maxIdx,
      slice components (addi maxIdx 1) n,
      [newNode]
    ]) in
    let newN = subi n 1 in

    let newEpsilon = maxf epsilon age in

    let newPropagated  = map (bushMsg q newEpsilon) newComponents in
    let newBushLogLike = bushLogLike newPropagated (getMsg (head newComponents)).n in

    weight (subf newBushLogLike oldBushLogLike);
    resample;

    starCluster q newEpsilon newComponents newBushLogLike newN age seqLen newPartitions dNew n_0
end

let model = lam leaves. lam seqLength. lam q. lam initEpsilon. lam partitions. lam distanceMatrix.
  let n = length leaves in
  let initEpsilon = 1.0 in
  let propagatedMsgs = map (bushMsg q initEpsilon) leaves in
  let initBushLogLike = bushLogLike propagatedMsgs (getMsg (head leaves)).n in
  weight initBushLogLike;
  starCluster q initEpsilon leaves initBushLogLike n 0. seqLength partitions distanceMatrix n
