include "matrix.mc"
include "ext/mat-ext.mc"
include "ext/dist-ext.mc"
include "../../helper/helper.mc"
include "../../helper/buildTree.mc"

let slice = lam seq. lam beg. lam mend.
    subsequence seq beg (subi mend beg)

let matrixGet = lam row. lam col. lam mtx.
  matGetExn mtx row col

let pickpair = lam n.
  let i = assume (UniformDiscrete 0 (subi n 1)) in
  let j = assume (UniformDiscrete 0 (subi n 2)) in
  if lti j i then (i,j) else (i,addi j 1)

let iid = lam f. lam p. lam n.
  let params = make n p in
  map f params

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
recursive
let starCluster = lam q. lam epsilon. lam components. lam oldBushLogLike. lam n. lam maxAge. 
  if eqi n 1 then
    let finalNode   = head components in
    let trueLogLike = total_loglikes (getMsg finalNode) in
    weight (subf trueLogLike oldBushLogLike);  -- always 0 by identity; kept for clarity
   -- printLn (float2string (subf trueLogLike oldBushLogLike));
    components
  else
    let pairs = pickpair n in
    let leftChild  = get components pairs.0 in
    let rightChild = get components pairs.1 in

    -- Single sample: time above the taller child to the new internal node.
    -- age = max(ageLeft, ageRight) + t
    -- branch lengths: age - ageLeft, age - ageRight  (both measured from child)
    let t   = assume (Exponential 10.) in
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
    let minIdx = mini pairs.0 pairs.1 in
    let maxIdx = maxi pairs.0 pairs.1 in
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
    --printLn (float2string (subf newBushLogLike oldBushLogLike));
    resample;

    starCluster q newEpsilon newComponents newBushLogLike newN age
end

let model = lam leaves. lam seqLength. lam q. lam initEpsilon.
  let n = length leaves in
  let initEpsilon = 1.0 in
  let propagatedMsgs = map (bushMsg q initEpsilon) leaves in
  let initBushLogLike = bushLogLike propagatedMsgs (getMsg (head leaves)).n in
  weight initBushLogLike;
  starCluster q initEpsilon leaves initBushLogLike n 0.
