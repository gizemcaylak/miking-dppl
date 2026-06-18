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

-- sum_i log(col[i,0])
recursive let sumLog = lam arr:ExtArr Float. lam i:Int. lam m:Int. lam acc:Float.
  if eqi i m then acc
  else sumLog arr (addi i 1) m (addf acc (log (externalExtArrGet arr i)))
end
-- Compute log P(Y(X_i) | t_i) by marginalizing over root states
-- with a flat stationary distribution (0.25 per state for 4 nucleotides).
-- This corresponds to the likelihood L_{Y(X_i)}(t_i) in Equation (6)
-- of the paper's natural forest extension.
let total_loglikes = lam nodeMsg:Mat Float.
  let s = nodeMsg.n in
  let vec = matMake extArrKindFloat64 s 1 0.25 in
  let col = matMulExn nodeMsg vec in
  -- col is m×1 row-major, so element (i,0) is at index i in col.arr
  sumLog col.arr 0 col.m 0.0

recursive
let cluster = lam q. lam trees. lam maxAge. lam seqLen. lam n.
  if eqi n 1 then trees else
  let pairs = pickpair n in
  let leftChild = get trees pairs.0 in
  let rightChild = get trees pairs.1 in
  let children = [leftChild, rightChild] in
  let t = assume (Exponential 10.) in
  let age = addf t maxAge in
  let ps = map (lam c. matTranspose (matExpExn (matScale (subf age (getAge c)) q))) children in
  let leftPost  = applyPRows (get ps 0) (getMsg leftChild)  in 
  let rightPost = applyPRows (get ps 1) (getMsg rightChild) in   
  let node_msg = matElemMulExn leftPost rightPost in 
  -- as we progress, age gap increases
  let lw_left  = total_loglikes (getMsg leftChild) in
  let lw_right = total_loglikes (getMsg rightChild) in
  let lw_node  = total_loglikes node_msg in 
  weight (negf lw_left);
  weight (negf lw_right);
  weight lw_node;
  resample;
  let parent = Node {age=age, msg = node_msg,left = leftChild, right = rightChild, lastWeight=0.0} in
  let min = mini pairs.0 pairs.1 in
  let max = maxi pairs.0 pairs.1 in
  let new_trees = join ([slice trees 0 min, slice trees (addi min 1) max, slice trees (addi max 1) n, [parent]]) in
  cluster q new_trees age seqLen (subi n 1)
end

let model = lam trees. lam seqLength. lam q. lam initWeight.
  weight initWeight;
  cluster q trees 0.0 seqLength (length trees)
