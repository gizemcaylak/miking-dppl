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

let totalw = lam nodeMsg:Mat Float. lam n:Int.
  let s = nodeMsg.n in
  let w = if gti n 2 then 1.0 else divf 1.0 (int2float s) in
  let vec = matMake extArrKindFloat64 s 1 w in
  let col = matMulExn nodeMsg vec in
  -- col is m×1 row-major, so element (i,0) sits at index i in col.arr
  sumLog col.arr 0 col.m 0.0

/-let jcProbs = lam i. lam j. lam t.
  if eqi i j then addf 0.25 (mulf 0.75 (exp (negf (mulf (divf 4. 3.) t))))
  else subf 0.25 (mulf 0.25 (exp (negf (mulf (divf 4. 3.) t))))
let jcMat = lam t:Float.
  let p = matMakeUninit extArrKindFloat64 4 4 in
  recursive let fill = lam i:Int. lam j:Int.
    if eqi i 4 then ()
    else 
      if eqi j 4 then fill (addi i 1) 0
      else 
        matSetExn p i j (jcProbs i j t);
        fill i (addi j 1)
  in fill 0 0; p-/

recursive
let cluster = lam q. lam trees. lam maxAge. lam seqLen. lam n.
  if eqi n 1 then trees else
  let pairs = pickpair n in
  let leftChild = get trees pairs.0 in
  let rightChild = get trees pairs.1 in
  let children = [leftChild, rightChild] in

  let t = assume (Exponential 10.0) in
  let age = addf t maxAge in
  let ps = map (lam c. matTranspose (matExpExn (matScale (subf age (getAge c)) q))) children in
  iter (lam c. match c with Node n then weight (negf n.lastWeight) else ()) children;
  let leftPost  = matMulExn (getMsg leftChild)(get ps 0) in -- if q is not symmetric, (matTranspose (get ps 0))
  let rightPost = matMulExn (getMsg rightChild) (get ps 1) in   
  let node_msg = matElemMulExn leftPost rightPost in  
  let lastW = totalw node_msg n in
  weight lastW;
  resample;
  let parent = Node {age=age, msg = node_msg,left = leftChild, right = rightChild, lastWeight=lastW} in
  let min = mini pairs.0 pairs.1 in
  let max = maxi pairs.0 pairs.1 in
  let new_trees = join ([slice trees 0 min, slice trees (addi min 1) max, slice trees (addi max 1) n, [parent]]) in
  cluster q new_trees age seqLen (subi n 1)
end

let model = lam trees. lam seqLength. lam q.
  cluster q trees 0.0 seqLength (length trees)
