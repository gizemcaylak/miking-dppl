-- Weight-free simulation of star decomposition (prior sampling only).
-- Message/likelihood/weight computations are removed for speed; this samples
-- topology (uniform pair merges) and branch lengths (Exp(10) age increments)
-- from the prior, matching stardecomp's generative structure.
include "matrix.mc"
include "ext/mat-ext.mc"
include "ext/dist-ext.mc"
include "../../helper/helper.mc"
include "../../helper/buildTree.mc"

let slice = lam seq. lam beg. lam mend.
    subsequence seq beg (subi mend beg)

let pickpair = lam n.
  let i = assume (UniformDiscrete 0 (subi n 1)) in
  let j = assume (UniformDiscrete 0 (subi n 2)) in
  if lti j i then (i,j) else (i,addi j 1)

recursive
let starCluster = lam q. lam components. lam maxAge. lam seqLen. lam n.
  if eqi n 1 then components else
  let pairs = pickpair n in
  let leftChild  = get components pairs.0 in
  let rightChild = get components pairs.1 in
  let t   = assume (Exponential 10.0) in
  let age = addf maxAge t in
  -- no message propagation / weighting: msg is a placeholder for tree extraction
  let newNode = Node {age=age, msg = getMsg leftChild, left = leftChild, right = rightChild, lastWeight=0.0} in
  let minIdx = mini pairs.0 pairs.1 in
  let maxIdx = maxi pairs.0 pairs.1 in
  let newComponents = join ([slice components 0 minIdx, slice components (addi minIdx 1) maxIdx, slice components (addi maxIdx 1) n, [newNode]]) in
  starCluster q newComponents age seqLen (subi n 1)
end

let model = lam trees. lam seqLength. lam q.
  starCluster q trees 0.0 seqLength (length trees)
