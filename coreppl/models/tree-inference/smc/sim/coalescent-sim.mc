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
let cluster = lam q. lam trees. lam maxAge. lam seqLen. lam n.
  if eqi n 1 then trees else
  let pairs = pickpair n in
  let leftChild = get trees pairs.0 in
  let rightChild = get trees pairs.1 in
  let children = [leftChild, rightChild] in
  let t = assume (Exponential 10.0) in
  let age = addf t maxAge in
  let parent = Node {age=age, msg = getMsg leftChild,left = leftChild, right = rightChild, lastWeight=0.0} in
  let min = mini pairs.0 pairs.1 in
  let max = maxi pairs.0 pairs.1 in
  let new_trees = join ([slice trees 0 min, slice trees (addi min 1) max, slice trees (addi max 1) n, [parent]]) in
  cluster q new_trees age seqLen (subi n 1)
end

let model = lam trees. lam seqLength. lam q.
  cluster q trees 0.0 seqLength (length trees)