include "../../data/M336_pruned.mc"
include "../../data/distance_M336.mc"
include "tree-inference-pruned-nj.mc"
include "../../helper/buildTree.mc"
include "../../helper/postProcess.mc"
mexpr
let q = [negf 1., divf 1. 3., divf 1. 3., divf 1. 3.,
 divf 1. 3., negf 1., divf 1. 3., divf 1. 3.,
 divf 1. 3., divf 1. 3.,negf 1., divf 1. 3.,
 divf 1. 3., divf 1. 3., divf 1. 3., negf 1.] in
let q:Mat Float = matFromArrExn 4 4 (extArrOfSeq extArrKindFloat64 q) in
let trees:[Tree] = buildForest data [] 0 (length data) seqLength in
let partitions:[Partition] = create (length trees) (lam i:Int. partSingleton i) in
match triToFlatSymArr distanceMatrix with dFlat in
let modelI = (lam. model trees seqLength q partitions dFlat) in
-- file read here for particle number
match fileReadLine fileStdin with Some info in
match strSplit ":" info with [p, filenameTl,filenameSp] in
let dist = infer (LightweightMCMC {align = true,driftKernel=true,cps="none",continue = (lam. floorfi (string2float p), lam x. lam. lam. (subi x 1, geqi x 0))}) modelI in --infer part
postProcessTree dist filenameTl filenameSp

--print (splitPrint treeSamples weights)
--match collectSplits (get tree 0) with (_, splits) in
--splits

/-
let dist = infer (BPF {particles = floorfi (string2float p)}) modelI in --infer part
let printNormConst = lam dist.
  print (float2string (distEmpiricalNormConst dist)); print "\n" in
 (printNormConst dist)-/

