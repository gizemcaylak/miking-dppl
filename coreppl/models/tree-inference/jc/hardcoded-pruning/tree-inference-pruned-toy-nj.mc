include "../../data/toydata_pruned.mc"
include "../../data/distance_toy.mc"
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
let initWeight = 
  foldl (lam acc. lam l. foldl (lam acc. lam s. if eqi s 4 then acc else addf acc ((log 0.25)) ) acc l) 0.0 data in
let modelI = (lam. model trees seqLength q partitions dFlat initWeight) in
-- file read here for particle number
match fileReadLine fileStdin with Some info in
match strSplit ":" info with [p, filenameTl,filenameSp] in
let isMCMC = false in

let printNormConst = lam dist.
  print (float2string (distEmpiricalNormConst dist)); print "\n" in
match  
	if isMCMC then
		(false, infer (LightweightMCMC {align = true,driftKernel=true,cps="partial",continue = (lam. floorfi (string2float p), lam x. lam. lam. (subi x 1, geqi x 0))}) modelI) --infer part
	else (true, let dist = infer (BPF {particles = floorfi (string2float p),cps="partial"}) modelI in  (printNormConst dist);dist) --infer part
with (consNormConst, dist) in
()
 --postProcessTree dist filenameTl filenameSp consNormConst

