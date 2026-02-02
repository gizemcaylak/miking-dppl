include "../../data/M336_pruned.mc"
include "tree-inference-pruned.mc"
include "../../helper/buildTree.mc"
include "../../helper/postProcess.mc"
mexpr
let q = [negf 1., divf 1. 3., divf 1. 3., divf 1. 3.,
 divf 1. 3., negf 1., divf 1. 3., divf 1. 3.,
 divf 1. 3., divf 1. 3.,negf 1., divf 1. 3.,
 divf 1. 3., divf 1. 3., divf 1. 3., negf 1.] in
let q:Mat Float = matFromArrExn 4 4 (extArrOfSeq extArrKindFloat64 q) in
let trees:[Tree] = buildForest data [] 0 (length data) seqLength in
let modelI = (lam. model trees seqLength q) in
match fileReadLine fileStdin with Some info in
match strSplit ":" info with [p, filenameTl,filenameSp] in
let isMCMC = false in
match  
	if isMCMC then
		(false, infer (LightweightMCMC {align = true,driftKernel=true,cps="partial",continue = (lam. floorfi (string2float p), lam x. lam. lam. (subi x 1, geqi x 0))}) modelI) --infer part
	else (true, infer (BPF {particles = floorfi (string2float p),cps="partial",resampleFrac=0.}) modelI) --infer part
with (consNormConst, dist) in
/-let printNormConst = lam dist.
  print (float2string (distEmpiricalNormConst dist)); print "\n" in
 (printNormConst dist)-/
 postProcessTree dist filenameTl filenameSp consNormConst