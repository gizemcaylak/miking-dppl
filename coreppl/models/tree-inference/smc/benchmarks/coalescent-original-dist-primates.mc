include "../../data/primates_pruned.mc"
include "../../data/distance_primates.mc"
include "../models/coalescent-original-dist.mc"
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
let initWeight = foldl (lam acc. lam l. foldl (lam acc. lam s. if eqi s 4 then acc else addf acc (log 0.25)) acc l) 0. data in
let modelI = (lam. model trees seqLength q partitions dFlat initWeight) in
match fileReadLine fileStdin with Some info in
match strSplit ":" info with [p, filenameTl, filenameSp] in
let dist = infer (BPF {particles = floorfi (string2float p), cps="partial"}) modelI in
postProcessTree dist filenameTl filenameSp true
