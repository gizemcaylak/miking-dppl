include "ext/file-ext.mc"
recursive 
let branchLengths = lam tree. lam tl.
	let age = getAge tree in
	match tree with Node n then
		let t = subf age (getAge n.left) in
		let tl = branchLengths n.left (cons t tl) in
		let t = subf age (getAge n.right) in
		branchLengths n.right (cons t tl)
	else tl
end
let branchLengthRes = lam treeSamples. lam weights. foldl2 (lam acc. lam tree. lam w. 
	let branchLens:[Float] = branchLengths (get tree 0) [] in
	let branchLens = join ["[ ", strJoin ", " (map float2string branchLens), " ]"] in
	join [acc, branchLens," ", float2string w, "\n"]
) "" treeSamples weights
recursive
let collectSplits = lam tree.
  match tree with Leaf l then
    ([l.id], [])                  -- (leaf set, splits)
  else match tree with Node n then
    match collectSplits n.left with (leftLeaves, leftSplits) in
    match collectSplits n.right with (rightLeaves, rightSplits) in
    let thisLeaves = join [leftLeaves, rightLeaves] in
    let allSplits  = join [leftSplits, rightSplits, [thisLeaves]] in
    (thisLeaves, allSplits)
  else error "unexpected"
end
let printIntList = lam xs:[Int].
  join ["[", strJoin "," (map int2string xs), "]"]

let splitPrint =  lam treeSamples. lam weights. foldl2 (lam acc. lam tree. lam w. 
	match collectSplits (get tree 0) with (_, splits) in
	let splits:[[Int]] = splits in
	let splits = join ["[", strJoin "," (map (lam split. printIntList split) splits),"]"] in
	join [acc, splits," ", float2string w, "\n"]
) "" treeSamples weights

let postProcessTree = lam dist. lam tlFilename. lam splitFilename.
	match distEmpiricalSamples dist with (treeSamples, weights) in
	(match fileWriteOpen tlFilename with Some wc then
	  let write = fileWriteString wc in
	  write (branchLengthRes treeSamples weights);
	  fileWriteFlush wc; -- Not needed here, just testing the API
	  fileWriteClose wc;
	  ""
	else error "Error writing to file.");
	match fileWriteOpen splitFilename with Some wc then
	  let write = fileWriteString wc in
	  write (splitPrint treeSamples weights);
	  fileWriteFlush wc; -- Not needed here, just testing the API
	  fileWriteClose wc;
	  ""
	else error "Error writing to file."