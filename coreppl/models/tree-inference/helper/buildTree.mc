include "ext/mat-ext.mc"
type Tree
con Leaf : {age: Float, msg: Mat Float, id: Int} -> Tree
con Node : {age: Float, msg: Mat Float, left: Tree, right: Tree, lastWeight:Float} -> Tree
let getAge = lam n. match n with Node r then r.age else match n with Leaf r then r.age else never
let getMsg = lam n. match n with Leaf r then r.msg else match n with Node r then r.msg else never

let getLeafMessage = lam seq:Int.
  if eqi seq 0 then (1.0, 0.0, 0.0, 0.0)
  else if eqi seq 1 then (0.0, 1.0, 0.0, 0.0)
  else if eqi seq 2 then (0.0, 0.0, 1.0, 0.0)
  else if eqi seq 3 then (0.0, 0.0, 0.0, 1.0)
  else if eqi seq 4 then (1.0, 1.0, 1.0, 1.0)
  else error "Invalid state at leaf"

-- implement of Array
let leafMsgMat = lam seqLen:Int. lam xs:[Int].
  let a = arrMakeUninitFloat (muli seqLen 4) in
  recursive let fill = lam i:Int. lam ys:[Int].
    switch ys
    case [] then ()
    case [y] ++ ys then
      let v = getLeafMessage y in
      let base = muli i 4 in
      arrSetExn a (base)        v.0;
      arrSetExn a (addi base 1) v.1;
      arrSetExn a (addi base 2) v.2;
      arrSetExn a (addi base 3) v.3;
      fill (addi i 1) ys
    end
  in
    fill 0 xs;
    matFromArrExn seqLen 4 (extArrOfArr extArrKindFloat64 a)
recursive
let buildForest = lam data. lam forest:[Tree]. lam index. lam data_len. lam seq_len.
  foldl (lam forest. lam seq.
    let newMessage = leafMsgMat seq_len seq in
    let newLeaf = Leaf {age=0.0, msg=newMessage, id=length forest} in
    let newForest = join ([forest,[newLeaf]]) in
    newForest
  ) [] data
end
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

	
let printIntList = lam xs:[Int].
  join ["[", strJoin "," (map int2string xs), "]"]

let splitPrint =  lam treeSamples. lam weights. foldl2 (lam acc. lam tree. lam w. 
	match collectSplits (get tree 0) with (_, splits) in
	let splits:[[Int]] = splits in
	let splits = join ["[", strJoin "," (map (lam split. printIntList split) splits),"]"] in
	join [acc, splits," ", float2string w, "\n"]
) "" treeSamples weights


let triGet = lam dTri:[[Float]]. lam i:Int. lam j:Int.
  -- assumes i > j
  get (get dTri (subi i 1)) j

let idx2 = lam n:Int. lam i:Int. lam j:Int.
  addi (muli i n) j

-- CFA-safe Float array creator. The stdlib polymorphic `arrCreate` uses
-- `unsafeCoerce` in its empty-array branch, which the alignment CFA pass run by
-- `--cps partial` cannot analyze ("Constant not supported in CFA: unsafeCoerce").
-- This builds the array via `arrMakeUninitFloat`, which is CFA-safe (the leaf
-- message construction already relies on it under `--cps partial`).
let arrCreateF : Int -> (Int -> Float) -> Arr Float = lam n. lam f.
  let a = arrMakeUninitFloat n in
  recursive let work = lam i.
    if eqi i n then () else (arrSetExn a i (f i); work (addi i 1))
  in
  work 0;
  a

let triToFlatSymArr = lam dTri:[[Float]].
  let n = addi (length dTri) 1 in
	arrCreateF (muli n n) (lam k.
	  let i = divi k n in
	  let j = modi k n in
	  if eqi i j then 0.0
	  else if gti i j then triGet dTri i j
	  else triGet dTri j i
	)


mexpr

let dGet = lam d:Arr Float. lam n:Int. lam i:Int. lam j:Int. arrGetExn d (idx2 n i j) in
-- helper: index in flattened n×n
let idx2 = lam n:Int. lam i:Int. lam j:Int. addi (muli i n) j in


------------------------------------------------------------
-- UTESTS
------------------------------------------------------------

utest
  -- Example triangular matrix for n=4
  -- Full symmetric should be:
  -- 0  5  3  5
  -- 5  0  6  2
  -- 3  6  0  7
  -- 5  2  7  0
  let dTri = [
    [5.0],           -- (1,0)
    [3.0, 6.0],      -- (2,0), (2,1)
    [5.0, 2.0, 7.0]  -- (3,0), (3,1), (3,2)
  ] in
  let a = triToFlatSymArr dTri in
  let n = 4 in

  -- length is n*n
  utest arrLength a with (muli n n) in

  -- diagonal zeros
  utest dGet a n 0 0 with 0.0 in
  utest dGet a n 1 1 with 0.0 in
  utest dGet a n 2 2 with 0.0 in
  utest dGet a n 3 3 with 0.0 in

  -- spot-check upper triangle values
  utest dGet a n 0 1 with 5.0 in
  utest dGet a n 0 2 with 3.0 in
  utest dGet a n 0 3 with 5.0 in
  utest dGet a n 1 2 with 6.0 in
  utest dGet a n 1 3 with 2.0 in
  utest dGet a n 2 3 with 7.0 in

  -- symmetry checks (lower triangle mirrors)
  utest dGet a n 1 0 with 5.0 in
  utest dGet a n 2 0 with 3.0 in
  utest dGet a n 3 0 with 5.0 in
  utest dGet a n 2 1 with 6.0 in
  utest dGet a n 3 1 with 2.0 in
  utest dGet a n 3 2 with 7.0 in
  () with () in

utest
  -- Edge case: n = 2 (one distance)
  -- Full:
  -- 0 9
  -- 9 0
  let dTri = [[9.0]] in
  let a = triToFlatSymArr dTri in
  let n = 2 in
  utest arrLength a with 4 in
  utest dGet a n 0 0 with 0.0 in
  utest dGet a n 1 1 with 0.0 in
  utest dGet a n 0 1 with 9.0 in
  utest dGet a n 1 0 with 9.0 in
  () with () in

utest
  -- Another sanity case: n = 3
  -- tri:
  -- (1,0)=1
  -- (2,0)=2, (2,1)=4
  -- Full:
  -- 0 1 2
  -- 1 0 4
  -- 2 4 0
  let dTri = [
    [1.0],
    [2.0, 4.0]
  ] in
  let a = triToFlatSymArr dTri in
  let n = 3 in
  utest dGet a n 0 1 with 1.0 in
  utest dGet a n 1 0 with 1.0 in
  utest dGet a n 0 2 with 2.0 in
  utest dGet a n 2 0 with 2.0 in
  utest dGet a n 1 2 with 4.0 in
  utest dGet a n 2 1 with 4.0 in
  utest dGet a n 0 0 with 0.0 in
  utest dGet a n 1 1 with 0.0 in
  utest dGet a n 2 2 with 0.0 in
  () with () in ()

