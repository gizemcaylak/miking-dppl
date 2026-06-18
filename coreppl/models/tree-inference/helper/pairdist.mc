include "tensor.mc"
include "ext/mat-ext.mc"
include "buildTree.mc"
type Partition
con Partition : [Int] -> Partition
let partSingleton = lam i. Partition [i]

let partUnion = lam p1. lam p2.
  match p1 with Partition xs in
  match p2 with Partition ys in
  let zs = merge subi xs ys in
  Partition zs

let partElems = lam p. match p with Partition xs in xs

let idx2 = lam n:Int. lam i:Int. lam j:Int. addi (muli i n) j

let dGet = lam d:Arr Float. lam n:Int. lam i:Int. lam j:Int. arrGetExn d (idx2 n i j)

let dSet = lam d:Arr Float. lam n:Int. lam i:Int. lam j:Int. lam x:Float. arrSetExn d (idx2 n i j) x

let removeRowsCols = lam d. lam i. lam j. lam keep.
  -- Rebuild base rows among the kept nodes
  foldl (lam rows. lam ai.
      if eqi ai 0 then rows else --only keep lower triangle
      -- build row for 'a' against all earlier kept nodes
      let rowKeep = get d (subi ai 1) in --since we keep indices 1,2,3 for rows as 0,1,2
      let row = foldli (lam row. lam aj. lam e. if or (eqi aj i) (eqi aj j) then row else snoc row e) [] rowKeep in
      if null row then rows else snoc rows row
    ) [] keep

let norm4 = lam v:[Float].
  let s = foldl addf 0.0 v in
  if ltf s 1e-30 then [0.25,0.25,0.25,0.25] else map (lam x. divf x s) v

let dot4 = lam a:[Float]. lam b:[Float].
  foldl2 (lam acc. lam x. lam y. addf acc (mulf x y)) 0.0 a b

let msgRow4 = lam msg:Mat Float. lam r:Int.
  [ matGetExn msg r 0
  , matGetExn msg r 1
  , matGetExn msg r 2
  , matGetExn msg r 3 ]

recursive
let msgDistAcc = lam m1:Mat Float. lam m2:Mat Float. lam l:Int. lam s:Int. lam acc:Float.
  if eqi s l then acc else
    let p1 = norm4 (msgRow4 m1 s) in
    let p2 = norm4 (msgRow4 m2 s) in
    let mismatch = subf 1.0 (dot4 p1 p2) in
    msgDistAcc m1 m2 l (addi s 1) (addf acc mismatch)
end

let msgDistance = lam t1. lam t2. lam l:Int.
  msgDistAcc (getMsg t1) (getMsg t2) l 0 0.0

let indexOfUnion = lam pairSets. lam u.
  recursive let helper = lam i.
    if eqi i (length pairSets) then negi 1
    else let v = get pairSets i in
      if eqSeq eqi v u then i else helper (addi i 1)
  in helper 0

let slice = lam seq. lam beg. lam mend.
    subsequence seq beg (subi mend beg)

-- returns [((i,j), dij')] for i>j
let flattenSymmetricFlatArr = lam n:Int. lam d:Arr Float. lam fLog.
  recursive let go = lam i:Int. lam j:Int. lam acc:[((Int,Int),Float)].
    if eqi i n then reverse acc
    else if eqi j i then go (addi i 1) 0 acc
    else
      let dij = fLog (dGet d n i j) in
      go i (addi j 1) (cons (((j,i),dij)) acc)
  in go 0 0 []
recursive
let sumAndPairs = lam fd. lam acc:Float. lam pairs:[(Int,Int)].
  if null fd then (acc, reverse pairs)
  else
    let e = head fd in
    let ij = e.0 in
    let v  = e.1 in
    sumAndPairs (tail fd) (addf acc v) (cons ij pairs)
end
let maxList = lam xs.
  foldl (lam acc. lam x. if gtf x acc then x else acc) (negf inf) xs

let logSumExp = lam ls.
  let m = maxList ls in
  let s = foldl addf 0. (map (lam x. exp (subf x m)) ls) in
  addf m (log s)

let pairCalcP = lam partitions. lam n:Int. lam d:Arr Float. lam fLog.
  if eqi n 2 then
    let idxPairs = [(0,1)] in
    let pairSets = [ partElems (partUnion (get partitions 0) (get partitions 1)) ] in
    let p = [1.0] in
    (idxPairs, pairSets, p)
  else
    let fd = flattenSymmetricFlatArr n d fLog in
    -- collect log-scores
    let logs = map (lam v. v.1) fd in
    let logZ = logSumExp logs in
    -- probabilities
    let p = map (lam v. exp (subf v.1 logZ)) fd in
    /-let sumP = foldl addf 0. p in
    printLn (join ["d:",(strJoin " " (map float2string (extArrToSeq ( extArrOfArr extArrKindFloat64 d))))]);
    printLn (join ["d:",(strJoin " " (map (lam i. join ["(",int2string i.0, ",",int2string i.1,")"]) indices))]);
    printLn (join ["fd:",(strJoin " " (map float2string logs))]);
    printLn (join ["p:",(strJoin " " (map float2string p))," sum: ",(float2string sumP)]);-/
    --match sumAndPairs fd 0.0 [] with (sumd, idxPairs) in
    --let p = map (lam v. divf v.1 sumd) fd in
    let idxPairs = map (lam v. v.0) fd in
    --let ldf = int2float (length fd) in
    --let p = map (lam v. divf 1. ldf) fd in
    let pairSets = map (lam ij. match ij with (i,j) in partElems (partUnion (get partitions i) (get partitions j))) idxPairs in
    /-printLn ":";
    iter (lam ij. match ij with (i,j) in printLn (join ["i:",(strJoin " " (map int2string (partElems (get partitions i))))
      , "j:",(strJoin " " (map int2string (partElems (get partitions j))))
      ,"ij:",(strJoin " " (map int2string (partElems (partUnion (get partitions i) (get partitions j)))))

      ])) idxPairs;-/
    (idxPairs, pairSets, p)

let printBlock = lam block.
  let labels = map (lam x. strJoin "" ["L", (int2string x)]) block in
  let inside = strJoin ","  labels in
  let out = strJoin "" ["{", inside ,"}"] in
  printLn out

let printpartitions = lam partitions.
  iter printBlock partitions


let isKept = lam k:Int. lam i:Int. lam j:Int.
  and (neqi k i) (neqi k j)

-- map new index -> old index (skipping i and j), for new indices < z
let oldIndex = lam t:Int. lam i:Int. lam j:Int.
  -- assumes t is in [0 .. n-3]
  let t = if geqi t (mini i j) then addi t 1 else t in
  if geqi t (maxi i j) then addi t 1 else t
-- this can be
let mergeIntoLast = lam n:Int. lam d:Arr Float. lam i:Int. lam j:Int.
  let m = subi n 1 in
  let z = subi m 1 in
  -- gonna be an m by m matrix (flattened)
  arrCreateF (muli m m) (lam k.
    let r = divi k m in -- row 
    let c = modi k m in -- column
    if eqi r c then 0.0 -- diagonal is 0
    else
      -- Case A: neither coordinate is the new merged node (both < z)
      if and (lti r z) (lti c z) then
        let ro = oldIndex r i j in
        let co = oldIndex c i j in
        dGet d n ro co

      -- Case B: one coordinate is z (merged node), other is < z
      else
        let t = if eqi r z then c else r in
        let ko = oldIndex t i j in
        let dik = dGet d n i ko in
        let djk = dGet d n j ko in
        mulf 0.5 (addf dik djk)
  )

let idx2 = lam n:Int. lam i:Int. lam j:Int. addi (muli i n) j
let dGet = lam d:Arr Float. lam n:Int. lam i:Int. lam j:Int. arrGetExn d (idx2 n i j)

-- map new index -> old index (skipping i and j), for new indices < z
let oldIndex = lam t:Int. lam i:Int. lam j:Int.
  let t = if geqi t (mini i j) then addi t 1 else t in
  if geqi t (maxi i j) then addi t 1 else t

let mergeIntoLastFromMsgs =
  lam n:Int. lam d:Arr Float. lam trees. lam seqLen:Int. lam i:Int. lam j:Int. lam parent.
    let m = subi n 1 in
    let z = subi m 1 in
    arrCreateF (muli m m) (lam k.
      let r = divi k m in
      let c = modi k m in
      if eqi r c then 0.0 else
      if and (lti r z) (lti c z) then
        -- copy existing distances among kept nodes
        let ro = oldIndex r i j in
        let co = oldIndex c i j in
        dGet d n ro co
      else
        -- distances involving merged node z computed from messages
        let t = if eqi r z then c else r in
        let ko = oldIndex t i j in
        let tk = get trees ko in
        msgDistance parent tk seqLen
    )

let newDistanceMatrix = lam n:Int. lam d:Arr Float. lam pair.
  mergeIntoLast n d pair.0 pair.1

let newDistanceMatrixMessage = lam n:Int. lam d:Arr Float. lam pair. lam parent. lam trees. lam seqLength.
  mergeIntoLastFromMsgs n d trees seqLength pair.0 pair.1 parent 

-- check whether a sorted sequence sub is a subset of the sorted sequence sup
let isSubset = lam sub. lam sup.
  recursive let helper = lam sub. lam sup.
    if eqi (length sub) 0 then true
    else if eqi (length sup) 0 then false
    else
      let a = head sub in
      let b = head sup in
      if eqi a b then
        helper (tail sub) (tail sup)
      else if lti b a then
        -- sup head is too small, skip it
        helper sub (tail sup)
      else -- b > a, so a cannot appear later (since sorted)
        false
  in
  helper sub sup

let swapPartner = lam partitions. lam weights. lam leafSets:[[Int]]. lam prev:[Int].
  -- prev = (1 2 3)
  -- partitions = [(1 2), (3), (4)]
  let inputs = filter (lam i. isSubset i prev) partitions in
  -- inputs = [(1 2), (3)]
  -- leafSets = [(1,2,3),(1,2,4),(3,4)]
  let something = zip weights leafSets in
  let f = lam weightedPair.
    xor (isSubset (get inputs 0) weightedPair.1)
    (isSubset (get inputs 1) weightedPair.1) in
  match unzip (filter f something) with (weightsN, leafSetsN) in
  --printLn (foldl (lam acc. lam l. join [acc,"(",strJoin "," (map int2string l),")"] )  "after:\n" leafSetsN);
  --print "prev:";printLn (strJoin "," (map int2string prev)) ;
  if null leafSetsN then TreeInferenceCategorical weights leafSets --if it is the only option
  else
    let sumW = foldl addf 0.0 weightsN in
    let weightsN = map (lam e. divf e sumW) weightsN in
    TreeInferenceCategorical weightsN leafSetsN

let propose = lam d. lam partitions. lam f. lam n.
  match pairCalcP partitions n d f with (idxPairs,pairSets,p) in
  let pairU = assume (TreeInferenceCategorical p pairSets) in
  --let pairU = assumeDrift (TreeInferenceCategorical p pairSets) (swapPartner (map partElems partitions ) p pairSets) in
  -- correction ---
  cancel (observe pairU (TreeInferenceCategorical p pairSets)); -- this part should stay the same since kernel itself corrects?
  let logU = log (divf 1. (int2float (length p))) in
  weight logU;
  -----------------
  let idx = indexOfUnion pairSets pairU in
  let idxPair = get idxPairs idx in
  let i = idxPair.0 in
  let j = idxPair.1 in
  --printLn (foldl (lam acc. lam l. join [acc,"(",strJoin "," (map int2string l),")"] )  "pairSets:\n" pairSets);
  --printLn (join ["selectedPair: ", int2string i, int2string j]);
  let min = mini i j in
  let max = maxi i j in
  let pi  = get partitions i in
  let pj  = get partitions j in
  let mergedSet = partUnion pi pj in
  let partitionsNew =
    join ([ slice partitions 0 min,
            slice partitions (addi min 1) max,
            slice partitions (addi max 1) n,
            [mergedSet] ]) in
  let dNew = newDistanceMatrix n d idxPair in
  (idxPair, partitionsNew, dNew)
mexpr

-- UTESTS --
utest
  let p1 = partSingleton 2 in
  let p2 = partSingleton 0 in
  let u  = partUnion p1 p2 in
  partElems u
with [0,2] in

utest
  let pairSets = [[0,1],[0,2],[1,2]] in
  ( indexOfUnion pairSets [0,2]
  , indexOfUnion pairSets [2,3]
  , indexOfUnion pairSets [0,1]
  , indexOfUnion pairSets [1,2] )
with (1, -1, 0, 2)
in
utest
  let n = 4 in
  recursive let g = lam i. lam j.
    if eqi i j then 0.0 else
    if and (eqi i 1) (eqi j 0) then 5.0 else
    if and (eqi i 2) (eqi j 0) then 3.0 else
    if and (eqi i 2) (eqi j 1) then 6.0 else
    if and (eqi i 3) (eqi j 0) then 5.0 else
    if and (eqi i 3) (eqi j 1) then 2.0 else
    if and (eqi i 3) (eqi j 2) then 7.0 else
    g j i
  in
  let d = arrCreateF (muli n n) (lam k.
    let i = divi k n in
    let j = modi k n in
    g i j) in
  let fd = flattenSymmetricFlatArr n d (lam x. x) in
  length fd
with 6 in 
utest
  let fd = [(((1,0),0.2)),(((2,0),0.3)),(((2,1),0.5))] in
  sumAndPairs fd 0.0 []
with (1.0, [(1,0),(2,0),(2,1)]) in

utest
  let partitions =
    [partSingleton 0, partSingleton 1, partSingleton 2, partSingleton 3] in
  let n = 4 in
  recursive let g = lam i. lam j.
    if eqi i j then 0.0 else
    if and (eqi i 1) (eqi j 0) then 5.0 else
    if and (eqi i 2) (eqi j 0) then 3.0 else
    if and (eqi i 2) (eqi j 1) then 6.0 else
    if and (eqi i 3) (eqi j 0) then 5.0 else
    if and (eqi i 3) (eqi j 1) then 2.0 else
    if and (eqi i 3) (eqi j 2) then 7.0 else
    g j i
  in
  let d = arrCreateF (muli n n) (lam k.
    let i = divi k n in
    let j = modi k n in
    g i j) in
  let f = lam c. negf c in
  match pairCalcP partitions n d f with (idxPairs, _, p) in
  let bestIdx =
    foldli (lam acc. lam i. lam x.
      if gtf x (get p acc) then i else acc) 0 p in
  get idxPairs bestIdx
with (1,3) in

utest
  let n = 4 in
  recursive let g = lam i. lam j.
    if eqi i j then 0.0 else
    if and (eqi i 1) (eqi j 0) then 5.0 else
    if and (eqi i 2) (eqi j 0) then 3.0 else
    if and (eqi i 2) (eqi j 1) then 6.0 else
    if and (eqi i 3) (eqi j 0) then 5.0 else
    if and (eqi i 3) (eqi j 1) then 2.0 else
    if and (eqi i 3) (eqi j 2) then 7.0 else
    g j i
  in
  let d = arrCreateF (muli n n) (lam k.
    let i = divi k n in
    let j = modi k n in
    g i j) in
  let d2 = mergeIntoLast n d 3 1 in
  ( dGet d2 3 2 0
  , dGet d2 3 2 1 )
with (5.0, 6.5) in
-- Helper: make a flattened n×n distance matrix from a function g(i,j)
-- g is assumed symmetric and g(i,i)=0 in the caller logic if desired.
let mkMat = lam n:Int. lam g.
  arrCreateF (muli n n) (lam k.
    let i = divi k n in
    let j = modi k n in
    g i j
  ) in

-- Helper: float sum
let sumFloats = lam xs.
  foldl addf 0.0 xs in
utest
  -- n=5, remove i=0 and j=3. Remaining old indices: [1,2,4] -> new indices [0,1,2]
  utest oldIndex 0 0 3 with 1 in
  utest oldIndex 1 0 3 with 2 in
  utest oldIndex 2 0 3 with 4 in
  () with () in
utest
  let n = 4 in
  -- symmetric distances:
  -- d(1,0)=5  d(2,0)=3 d(2,1)=6  d(3,0)=5 d(3,1)=2 d(3,2)=7
  let d =
    mkMat n (lam i. lam j.
      if eqi i j then 0.0
      else if and (eqi i 1) (eqi j 0) then 5.0
      else if and (eqi i 2) (eqi j 0) then 3.0
      else if and (eqi i 2) (eqi j 1) then 6.0
      else if and (eqi i 3) (eqi j 0) then 5.0
      else if and (eqi i 3) (eqi j 1) then 2.0
      else if and (eqi i 3) (eqi j 2) then 7.0
      else if and (eqi i 0) (eqi j 1) then 5.0
      else if and (eqi i 0) (eqi j 2) then 3.0
      else if and (eqi i 1) (eqi j 2) then 6.0
      else if and (eqi i 0) (eqi j 3) then 5.0
      else if and (eqi i 1) (eqi j 3) then 2.0
      else if and (eqi i 2) (eqi j 3) then 7.0
      else 0.0
    ) in

  -- merge i=3 and j=1 => new size m=3 (indices: {0},{2},{(1,3)})
  let dNew = mergeIntoLast n d 3 1 in
  let m = 3 in

  -- diagonal is 0
  utest (dGet dNew m 0 0) with 0.0 in
  utest (dGet dNew m 1 1) with 0.0 in
  utest (dGet dNew m 2 2) with 0.0 in

  -- distance between remaining old 2 and 0 should stay 3.0
  utest (dGet dNew m 1 0) with 3.0 in

  -- merged node z has index 2.
  -- z–{0}: 0.5*(d(3,0)+d(1,0)) = 0.5*(5+5)=5
  utest (dGet dNew m 2 0) with 5.0 in
  -- z–{2}: 0.5*(d(3,2)+d(1,2)) = 0.5*(7+6)=6.5
  utest (dGet dNew m 2 1) with 6.5 in

  () with () in

  utest
  let n = 4 in
  let partitions = [partSingleton 0, partSingleton 1, partSingleton 2, partSingleton 3] in

  -- use any matrix; we just want pairSets and idxPairs
  let d = mkMat n (lam i. lam j.
    if eqi i j then 0.0 else 1.0
  ) in

  match pairCalcP partitions n d (lam x. x) with (idxPairs, pairSets, p) in

  -- pairSets[k] must be findable at the same position
  recursive let check = lam k:Int.
    if eqi k (length pairSets) then true
    else
      let u = get pairSets k in
      and (eqi (indexOfUnion pairSets u) k) (check (addi k 1))
  in
  utest (check 0) with true in
  () with ()
  in 

let isSortedStrict = lam xs:[Int].
  recursive let go = lam xs:[Int].
    match xs with [] then true
    else match xs with [x] then true
    else match xs with [x,y] ++ rest then
      and (lti x y) (go (cons y rest))
    else never
  in go xs

in

let memInt = lam x:Int. lam xs:[Int].
  foldl (lam acc. lam y. or acc (eqi x y)) false xs

in
-- check disjointness between two sorted unique lists
let disjoint = lam xs:[Int]. lam ys:[Int].
  recursive let go = lam xs:[Int]. lam ys:[Int].
    if null xs then true else
    if null ys then true else
      let a = head xs in
      let b = head ys in
      if eqi a b then false
      else if lti a b then go (tail xs) ys
      else go xs (tail ys)
  in go xs ys

in
-- merge union of many lists (assumes each list sorted+unique)
recursive let mergeMany = lam xss:[[Int]]. lam acc:[Int].
  if null xss then acc
  else
    let xs = head xss in
    let rest = tail xss in
    -- use your merge function (cmp = subi) to union:
    let acc = merge subi acc xs in
    mergeMany rest acc

in

-- check "cover exactly 0..(m-1)" given partitions
let partitionsCover = lam partitions. lam m:Int.
  let elems = map partElems partitions in
  let allx = mergeMany elems [] in
  and (eqi (length allx) m)
      (and (isSortedStrict allx)
           (foldl (lam ok. lam i. and ok (eqi (get allx i) i)) true (create m (lam i. i))))

in
let partitionsDisjoint = lam partitions:[Partition].
  let elems = map partElems partitions in
  let n = length elems in
  indexFoldu (lam ok. lam i.
    indexFoldu (lam ok2. lam j.
      if eqi i j then ok2
      else and ok2 (disjoint (get elems i) (get elems j))
    ) ok 0 n
  ) true 0 n

in
let partitionsSortedStrict = lam partitions:[Partition].
  foldl (lam ok. lam p. and ok (isSortedStrict (partElems p))) true partitions

in
-- ----------------------------------------
-- Matrix helpers (flattened n×n float arr)
-- ----------------------------------------

let mkMat = lam n:Int. lam g.
  arrCreateF (muli n n) (lam k.
    let i = divi k n in
    let j = modi k n in
    g i j
  )

in
-- Reference merge: explicitly build new matrix by
-- removing rows/cols i,j and appending merged node at the end.
-- This is "slow but obviously correct", used only in tests.
let mergeIntoLastRef = lam n:Int. lam d:Arr Float. lam i:Int. lam j:Int.
  let m = subi n 1 in
  let keep = filter (lam k. and (neqi k i) (neqi k j)) (create n (lam t. t)) in
  -- map new index r (0..m-2) -> old index keep[r]
  let keepAt = lam r:Int. get keep r in
  -- merged node is new index (m-1)
  let z = subi m 1 in
  arrCreateF (muli m m) (lam k.
    let r = divi k m in
    let c = modi k m in
    if eqi r c then 0.0 else
    if and (lti r z) (lti c z) then
      let ro = keepAt r in
      let co = keepAt c in
      dGet d n ro co
    else
      let t = if eqi r z then c else r in
      let ko = keepAt t in
      let dik = dGet d n i ko in
      let djk = dGet d n j ko in
      mulf 0.5 (addf dik djk)
  )

in
let arrEqFloatTol = lam a:Arr Float. lam b:Arr Float. lam tol:Float.
  let n = arrLength a in
  if neqi n (arrLength b) then false else
  indexFoldu (lam ok. lam k.
    and ok (ltf (absf (subf (arrGetExn a k) (arrGetExn b k))) tol)
  ) true 0 n

in

-- Ensures: for every k, indexOfUnion(pairSets, pairSets[k]) == k
let pairSetsSelfIndexOk = lam pairSets:[[Int]].
  recursive let go = lam k:Int.
    if eqi k (length pairSets) then true else
      let u = get pairSets k in
      and (eqi (indexOfUnion pairSets u) k) (go (addi k 1))
  in go 0

in
-- Ensures: pairSets[k] == union(partitions[i], partitions[j]) where (i,j)=idxPairs[k]
let pairSetsMatchIdxPairs = lam partitions:[Partition]. lam idxPairs:[(Int,Int)]. lam pairSets:[[Int]].
  let n = length idxPairs in
  indexFoldu (lam ok. lam k.
    let ij = get idxPairs k in
    let u  = partElems (partUnion (get partitions ij.0) (get partitions ij.1)) in
    and ok (eqSeq eqi u (get pairSets k))
  ) true 0 n
in
-- -------------------------
-- JC log-score sanity checks
-- -------------------------
-- A numerically stable log(1 - exp(-x)) for x>0
let log1mexp = lam x:Float.
  -- if x is tiny, 1-exp(-x) ~ x
  if ltf x 1e-6 then log x else log (subf 1.0 (exp (negf x)))
in
let log1p = lam u:Float. log (addf 1.0 u)
in
-- Correct JC-inspired log-score using t ≈ c/L:
-- x = 4c/(3L)
-- logScore(c) = (c*beta)*log(1-exp(-x)) + ((L-c)*beta)*log(1+3exp(-x))
let jcLogScore = lam c:Float. lam l:Float. lam beta:Float.
  let x = mulf (divf 4.0 3.0) (divf c l) in
  let termDiff = mulf (mulf c beta) (log1mexp x) in
  let termSame = mulf (mulf (subf l c) beta) (log1p (mulf 3.0 (exp (negf x)))) in
  addf termDiff termSame
in
-- monotonic sanity: for fixed L,beta, score should generally decrease as c increases 
let isMostlyDecreasing = lam xs:[Float].
  let n = length xs in
  if lti n 2 then true else
    -- allow a few small violations
    let okCount =
      indexFoldu (lam acc. lam i.
        if eqi i (subi n 1) then acc else
          let a = get xs i in
          let b = get xs (addi i 1) in
          if leqf b a then addi acc 1 else acc
      ) 0 0 n in
    gti (muli okCount 10) (muli (subi n 1) 7)  -- okCount/(n-1) > 0.7
in

--  Partition union produces sorted unique list
utest
  let p1 = partSingleton 2 in
  let p2 = partSingleton 0 in
  let u  = partUnion p1 p2 in
  (partElems u, isSortedStrict (partElems u))
with ([0,2], true)
in

-- indexOfUnion behaves
utest
  let pairSets = [[0,1],[0,2],[1,2]] in
  ( indexOfUnion pairSets [0,2]
  , indexOfUnion pairSets [2,3]
  , indexOfUnion pairSets [0,1]
  , indexOfUnion pairSets [1,2] )
with (1, -1, 0, 2)
in

-- oldIndex mapping sanity (example)
utest
  -- n=5, remove i=0 and j=3. Remaining old indices: [1,2,4] -> new indices [0,1,2]
  ( oldIndex 0 0 3
  , oldIndex 1 0 3
  , oldIndex 2 0 3 )
with (1,2,4)
in

-- mergeIntoLast correctness vs reference for a concrete n=4 case
utest
  let n = 4 in
  let d =
    mkMat n (lam i. lam j.
      if eqi i j then 0.0
      else if and (eqi i 1) (eqi j 0) then 5.0
      else if and (eqi i 2) (eqi j 0) then 3.0
      else if and (eqi i 2) (eqi j 1) then 6.0
      else if and (eqi i 3) (eqi j 0) then 5.0
      else if and (eqi i 3) (eqi j 1) then 2.0
      else if and (eqi i 3) (eqi j 2) then 7.0
      else
        -- symmetric fill
        if gti i j then 0.0 else
        if and (eqi j 1) (eqi i 0) then 5.0 else
        if and (eqi j 2) (eqi i 0) then 3.0 else
        if and (eqi j 2) (eqi i 1) then 6.0 else
        if and (eqi j 3) (eqi i 0) then 5.0 else
        if and (eqi j 3) (eqi i 1) then 2.0 else
        if and (eqi j 3) (eqi i 2) then 7.0 else 0.0
    ) in
  let i = 3 in
  let j = 1 in
  let a = mergeIntoLast n d i j in
  let b = mergeIntoLastRef n d i j in
  arrEqFloatTol a b 1e-9
with true
in

-- mergeIntoLast correctness vs reference on another removal pattern (n=5)
utest
  let n = 5 in
  -- make a simple symmetric matrix: d(i,j)=10*i + j for i>j, mirrored
  let d =
    mkMat n (lam i. lam j.
      if eqi i j then 0.0
      else if gti i j then int2float (addi (muli 10 i) j)
      else int2float (addi (muli 10 j) i)
    ) in
  let i = 4 in
  let j = 0 in
  let a = mergeIntoLast n d i j in
  let b = mergeIntoLastRef n d i j in
  arrEqFloatTol a b 1e-9
with true
in

-- partitions invariants: sorted, disjoint, cover
utest
  let parts =
    [ Partition [0]
    , Partition [1]
    , Partition [2]
    , Partition [3] ] in
  ( partitionsSortedStrict parts
  , partitionsDisjoint parts
  , partitionsCover parts 4 )
with (true,true,true)
in

-- after one merge, invariants still hold
utest
  let parts0 =
    [ Partition [0]
    , Partition [1]
    , Partition [2]
    , Partition [3] ] in
  let merged = partUnion (get parts0 3) (get parts0 1) in -- {1,3}
  let parts1 = [ Partition [0], Partition [2], merged ] in
  ( partitionsSortedStrict parts1
  , partitionsDisjoint parts1
  , partitionsCover parts1 4 )
with (true,true,true)
in

-- pairCalcP consistency: pairSets correspond to idxPairs and indexOfUnion finds itself
utest
  let n = 4 in
  let partitions = [partSingleton 0, partSingleton 1, partSingleton 2, partSingleton 3] in
  let d = mkMat n (lam i. lam j. if eqi i j then 0.0 else 1.0) in
  -- constant log-score -> uniform probs, but we only test structure
  let fLog = lam c. 0.0 in
  match pairCalcP partitions n d fLog with (idxPairs, pairSets, p) in
  ( pairSetsSelfIndexOk pairSets
  , pairSetsMatchIdxPairs partitions idxPairs pairSets
  , eqi (length p) (length idxPairs)
  , eqi (length idxPairs) 6 )
with (true,true,true,true)
in

-- pairCalcP: best pair under a simple log-score should match expectation
-- Here fLog(c) = -c (so smaller distance => higher log-score).
-- In the toy distances, smallest is between (3,1) = 2.0, so best is (3,1) (or (1,3) depending on ordering).
utest
  let n = 4 in
  let partitions = [partSingleton 0, partSingleton 1, partSingleton 2, partSingleton 3] in
  let d =
    mkMat n (lam i. lam j.
      if eqi i j then 0.0
      else if and (eqi i 1) (eqi j 0) then 5.0
      else if and (eqi i 2) (eqi j 0) then 3.0
      else if and (eqi i 2) (eqi j 1) then 6.0
      else if and (eqi i 3) (eqi j 0) then 5.0
      else if and (eqi i 3) (eqi j 1) then 2.0
      else if and (eqi i 3) (eqi j 2) then 7.0
      else if gti i j then 0.0
      else dGet (mkMat n (lam a. lam b. 0.0)) n 0 0 -- dummy
    ) in
  -- fill symmetry for missing entries
  let d = mkMat n (lam i. lam j. if gti i j then dGet d n i j else if lti i j then dGet d n j i else 0.0) in
  let fLog = lam c. negf c in
  match pairCalcP partitions n d fLog with (idxPairs, _, p) in
  let bestIdx =
    foldli (lam acc. lam i. lam x.
      if gtf x (get p acc) then i else acc) 0 p in
  let best = get idxPairs bestIdx in
  -- accept either orientation if your idxPairs stores (j,i) etc
  or (and (eqi best.0 3) (eqi best.1 1)) (and (eqi best.0 1) (eqi best.1 3))
with true
in

-- JC log-score monotonic sanity
utest
  let l = 800.0 in
  let beta = divf 16.0 l in -- your k/L example
  let xs = map (lam c. jcLogScore (int2float c) l beta) (create 50 (lam i. addi i 1)) in
  isMostlyDecreasing xs
with true
in 
let sumFloats = lam xs:[Float]. foldl addf 0.0 xs in


-- argmax index of a float list (first max)
let argmax = lam xs:[Float].
  foldli (lam best. lam i. lam x.
    if gtf x (get xs best) then i else best
  ) 0 xs in

-- argmax(logScore) == argmax(p)
-- Build fd ourselves, then compare:
--   argmax over fd[i].1  (log-scores)
-- with
--   argmax over p[i]
utest
  let n = 4 in
  let partitions = [partSingleton 0, partSingleton 1, partSingleton 2, partSingleton 3] in

  -- same toy distances
  let d =
    mkMat n (lam i. lam j.
      if eqi i j then 0.0
      else if and (eqi i 1) (eqi j 0) then 5.0
      else if and (eqi i 2) (eqi j 0) then 3.0
      else if and (eqi i 2) (eqi j 1) then 6.0
      else if and (eqi i 3) (eqi j 0) then 5.0
      else if and (eqi i 3) (eqi j 1) then 2.0
      else if and (eqi i 3) (eqi j 2) then 7.0
      else if gti i j then 0.0
      else 0.0
    ) in
  let d = mkMat n (lam i. lam j.
    if eqi i j then 0.0 else if gti i j then dGet d n i j else dGet d n j i
  ) in

  let fLog = lam c. negf c in

  let fd = flattenSymmetricFlatArr n d fLog in
  let logs = map (lam v. v.1) fd in
  let logZ = logSumExp logs in
  let pRef = map (lam v. exp (subf v.1 logZ)) fd in

  match pairCalcP partitions n d fLog with (_, _, p) in

  -- they should pick the same index (since pairCalcP uses the same fd ordering)
  eqi (argmax logs) (argmax p)
with true
in

-- sum(p) ≈ 1
utest
  let n = 4 in
  let partitions = [partSingleton 0, partSingleton 1, partSingleton 2, partSingleton 3] in

  let d = mkMat n (lam i. lam j.
    if eqi i j then 0.0
    else
      -- arbitrary positive distances
      int2float (addi 1 (absi (subi i j)))
  ) in

  -- any bounded log-score (here: -distance)
  let fLog = lam c. negf c in

  match pairCalcP partitions n d fLog with (_, _, p) in
  approxEqf 1e-9 (sumFloats p) 1.0 
with true
in ()


