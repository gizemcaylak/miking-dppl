-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Represents a directed graph with labeled edges.
--
-- Vertices and labels can be of any data types, as long as they have an
-- equality function.
--
-- An edge is represented as a triple (from, to, label), where the edge goes
-- from "from" to "to", and "label" is the label of the edge. There can be
-- several edges between two vertices.
--
-- Vertices must be unique: there cannot be two vertices whose value of the
-- equality function is true. This is maintained as invariant. Similarly, labels
-- between any pair of vertices must be unique; this is also maintained as
-- invariant.

include "option.mc"
include "seq.mc"
include "map.mc"
include "math.mc"
include "eqset.mc"
include "set.mc"

type DigraphEdge k = (k, k)
type Digraph k v = { children : Map k [k], parents : Map k [k], keyToVrtx: Map k v}

-- Returns an empty graph. Input: A compare function for vertices and an
-- equality functions for labels.
let digraphEmpty : all k. all v. (k -> k -> Int) -> Digraph k v =
  lam cmpv. {children = mapEmpty cmpk, parents = mapEmpty cmpk, keyToVrtx = mapEmpty cmpk}

-- Get comparison function for keys.
let digraphCmpk : all k. all v. Digraph k v -> k -> k -> Int =
  lam g. mapGetCmpFun g.keyToVrtx

-- Get equivalence function for vertices.
let digraphEqk : all k. all v. Digraph k v -> v -> v -> Bool =
  lam g. lam k1. lam k2. eqi (digraphCmpk g k1 k2) 0

-- Get the vertices of the graph g.
let digraphVertices : all v. all k. Digraph k v -> [v] =
  lam g. mapValues g.keyToVrtx

-- Get the number of vertices in graph g.
let digraphCountVertices : all k. all v. Digraph k v -> Int =
  lam g. mapSize g.keyToVrtx

-- Get the edges of the graph g.
let digraphEdges : all k. all v. Digraph k v -> [DigraphEdge k] = lam g.
  foldl (lam acc. lam b : (k, [k]).
    concat acc (map (lam t : k. (b.0, t)) b.1))
    [] (mapBindings g.children)

-- Get the edges of the graph g.
let digraphCountEdges : all k. all v. Digraph k v -> Int = lam g.
  foldl (lam acc. lam es. addi acc (length es)) 0 (mapValues g.children)

-- Get the outgoing edges from vertex v in graph g.
let digraphEdgesFrom : all k. all v. k -> Digraph k v -> [DigraphEdge k] =
  lam k. lam g.
  map (lam t : k. (k, t))
    (mapLookupOrElse (lam. error "Lookup failed") k g.children)

-- Get the incoming edges to vertex v in graph g.
let digraphEdgesTo : all k. all v. k -> Digraph k v -> [DigraphEdge k] =
  lam k. lam g.
   map (lam t : k. (t, k))
    (mapLookupOrElse (lam. error "Lookup failed") k g.parents)

-- Check whether g has vertex v.
let digraphHasVertex : all k. all v. k -> Digraph k v -> Bool = lam k. lam g.
  mapMem k g.keyToVrtx

-- Check whether g has all the vertices vs.
let digraphHasVertices = lam vs. lam g.
  forAll (lam v. digraphHasVertex v g) vs

-- Check whether edges e1 and e2 are equal in graph g.
let digraphEdgeEq : all k. all v.
  Digraph k v -> DigraphEdge k -> DigraphEdge k -> Bool =
  lam g. lam e1. lam e2.
  (and (eqi (digraphCmpk g e1.0 e2.0) 0)
           (eqi (digraphCmpk g e1.1 e2.1) 0))

-- Check whether g has edge e.
let digraphHasEdge : all k. all v. DigraphEdge k -> Digraph k v -> Bool =
  lam e. lam g.
  match e with (from, to) in
  match mapLookup from g.children with Some edgesFrom then
    any (lam t : k.
      eqi 0 (digraphCmpk g t to)
    ) edgesFrom
  else false

-- Check whether graph g has all the edges in es.
let digraphHasEdges = lam es. lam g.
  forAll (lam e. digraphHasEdge e g) es


-- Get successor nodes of v.
let digraphSuccessors :all k. all v. k -> Digraph k v -> [k] = lam k. lam g.
  let outgoing = digraphEdgesFrom k g in
  let successors = map (lam t : DigraphEdge k. t.1) outgoing in
  setToSeq (setOfSeq (digraphCmpk g) successors)

-- Get predecessor nodes of v.
let digraphPredeccessors : all k. all v. k -> Digraph k v -> [k] = lam k. lam g.
  distinct (lam k1. lam k2. eqi (digraphCmpk g k1 k2) 0)
    (map (lam tup : DigraphEdge k. tup.0) (digraphEdgesTo k g))


-- Add vertex v to graph g
let digraphAddVertexCheck : all k. all v. k -> Digraph k v -> Bool -> Digraph k v =
  lam k. lam g. lam check.
    {g with children = mapInsert k [] g.children}

-- Add a vertex to graph g. Throws an error if v already exists in g.
let digraphAddVertex = lam k. lam g.
  digraphAddVertexCheck k g true


/-
-- Add a vertex v to g. Updates the vertex v in graph g if v already exists in g.
let digraphUpdateVertex : all v. v -> Digraph v -> Digraph v =
  lam v. lam g.
    let edgeList = mapLookupOrElse (lam. error "Lookup failed") v g.adj in
    let m = mapRemove v g.adj in
    let m = foldl (lam acc. lam v2.
            let edgeLst = mapLookupOrElse (lam. error "Lookup failed") v2 acc in
            let newEdgeLst = map (lam e:v. if (digraphEqv g) v e then v else e) edgeLst in
            mapInsert v2 newEdgeLst acc) m (mapKeys m) in
    {g with adj = mapInsert v edgeList m}
-/
/-
let digraphRemoveVertex : all v. all l. v -> Digraph v l -> Digraph v l = lam v. lam g.
  utest digraphHasVertex v g with true in
    let m = mapRemove v g.adj in
    let m = foldl (lam acc. lam v2.
            let edgeLst = mapLookupOrElse (lam. error "Lookup failed") v2 acc in
            let newEdgeLst = filter (lam e:(v,l). not ((digraphEqv g) v e.0) ) edgeLst in
            mapInsert v2 newEdgeLst (mapRemove v2 acc)) m (mapKeys m) in
    {g with adj = m}
-/
-- Add edge e=(v1,v2,l) to g. Checks invariants iff utests are enabled.
let digraphAddEdge : all k. all v. k -> k -> Digraph k v -> Digraph k v =
  lam k1. lam k2. lam g.
  utest digraphHasVertex k1 g with true in
  utest digraphHasVertex k2 g with true in
  let oldEdgeList =
    mapLookupOrElse (lam. error "Vertex not found") k1 g.children
  in
  let oldParentList = mapLookupOrElse (lam. error "Vertex not found") k2 g.parents
  in
  {{g with children = mapInsert k1 (snoc oldEdgeList k2) g.children} with parents= mapInsert k2 (snoc oldParentList k1) g.parents}

-- Add a list of edges to a graph g.
let digraphAddEdges : all k. all v. [DigraphEdge k] -> Digraph k v -> Digraph k v =
  lam es. lam g.
  foldl (lam g. lam e : DigraphEdge k. digraphAddEdge e.0 e.1 g) g es

-- Remove an edge from the graph g.
let digraphRemoveEdge : all k. all v. k -> k -> Digraph k v -> Digraph k v =
  lam from. lam to. lam g.
  utest (digraphHasEdge (from, to) g) with true in
  let outgoing = mapFindExn from g.children in
  let newOutgoing = filter (lam o : v. (not ((digraphEqv g) o to))) outgoing in
  let incoming = mapFindExn to g.parents in
  let newIncoming = filter (lam o : v. (not ((digraphEqv g) o from))) incoming in

  {{g with children = mapInsert from newOutgoing g.children} with parents=newIncoming}


-- Print as dot format
let digraphPrintDot : all v.
  Digraph v l -> (v -> String)-> () =
  lam g. lam v2str.
  print "digraph {";
  (map
    (lam e : DigraphEdge v .
            print (v2str e.0);
            print " -> ";
            print (v2str e.1)
            )
    (digraphEdges g));
  print "}\n"; ()

