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

type DigraphEdge v = (v, v)
type Digraph v = { adj : Map v (Map v {}), parents : Map v (Map v {}), size : Int}

-- Returns an empty graph. Input: A compare function for vertices and an
-- equality functions for labels.
let digraphEmpty : all v. (v -> v -> Int) -> Digraph v =
  lam cmpv. {adj = mapEmpty cmpv, parents = mapEmpty cmpv, size=0}

-- Get comparison function for vertices.
let digraphCmpv : all v. Digraph v -> v -> v -> Int =
  lam g. mapGetCmpFun g.adj

-- Get equivalence function for vertices.
let digraphEqv : all v.  Digraph v -> v -> v -> Bool =
  lam g. lam v1. lam v2. eqi (digraphCmpv g v1 v2) 0

-- Get the vertices of the graph g.
let digraphVertices : all v. Digraph v -> [v] =
  lam g. mapKeys g.adj

-- Get the number of vertices in graph g.
let digraphCountVertices : all v. Digraph v -> Int =
  lam g. g.size

-- Get the outgoing edges from vertex v in graph g.
let digraphEdgesFrom : all v. v -> Digraph v -> (v -> Bool) -> [v] =
  lam v. lam g. lam p.
  mapKeys (mapFilterWithKey (lam t : v. lam. p t)
    (mapLookupOrElse (lam. error "Lookup failed") v g.adj))

-- Get the incoming edges to vertex v in graph g.
let digraphEdgesTo : all v. v -> Digraph v -> [v] =
  lam v. lam g.
  mapKeys (mapLookupOrElse (lam. error "Lookup failed") v g.parents)

-- Check whether g has vertex v.
let digraphHasVertex : all v. v -> Digraph v -> Bool = lam v. lam g.
  mapMem v g.adj

-- Check whether g has all the vertices vs.
let digraphHasVertices = lam vs. lam g.
  forAll (lam v. digraphHasVertex v g) vs

-- Check whether edges e1 and e2 are equal in graph g.
let digraphEdgeEq : all v. 
  Digraph v -> DigraphEdge v -> DigraphEdge v -> Bool =
  lam g. lam e1. lam e2.
  and (eqi (digraphCmpv g e1.0 e2.0) 0)
           (eqi (digraphCmpv g e1.1 e2.1) 0)

-- Get successor nodes of v.
let digraphSuccessors : all v. v -> Digraph v -> (v -> Bool) ->[v] = lam v. lam g. lam p.
  let outgoing = digraphEdgesFrom v g p in
  outgoing

-- Get predecessor nodes of v.
let digraphPredeccessors : all v. v -> Digraph v -> [v] = lam v. lam g.
  let incoming = digraphEdgesTo v g in
  incoming

-- Add vertex v to graph g if it doesn't already exist in g.
-- If v exists in g and check is true, an error is thrown.
-- If v exist in g and check is false, g stays unchanged.
let digraphAddVertexCheck : all v. v -> Digraph v -> Digraph v =
  lam v. lam g.
  {{{g with adj = mapInsert v (mapEmpty (digraphCmpv g)) g.adj} with size=addi g.size 1} 
    with parents=mapInsert v (mapEmpty (digraphCmpv g)) g.parents}

-- Add a vertex to graph g. Throws an error if v already exists in g.
let digraphAddVertex = lam v. lam g.
  digraphAddVertexCheck v g


-- Add edge e=(v1,v2,l) to g. Checks invariants iff utests are enabled.
let digraphAddEdge : all v. v -> v -> Digraph v -> Digraph v =
  lam v1. lam v2. lam g.
  let oldEdgeList =
    mapLookupOrElse (lam. error "Vertex not found") v1 g.adj
  in
  let oldPrList =
    mapLookupOrElse (lam. error "Vertex not found") v2 g.parents
  in
  {{g with adj = mapInsert v1 (mapInsert v2 {} oldEdgeList) g.adj} with parents=mapInsert v2 (mapInsert v1 {} oldPrList) g.parents}


-- Add a list of vertices to a graph g.
let digraphAddVertices = lam vs. lam g.
  foldl (lam g. lam v. digraphAddVertex v g) g vs

-- Add a list of edges to a graph g.
let digraphAddEdges : all v. [DigraphEdge v] -> Digraph v -> Digraph v =
  lam es. lam g.
  foldl (lam g. lam e : DigraphEdge v. digraphAddEdge e.0 e.1 g) g es


-- Remove an edge from the graph g.
let digraphRemoveEdge : all v. v -> v -> Digraph v -> Digraph v =
  lam from. lam to. lam g.
  let outgoing = mapFindExn from g.adj in
  let newOutgoing = mapFilterWithKey (lam o : v. lam. (not ((digraphEqv g) o to))) outgoing in
  let incoming = mapFindExn to g.parents in
  let newIncoming = mapFilterWithKey (lam o : v. lam. (not ((digraphEqv g) o from))) incoming in
  {{g with adj = mapInsert from newOutgoing g.adj} with parents=mapInsert to newIncoming g.parents}

let digraphEdges : all v. Digraph v -> [DigraphEdge v] = lam g.
  foldl (lam acc. lam b : (v, Map v {}).
    concat acc (map (lam t : v. (b.0, t)) (mapKeys b.1)))
    [] (mapBindings g.adj)

-- Print as dot format
let digraphPrintDot : all v.
  Digraph v  -> (v -> String) -> () =
  lam g. lam v2str. 
  print "digraph {";
  (map
    (lam e : DigraphEdge v l.
            print (v2str e.0);
            print " -> ";
            print (v2str e.1))
    (digraphEdges g));
  print "}\n"; ()


/-
let empty = digraphEmpty cmprVertex in

utest digraphVertices empty with []  in
utest digraphCountVertices empty with 0 in
utest digraphCountEdges empty with 0 in

let g = digraphAddVertex (RandomVarV {ident=0,state=0}) empty in
let g = digraphAddVertex (RandomVarV {ident=1,state=0})  g in
let g = digraphAddEdge (RandomVarV {ident=0,state=0}) (RandomVarV {ident=1,state=0}) g in

utest digraphCountVertices g with 2 in
utest digraphVertices g with [RandomVarV{ident=0,state=0},RandomVarV {ident=1,state=0}] in
utest digraphHasVertex (RandomVarV {ident=0,state=0}) g with true in
let g = digraphAddUpdateVertex (RandomVarV{ident=0,state=1}) g in
let g = digraphAddUpdateVertex (RandomVarV{ident=1,state=1}) g in
let g = digraphAddVertex (RandomVarV {ident=3,state=0}) g in
let g = digraphAddEdge (RandomVarV {ident=3,state=0}) (RandomVarV {ident=1,state=1}) g in
utest digraphVertices g with [RandomVarV{ident=0,state=1},RandomVarV {ident=1,state=1},RandomVarV {ident=3,state=0}] in
utest digraphSuccessors (RandomVarV{ident=0,state=1}) g with [(RandomVarV{ident=1,state=1})] in
utest digraphPredeccessors (RandomVarV{ident=1,state=1}) g with [(RandomVarV{ident=0,state=1}),(RandomVarV{ident=3,state=0})] in
let g = digraphRemoveEdge (RandomVarV {ident=3,state=0}) (RandomVarV {ident=1,state=1}) g in
utest digraphPredeccessors (RandomVarV{ident=1,state=1}) g with [(RandomVarV{ident=0,state=1})] in
-/
()

