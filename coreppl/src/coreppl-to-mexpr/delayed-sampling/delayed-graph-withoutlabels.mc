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
type Digraph v = { adj : Map v [v] }

-- Returns an empty graph. Input: A compare function for vertices and an
-- equality functions for labels.
let digraphEmpty : all v. (v -> v -> Int) -> Digraph v =
  lam cmpv. {adj = mapEmpty cmpv}

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
  lam g. mapSize g.adj

-- Get the edges of the graph g.
let digraphEdges : all v. Digraph v -> [DigraphEdge v] = lam g.
  foldl (lam acc. lam b : (v, [v]).
    concat acc (map (lam t : v. (b.0, t)) b.1))
    [] (mapBindings g.adj)

-- Get the edges of the graph g.
let digraphCountEdges : all v. Digraph v -> Int = lam g.
  foldl (lam acc. lam es. addi acc (length es)) 0 (mapValues g.adj)

-- Get the outgoing edges from vertex v in graph g.
let digraphEdgesFrom : all v. v -> Digraph v -> [DigraphEdge v] =
  lam v. lam g.
  map (lam t : v. (v, t))
    (mapLookupOrElse (lam. error "Lookup failed") v g.adj)

-- Get the incoming edges to vertex v in graph g.
let digraphEdgesTo : all v. v -> Digraph v -> [DigraphEdge v] =
  lam v. lam g.
  let allEdges = digraphEdges g in
  filter (lam tup : DigraphEdge v. eqi (digraphCmpv g v tup.1) 0) allEdges


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

-- Check whether g has edge e.
let digraphHasEdge : all v. DigraphEdge v -> Digraph v -> Bool =
  lam e. lam g.
  match e with (from, to) in
  match mapLookup from g.adj with Some edgesFrom then
    any (lam t : v.
      eqi 0 (digraphCmpv g t to)) edgesFrom
  else false

-- Check whether graph g has all the edges in es.
let digraphHasEdges = lam es. lam g.
  forAll (lam e. digraphHasEdge e g) es

-- Get successor nodes of v.
let digraphSuccessors : all v. v -> Digraph v -> (v -> Bool) -> [v] = lam v. lam g. lam p.
  let outgoing = digraphEdgesFrom v g in
  let successors = map (lam t : DigraphEdge v. t.1) outgoing in
  setToSeq (setOfSeq (digraphCmpv g) successors)

-- Get predecessor nodes of v.
let digraphPredeccessors : all v. v -> Digraph v -> [v] = lam v. lam g.
  distinct (lam v1. lam v2. eqi (digraphCmpv g v1 v2) 0)
    (map (lam tup : DigraphEdge v. tup.0) (digraphEdgesTo v g))


-- Add vertex v to graph g if it doesn't already exist in g.
-- If v exists in g and check is true, an error is thrown.
-- If v exist in g and check is false, g stays unchanged.
let digraphAddVertexCheck : all v. v -> Digraph v -> Digraph v =
  lam v. lam g.
  {g with adj = mapInsert v [] g.adj}

-- Add a vertex to graph g. Throws an error if v already exists in g.
let digraphAddVertex = lam v. lam g.
  digraphAddVertexCheck v g


-- Add a vertex v to g. Updates the vertex v in graph g if v already exists in g.
let digraphAddUpdateVertex : all v. v -> Digraph v -> Digraph v =
  lam v. lam g.
  let edgeList = mapLookupOrElse (lam. error "Lookup failed") v g.adj in
  let m = mapRemove v g.adj in
  let m = foldl (lam acc. lam v2.
          let edgeLst = mapLookupOrElse (lam. error "Lookup failed") v2 acc in
          let newEdgeLst = map (lam e:v. if digraphEqv g v e then v else e) edgeLst in
          mapInsert v2 newEdgeLst acc) m (mapKeys m) in
  {g with adj = mapInsert v edgeList m}


-- Add edge e=(v1,v2,l) to g. Checks invariants iff utests are enabled.
let digraphAddEdge : all v. v -> v -> Digraph v -> Digraph v =
  lam v1. lam v2. lam g.
  let oldEdgeList =
    mapLookupOrElse (lam. error "Vertex not found") v1 g.adj
  in
  {g with adj = mapInsert v1 (snoc oldEdgeList v2) g.adj}


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
  utest (digraphHasEdge (from, to) g) with true in
  let outgoing = mapFindExn from g.adj in
  let newOutgoing = filter (lam o : v. (not ((digraphEqv g) o to))) outgoing in
  {g with adj = mapInsert from newOutgoing g.adj}


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


lang DelayedGraph 

  syn Vertex =
  | RandomVarV {ident:Int,
                state:Int}
                -- 0: initialized
                -- 1: marginalized
                -- 2: realized


  sem cmprVertex: Vertex -> Vertex -> Int
  sem cmprVertex v1 =
  | v2 -> cmprVertexH (v1,v2)

  sem cmprVertexH: (Vertex,Vertex) -> Int
  sem cmprVertexH =
  | (RandomVarV v1, RandomVarV v2) ->  (subi v1.ident v2.ident)
end
  mexpr
use DelayedGraph in


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

()

