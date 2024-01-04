include "delayed-graph-mapparents.mc"
include "mexpr/ast.mc"
include "../runtime-dists.mc"

let debug = true
type Label = Int
lang DelayedGraph = MExprAst + RuntimeDistElementary

  sem debugPrint =
  | s -> if debug then print s else ()

  type DelayedGraph = Ref (Digraph Vertex)
  syn Vertex =
  | RandomVarV {ident:Int,
                dist:all a. DsDist a,
                margDist:all a. Ref (Option (DsDist a)),
                value:all a. Ref (Option a),
                state:Ref Int}
                -- 0: initialized
                -- 1: marginalized
                -- 2: realized

  -- a parameter can be either float, int, random variable or sequence of floats
  syn Param =
  | FloatParam Float
  | IntParam Int
  | SeqFParam [Float]
  | RandomParam Vertex

  -- delayed distributions where parameters are not sampled directly
  syn DsDist a =
  | DsDistBernoulli {p : Param}
  | DsDistBeta  {a : Param, b : Param}
  | DsDistGaussian {mu : Param, sigma : Param}
  | DsDistMultinomial {n : Param, p : Param}
  | DsDistDirichlet {a: Param}
  | DsDistCategorical {p : Param}
  | DsDistPoisson {lambda : Param}
  | DsDistBinomial {n : Param, p : Param}
  | DsDistUniform {a : Param, b : Param}
  | DsDistGamma {shape : Param, scale : Param}
  | DsDistExponential {rate : Param}
  | DsDistLomax {scale : Param, shape : Param}

  sem cmprVertex: Vertex -> Vertex -> Int
  sem cmprVertex v1 =
  | v2 -> cmprVertexH (v1,v2)

  sem cmprVertexH: (Vertex,Vertex) -> Int
  sem cmprVertexH =
  | (RandomVarV v1, RandomVarV v2) ->  (subi v1.ident v2.ident)

  -- clear the graph
  sem resetGraph =
  | g ->
    let emptyG = (digraphEmpty cmprVertex) in
    modref g emptyG

  sem addVertex g =
  | v ->
    -- add the vertex to the graph
    let gg = (digraphAddVertex v (deref g)) in
    let edges = findDependencies v in
    -- add the dependencies
    modref g (digraphAddEdges edges gg)

  sem findDependencies =
  | (RandomVarV v) & t ->
    foldl (lam edges. lam p.
      match p with RandomParam f then
        match f with RandomVarV p in
        (if neqi (deref p.state) 2 then -- if the parent is already realized no need to add an edge
          cons (f,t) edges else edges)
      else edges) [] (getParams v.dist)

  sem getMargDist =
  | RandomVarV t -> match deref t.margDist with Some mDist in mDist

  sem createVertex g =
  | d ->
    RandomVarV {ident=digraphCountVertices (deref g),state=ref 0, dist=unsafeCoerce d,value=unsafeCoerce (ref (None ())),margDist=unsafeCoerce (ref (None ()))}

  sem createObsVertex g d =
  | value ->
    RandomVarV {ident=digraphCountVertices (deref g),state=ref 0, dist=unsafeCoerce d,value=unsafeCoerce (ref (Some value)),margDist=unsafeCoerce (ref (None ()))}

  sem getParams =
  | DsDistBernoulli d -> [d.p]
  | DsDistBeta d -> [d.a,d.b]
  | DsDistGaussian d -> [d.mu, d.sigma]
  | DsDistCategorical d -> [d.p]
  | DsDistPoisson d -> [d.lambda]
  | DsDistBinomial d -> [d.n,d.p]
  | DsDistUniform d -> [d.a,d.b]
  | DsDistGamma d -> [d.shape,d.scale]
  | DsDistExponential d -> [d.rate]
  | DsDistLomax d -> [d.scale, d.shape]
  | DsDistDirichlet d -> [d.a]
  | DsDistMultinomial d -> [d.n, d.p]
  | _ -> error "getParams: distribution is not supported"

  sem d2str =
  | DsDistBernoulli d -> "DsDistBernoulli"
  | DsDistBeta d -> "DsDistBeta"
  | DsDistGaussian d -> "DsDistGaussian"
  | DsDistCategorical d -> "DsDistCategorical"
  | DsDistPoisson d -> "DsDistPoisson"
  | DsDistBinomial d -> "DsDistBinomial"
  | DsDistUniform d -> "DsDistUniform"
  | DsDistGamma d -> "DsDistGamma"
  | DsDistExponential d -> "DsDistExponential"
  | DsDistLomax d -> "DsDistLomax"
  | DsDistDirichlet d -> "DsDistDirichlet"
  | DsDistMultinomial d -> "DsDistMultinomial"
  | _ -> error "d2str: distribution is not supported"

  sem v2str: Vertex -> String
  sem v2str =
  | RandomVarV n -> let id = n.ident in
    let margDist = match deref n.margDist with Some d then d2str d else "no" in
    join ["RV Node ", int2string id, " margDist " ,margDist,"state: ", int2string (deref n.state),"\n"]

  sem printGraph: DelayedGraph -> ()
  sem printGraph =
  | g -> print "\nPrint graph:";iter (lam v. print (v2str v)) (digraphVertices (deref g));print "\n";digraphPrintDot (deref g) v2str int2string
end

lang DelayedSampling = DelayedGraph

  sem getValue: all a. Vertex -> a
  sem getValue =
  | RandomVarV n ->
    match deref n.value with Some value then value
    else error "DelayedSampling:Random variable is not realized."

  sem value: all a. (Dist a -> a) -> DelayedGraph -> Param -> a
  sem value sampleT g =
  | RandomParam v ->
    valueDs sampleT g v;
    getValue v
  | FloatParam v -> unsafeCoerce v
  | IntParam v -> unsafeCoerce v
  | SeqFParam v -> unsafeCoerce v

  -- graft(v) -> sample(v)
  sem valueDs: all a. (Dist a -> a) -> DelayedGraph -> Vertex -> ()
  sem valueDs sampleT g =
  | (RandomVarV v) & t ->
      if eqi (deref v.state) 2 then () else
      graft sampleT g t;
      sampleDs sampleT g t

  sem sampleDs: all a. (Dist a -> a) -> DelayedGraph -> Vertex -> ()
  sem sampleDs sampleT g =
  | (RandomVarV n)&t  ->
    --debugPrint (join ["sampling: ", (v2str t),"\n"]);
    let nisObserved = match deref n.value with Some _ then false else true in
    (if nisObserved then
      match deref n.margDist with Some margDist in
      let sampledV = sampleT (transformDsDist sampleT g margDist) in
      modref n.value (unsafeCoerce (Some sampledV)) else ());
    realize sampleT  g t

  sem isTerminal g =
  | (RandomVarV v) & t ->
    if eqi (deref v.state) 1 then
      (let children = digraphSuccessors t (deref g) (lam u. match u with RandomVarV u in eqi (deref u.state) 1) in
      (if null children then true else false))
    else false

  sem graft:  all a. (Dist a -> a) -> DelayedGraph -> Vertex -> ()
  sem graft sampleT g =
  | (RandomVarV v)&t ->
    --debugPrint (join ["grafting: ", (v2str t),"\n"]);
    if eqi (deref v.state) 1 then -- if v is marginalized
      (let children = (digraphSuccessors t (deref g) (lam u. match u with RandomVarV u in eqi (deref u.state) 1)) in
      if null children then ()
      else -- if it has a marginalized child, prune the child
        let child = get children 0 in
        --debugPrint (join ["has marg child: ", (v2str child),"\n"]);
        prune sampleT g child)
    else -- if v is not marginalized
      --print "it is not marginalized\n";
      let parents = (digraphPredeccessors t (deref g)) in
      if null parents then marginalize sampleT g t -- if no parents, directly marginalize
      else
        -- if has many parent sample the others
        --print "has parent need to graft them first\n";
        iter (lam p. valueDs sampleT g p) (tail parents);
        let parent = get parents 0 in
        graft sampleT g parent;
        marginalize sampleT g t

  sem prune: all a. (Dist a -> a) -> DelayedGraph -> Vertex -> ()
  sem prune sampleT g =
  | (RandomVarV v)&t ->
    --debugPrint (join ["pruning: ", (v2str t),"\n"]);
    --if neqi (deref v.state) 1 then error "Prune: rv should be marginalized" else
    let children = (digraphSuccessors t (deref g) (lam u. match u with RandomVarV u in eqi (deref u.state) 1)) in
   -- (if gti (length children) 1 then error "Cannot have more than one marginalized child"
   -- else -- if it has a marginalized child, prune the child
      let child = get children 0 in
      prune sampleT g child;
    sampleDs sampleT g t

  sem unwrap:all a. Param -> a
  sem unwrap =
  | RandomParam r -> unsafeCoerce (getValue r)
  | FloatParam f -> unsafeCoerce f
  | IntParam i -> unsafeCoerce i
  | SeqFParam s -> unsafeCoerce s

  -- to marginalize
  sem posteriorPredictive =
  | (DsDistBeta p, DsDistBernoulli l) ->
    let a = unwrap p.a in
    let b = unwrap p.b in
    let pp = divf a (addf a b) in
    Some (DsDistBernoulli {l with p = FloatParam pp})
  | (DsDistGaussian p, DsDistGaussian l) ->
    let mu0 = unwrap p.mu in
    let s0 = unwrap p.sigma in
    let s = unwrap l.sigma in
    let s2 = mulf s s in
    let s02 = mulf s0 s0 in
    let ppM = mulf s02 (divf mu0 s02) in
    let ppS = externalSqrt (addf s02 s2) in
    Some (DsDistGaussian {{l with mu = FloatParam ppM} with sigma= FloatParam ppS})
  | (DsDistGamma p, DsDistExponential l) ->
    let shape = unwrap p.shape in
    let scale = unwrap p.scale in
    let pScale = divf 1. scale in
    Some (DsDistLomax {scale = FloatParam pScale, shape = FloatParam shape})
  | (_,_) -> None ()

  -- TODO 
  -- to condition
  sem posterior: all a1. all a. a -> (DsDist a1, DsDist a) -> Option (DsDist a1)
  sem posterior obs =
  | (DsDistBeta p, DsDistBernoulli l) ->
    let a = unwrap p.a in
    let b = unwrap p.b in
    let pAB = if unsafeCoerce obs then (addf a 1., b) else (a, addf b 1.) in
    Some (DsDistBeta {a=FloatParam pAB.0,b=FloatParam pAB.1})
  | (DsDistGaussian p, DsDistGaussian l) ->
    let mu0 = unwrap p.mu in
    let s0 = unwrap p.sigma in
    let s = unwrap l.sigma in
    let s2 = mulf s s in
    let s02 = mulf s0 s0 in
    let muRHS = addf (divf mu0 s02) (divf (unsafeCoerce obs) s2) in
    let muLHS = divf 1. (addf (divf 1. s02) (divf 1. s2)) in
    let pMu = mulf muRHS muLHS in
    let pSigma = externalSqrt (divf 1. (addf (divf 1. s02) (divf 1. s2))) in
    Some (DsDistGaussian {mu=FloatParam pMu, sigma= FloatParam pSigma})
  | (DsDistGamma p, DsDistExponential l) ->
    let shape = unwrap p.shape in
    let scale = unwrap p.scale in
    let pSh = addf shape 1. in
    let pSc = addf 1. (mulf (unsafeCoerce obs) scale) in
    let pSc = divf scale pSc in
    Some (DsDistGamma {shape = FloatParam pSh, scale = FloatParam pSc})
  | _ -> None () --neverr

  sem realize: all a. (Dist a -> a) -> DelayedGraph -> Vertex -> ()
  sem realize sampleT g =
  | (RandomVarV v)&t ->
    --debugPrint (join ["realizing: ", (v2str t),"\n"]);
    let parents = (digraphPredeccessors t (deref g)) in
    modref v.state 2;
    let v = (if null parents then t
    --debugPrint (join ["with noparent: ","\n"]);
      else
     --if gti (length parents) 1 then error "too many parents" else
      let parent = get parents 0 in
      --debugPrint (join ["with parent: ", (v2str parent),"\n"]);
      match parent with RandomVarV p in
      match deref p.margDist with Some mDist in
      let ppDist = posterior (getValue t) (mDist, v.dist) in
      modref p.margDist (unsafeCoerce ppDist);
      modref g (digraphRemoveEdge parent t (deref g));t) in
    let gg = (deref g) in
    let children = digraphSuccessors v gg (lam. true) in
    let gg = foldl (lam acc. lam u.
      marginalize (sampleT) g u;
      (digraphRemoveEdge v u acc)) gg children in
    modref g gg

  sem marginalize: all a. (Dist a -> a) -> DelayedGraph -> Vertex -> ()
  sem marginalize sampleT g =
  | (RandomVarV v)&t ->
   --debugPrint (join ["marginalizing: ", (v2str t),"\n"]);
    let parents = filter (lam p. isTerminal g p) (digraphPredeccessors t (deref g)) in
      if null parents then
        --debugPrint (join ["with noparent: ","\n"]);
        modref v.state 1;
        modref v.margDist (unsafeCoerce (Some v.dist))
      else
        let parent = get parents 0 in
        match parent with RandomVarV p in
        match deref p.margDist with Some pDist in
        let mDist = posteriorPredictive (pDist, v.dist) in
        let mDist = match mDist with None () then
          valueDs sampleT g parent;Some v.dist
          else mDist in
        modref v.state 1;
        modref v.margDist (unsafeCoerce mDist)

  sem getTDist sampleT g =
  | dist -> transformDsDist sampleT g dist

  sem transformDsDist sampleT g =
  | DsDistBernoulli t -> DistBernoulli {p = value (unsafeCoerce sampleT) g t.p}
  | DsDistBeta t -> DistBeta {a = value (unsafeCoerce sampleT) g t.a, b = value (unsafeCoerce sampleT)  g t.b}
  | DsDistGaussian t -> DistGaussian {mu = value (unsafeCoerce sampleT) g t.mu, sigma = value (unsafeCoerce sampleT)  g t.sigma}
  | DsDistCategorical t -> DistCategorical { p = value (unsafeCoerce sampleT) g t.p}
  | DsDistPoisson t -> DistPoisson {lambda = value (unsafeCoerce sampleT)  g t.lambda}
  | DsDistBinomial t -> DistBinomial {n = value (unsafeCoerce sampleT) g t.n, p = value (unsafeCoerce sampleT) g t.p}
  | DsDistUniform t -> DistUniform {a = value (unsafeCoerce sampleT) g t.a, b = value (unsafeCoerce sampleT) g t.b}
  | DsDistGamma t -> DistGamma {shape = value (unsafeCoerce sampleT) g t.shape, scale =  value (unsafeCoerce sampleT) g t.scale}
  | DsDistExponential t -> DistExponential {rate = value  (unsafeCoerce sampleT)  g t.rate}
  | DsDistLomax t -> DistLomax {shape = value (unsafeCoerce sampleT) g t.shape, scale = value (unsafeCoerce sampleT)  g t.scale}
  | _ -> error "not supported currently."

end

let getTDist = lam a. lam g. lam d.
  use DelayedSampling in
  getTDist a g d

let marginalize = lam a. lam g. lam t.
  use DelayedSampling in
  marginalize a g t

let graft = lam a. lam g. lam t.
  use DelayedSampling in
  graft a g t

let prune = lam a. lam g. lam t.
  use DelayedSampling in
  prune a g t

let getMargDist = lam v.
  use DelayedSampling in
  getMargDist v

let sampleDs = lam a. lam g. lam t.
  use DelayedSampling in
  sampleDs a g t

let valueDs = lam a. lam g. lam t.
  use DelayedSampling in
  valueDs a g t

let realize = lam a. lam g. lam t.
  use DelayedSampling in
  realize a g t

let unwrap = lam p.
  use DelayedSampling in
  unwrap p

let posteriorPredictive = lam r.
  use DelayedSampling in
  posteriorPredictive r

let posterior = lam o. lam r.
  use DelayedSampling in
  posterior o r

let v2str = lam v.
  use DelayedSampling in
  v2str v

let getParams = lam d.
  use DelayedSampling in
  getParams d

let findDependencies = lam v.
  use DelayedSampling in
  findDependencies v

let getValue = lam v.
  use DelayedSampling in
  getValue v

let value = lam a. lam g. lam v.
  use DelayedSampling in
  value a g v

let transformDsDist = lam a. lam g. lam d.
  use DelayedSampling in
  transformDsDist a g d

let cmprVertex = lam v1. lam v2.
  use DelayedSampling in
  cmprVertex v1 v2

let resetGraph = lam g.
  use DelayedSampling in
  resetGraph g

let createVertex = lam g. lam d.
  use DelayedSampling in
  createVertex g d

let createObsVertex = lam g. lam d. lam o.
  use DelayedSampling in
  createObsVertex g d o

let addVertex = lam g. lam v.
  use DelayedSampling in
  addVertex g v

let printGraph = lam g.
  use DelayedSampling in
  printGraph g

let runSequential = lam model.
  use DelayedSampling in
  let emptyR = ref (digraphEmpty cmprVertex) in
  model emptyR

let runParallel = lam model.
  use DelayedSampling in
  (lam c. lam s.
  let emptyR = ref (digraphEmpty cmprVertex) in
   model emptyR c s)
