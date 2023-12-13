include "digraph.mc"
include "mexpr/ast.mc"
include "../runtime-dists.mc"
type Label = Int
let debug = false

lang DelayedGraph = MExprAst + RuntimeDistElementary

  sem debugPrint =
  | s -> if debug then print s else ()

  type DelayedGraph = Ref (Digraph Vertex Label)--,m:Ref (Map Name Vertex)}
  syn Vertex =
  | RandomVarV {ident:Name,
          dist:all a. DsDist a,
          margDist:all a. Option (DsDist a),
          value:all a. Option a,
          state:Int}
          -- 0: initialized
          -- 1: marginalized
          -- 2: realized

  -- a parameter can be either float, int or randomvar, how about categorical?
  syn Param =
  | FloatNum Float
  | IntNum Int
  | SeqFParam [Float]
  | RandomVar Vertex

  -- TODO(gizem) add other dists
  syn DsDist a =
  | DsDistBernoulli {p : Param}
  | DsDistBeta  {a : Param, b : Param}
  | DsDistGaussian {mu : Param, sigma : Param}
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
  | (RandomVarV v1, RandomVarV v2) -> nameCmp v1.ident v2.ident
  | (t1,t2) -> subi (constructorTag t1) (constructorTag t2)

  sem addVertex g =
  | v ->
      -- add the vertex to the graph
      modref g (digraphAddVertex v (deref g));
      -- add the dependencies
      addDependencies g v

  sem getVertex g =
  | RandomVarV t ->
    get (filter (lam x. match x with RandomVarV x in nameEq t.ident x.ident) (digraphVertices (deref g))) 0

  sem getMargDist g =
  | RandomVarV t -> match t.margDist with Some mDist in mDist

  sem createVertex =
  | d -> RandomVarV {ident=nameSym "",state=0, dist=unsafeCoerce d,value=unsafeCoerce (None ()),margDist=unsafeCoerce (None ())}

  sem createObsVertex d =
  | value -> RandomVarV {ident=nameSym "",state=0, dist=unsafeCoerce d,value=unsafeCoerce (Some value),margDist=unsafeCoerce (None ())}

  sem addDependencies g =
  | (RandomVarV v) & t ->
    iter (lam p.
      match p with RandomVar f then
        -- be careful may cause problems?
        --let f = getVertex g f in
        match f with RandomVarV p in
        (if neqi p.state 2 then
        addEdge f t g else ()) else ()) (getParams v.dist)

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

  sem addEdge a b =
  | g -> modref g (digraphAddEdge a b 0 (deref g))

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
  | _ -> "no dist"

  sem v2str: Vertex -> String
  sem v2str =
  | RandomVarV n -> let id = n.ident in
    let margDist = match n.margDist with Some d then d2str d else "no" in
    join ["RV Node ", id.0, int2string (sym2hash id.1), " margDist " ,margDist,"state: ", int2string n.state,"\n"]

  sem printGraph: DelayedGraph -> ()
  sem printGraph =
  | g -> print "\nPrint graph:";iter (lam v. print (v2str v)) (digraphVertices (deref g)); print "\n";digraphPrintDot (deref g) v2str int2string
end

lang DelayedSampling = DelayedGraph

  sem getValue: all a. Vertex -> a
  sem getValue =
  | RandomVarV n ->
    match n.value with Some value then value
    else error "DelayedSampling:Random variable is not realized."

  sem value: all a. (Dist a -> a) -> DelayedGraph -> Param -> a
  sem value sampleT g =
  | RandomVar v ->
    let v = getVertex g v in
    let v = valueDs sampleT g v in
    getValue v
  | FloatNum v -> unsafeCoerce v
  | IntNum v -> unsafeCoerce v
  | SeqFParam v -> unsafeCoerce v

  sem valueDs: all a. (Dist a -> a) -> DelayedGraph -> Vertex -> Vertex
  sem valueDs sampleT g =
  | (RandomVarV v) & t ->
      if eqi v.state 2 then t else
      let v = graft (unsafeCoerce sampleT) g t in
      sampleDs (unsafeCoerce sampleT) g v

  sem sampleDs: all a. (Dist a -> a) -> DelayedGraph -> Vertex -> Vertex
  sem sampleDs sampleT g =
  | (RandomVarV n)&t  ->
    --debugPrint (join ["sampling: ", (v2str t),"\n"]);
    let isObserved = match n.value with Some _ then true else false in
    let v =
      if isObserved then t
      else
        match n.margDist with Some margDist in
        let sampledV = sampleT (transformDsDist sampleT g margDist) in
        let updatedV = RandomVarV {n with value = unsafeCoerce (Some sampledV)} in
        modref g (digraphAddUpdateVertex updatedV (deref g)); updatedV
    in
    realize (unsafeCoerce sampleT)  g v

  sem isTerminal g =
  | (RandomVarV v) & t ->
    if eqi v.state 1 then
      (let children = filter (lam u. match u with RandomVarV u in eqi u.state 1) (digraphSuccessors t (deref g)) in
      (if null children then true else false))
    else false

  sem graft:  all a. (Dist a -> a) -> DelayedGraph -> Vertex -> Vertex
  sem graft sampleT g =
  | (RandomVarV v)&t ->
    --debugPrint (join ["grafting: ", (v2str t),"\n"]);
    if eqi v.state 1 then -- if v is marginalized
      (let children = filter (lam u. match u with RandomVarV u in eqi u.state 1) (digraphSuccessors t (deref g)) in
      if null children then t else
      if gti (length children) 1 then error "Cannot have more than one marginalized child"
      else -- if it has a marginalized child, prune the child
        let child = get children 0 in
        --debugPrint (join ["has marg child: ", (v2str child),"\n"]);
        prune (unsafeCoerce sampleT)  g child)
    else -- if v is not marginalized
      --print "it is not marginalized\n";
      let parents = (digraphPredeccessors t (deref g)) in
      if null parents then marginalize (unsafeCoerce sampleT) g t -- if no parents, directly marginalize
      else
        -- if has many parent sample the others
        --print "has parent need to graft them first\n";
        --iter (lam p. valueDs sampleT g p) (tail parents);
        let parent = get parents 0 in
        graft (unsafeCoerce sampleT)  g parent;
        marginalize (unsafeCoerce sampleT) g t

  sem prune:  all a. (Dist a -> a) -> DelayedGraph -> Vertex -> Vertex
  sem prune sampleT g =
  | (RandomVarV v)&t ->
    --debugPrint (join ["pruning: ", (v2str t),"\n"]);
    if neqi v.state 1 then error "Prune: rv should be marginalized" else
    let children = filter (lam u. match u with RandomVarV u in eqi u.state 1)
    (digraphSuccessors t (deref g)) in
    (if gti (length children) 1 then error "Cannot have more than one marginalized child"
    else -- if it has a marginalized child, prune the child
      let child = get children 0 in
      prune (unsafeCoerce sampleT) g child);
    sampleDs (unsafeCoerce sampleT) g t

  sem unwrap:all a. Param -> a
  sem unwrap =
  | FloatNum f -> unsafeCoerce f
  | IntNum i -> unsafeCoerce i

  -- to marginalize
  sem posteriorPredictive =
  | (DsDistBeta p, DsDistBernoulli l) ->
    let a = unwrap p.a in
    let b = unwrap p.b in
    let pp = divf a (addf a b) in
    Some (DsDistBernoulli {l with p = FloatNum pp})
  | (DsDistGaussian p, DsDistGaussian l) ->
    let mu0 = unwrap p.mu in
    let s0 = unwrap p.sigma in
    let s = unwrap l.sigma in
    let s2 = mulf s s in
    let s02 = mulf s0 s0 in
    let ppM = mulf s02 (divf mu0 s02) in
    let ppS = externalSqrt (addf s02 s2) in
    Some (DsDistGaussian {{l with mu = FloatNum ppM} with sigma= FloatNum ppS})
  | (DsDistGamma p, DsDistExponential l) ->
    let shape = unwrap p.shape in
    let scale = unwrap p.scale in
    let pScale = divf 1. scale in
    --Some (DsDistExponential l)
    Some (DsDistLomax {scale = FloatNum pScale, shape = FloatNum shape})
  | (_,_) -> None ()

  -- TODO 
  -- to condition
  sem posterior: all a1. all a. a -> (DsDist a1, DsDist a) -> Option (DsDist a1)
  sem posterior obs =
  | (DsDistBeta p, DsDistBernoulli l) ->
    let a = unwrap p.a in
    let b = unwrap p.b in
    let pAB = if unsafeCoerce obs then (addf a 1., b) else (a, addf b 1.) in
    Some (DsDistBeta {a=FloatNum pAB.0,b=FloatNum pAB.1})
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
    Some (DsDistGaussian {mu=FloatNum pMu, sigma= FloatNum pSigma})
  | (DsDistGamma p, DsDistExponential l) ->
    let shape = unwrap p.shape in
    let scale = unwrap p.scale in
    let pSh = addf shape 1. in
    let pSc = addf 1. (mulf (unsafeCoerce obs) scale) in
    let pSc = divf scale pSc in
    Some (DsDistGamma {shape = FloatNum pSh, scale = FloatNum pSc})
  | _ -> None () --neverr
  
  sem realize:  all a. (Dist a -> a) -> DelayedGraph -> Vertex -> Vertex
  sem realize sampleT g =
  | (RandomVarV v)&t ->
    --debugPrint (join ["realizing: ", (v2str t),"\n"]);
    let parents = (digraphPredeccessors t (deref g)) in
    let updatedV = RandomVarV {v with state=2} in
    modref g (digraphAddUpdateVertex updatedV (deref g));
    let v = (if null parents then
    --debugPrint (join ["with noparent: ","\n"]);
      t else
     if gti (length parents) 1 then error "too many parents" else
      let parent = get parents 0 in
      --debugPrint (join ["with parent: ", (v2str parent),"\n"]);
      match parent with RandomVarV p in
      match p.margDist with Some mDist in
      let ppDist = posterior (getValue t) (mDist, v.dist) in
      let updatedP = RandomVarV {p with margDist=unsafeCoerce ppDist} in
      modref g (digraphAddUpdateVertex updatedP (deref g));
      removeEdge updatedP updatedV g;
      updatedV
    ) in
    let children = digraphSuccessors v (deref g) in
    iter (lam u.
      let u = marginalize (unsafeCoerce sampleT) g u in
      removeEdge v u g) children;v

  sem removeEdge from to =
  | g -> modref g (digraphRemoveEdge from to 0 (deref g))

  sem marginalize sampleT g =
  | (RandomVarV v)&t ->
   --debugPrint (join ["marginalizing: ", (v2str t),"\n"]);
    let parents = filter (lam p. isTerminal g p) (digraphPredeccessors t (deref g)) in
    let updatedV =
      if null parents then
        --debugPrint (join ["with noparent: ","\n"]);
        RandomVarV {{v with state=1} with margDist = unsafeCoerce (Some v.dist)}
      else
        let parent = get parents 0 in
        match parent with RandomVarV p in
        match p.margDist with Some pDist in
        let mDist = posteriorPredictive (pDist, v.dist) in
        let mDist = match mDist with None () then
          valueDs (unsafeCoerce sampleT) g parent;
          Some v.dist
        else
          mDist in
        RandomVarV {{v with state=1} with margDist = unsafeCoerce mDist}
    in
    modref g (digraphAddUpdateVertex updatedV (deref g)); updatedV--;printGraph g

  sem transformDsDist sampleT g =
  | DsDistBernoulli t -> DistBernoulli {p = unsafeCoerce (value (unsafeCoerce sampleT) g t.p)}
  | DsDistBeta t -> DistBeta {a = unsafeCoerce (value sampleT g t.a), b = unsafeCoerce (value (unsafeCoerce sampleT)  g t.b)}
  | DsDistGaussian t -> DistGaussian {mu = unsafeCoerce (value sampleT g t.mu), sigma = unsafeCoerce (value (unsafeCoerce sampleT)  g t.sigma)}
  | DsDistCategorical t -> DistCategorical { p = unsafeCoerce (value (unsafeCoerce sampleT) g t.p)}
  | DsDistPoisson t -> DistPoisson {lambda = unsafeCoerce (value (unsafeCoerce sampleT)  g t.lambda)}
  | DsDistBinomial t -> DistBinomial {n = unsafeCoerce (value (unsafeCoerce sampleT) g t.n), p = unsafeCoerce (value (unsafeCoerce sampleT) g t.p)}
  | DsDistUniform t -> DistUniform {a = unsafeCoerce (value (unsafeCoerce sampleT) g t.a), b =unsafeCoerce (value (unsafeCoerce sampleT) g t.b)}
  | DsDistGamma t -> DistGamma {shape = unsafeCoerce (value (unsafeCoerce sampleT) g t.shape), scale = unsafeCoerce (value (unsafeCoerce sampleT) g t.scale)}
  | DsDistExponential t -> DistExponential {rate = unsafeCoerce (value  (unsafeCoerce sampleT)  g t.rate)}
  | DsDistLomax t -> DistLomax {shape= unsafeCoerce (value (unsafeCoerce sampleT) g t.shape), scale = unsafeCoerce (value (unsafeCoerce sampleT)  g t.scale)}

  | _ -> error "not supported currently."

end

let marginalize = lam a. lam g. lam t.
  use DelayedSampling in
  marginalize a g t

let graft = lam a. lam g. lam t.
  use DelayedSampling in
  graft a g t

let prune = lam a. lam g. lam t.
  use DelayedSampling in
  prune a g t

let getMargDist = lam g. lam v.
  use DelayedSampling in
  getMargDist g v

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

let getVertex = lam g. lam v.
  use DelayedSampling in
  getVertex g v

let addEdge = lam a. lam b. lam g.
  use DelayedSampling in
  addEdge a b g

let addDependencies = lam g. lam v.
  use DelayedSampling in
  addDependencies g v

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

let createVertex = lam d.
  use DelayedSampling in
  createVertex d

let createObsVertex = lam d. lam o.
  use DelayedSampling in
  createObsVertex d o

let addVertex = lam g. lam v.
  use DelayedSampling in
  addVertex g v

let printGraph = lam g.
  use DelayedSampling in
  printGraph g

let runD = lam model.
  use DelayedSampling in
  (lam c. lam s. 
  let emptyG = ref (digraphEmpty cmprVertex eqi) in
  --let emptyM = ref (mapEmpty nameCmp) in
  model emptyG c s)
