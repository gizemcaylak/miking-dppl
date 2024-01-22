include "mexpr/ast.mc"
include "../runtime-dists.mc"

--let debug = false
lang DelayedGraph = MExprAst + RuntimeDistElementary
  /-sem debugPrint =
  | s -> if debug then print s else ()-/
  syn Vertex =
  | RandomVarV { dist:all a. DsDist a,
                margDist:all a. Ref (Option (DsDist a)),
                value:all a. Ref (Option a),
                state:Ref Int,
                next:Ref (Option Vertex),
                terminal:Ref Bool}
                -- 0: initialized
                -- 1: marginalized
                -- 2: realized

  -- a parameter can be either float, int, random variable or sequence of floats
  syn Param =
  | FloatParam Float
  | IntParam Int
  | SeqFParam [Float]
  | RandomParam Vertex
  | AffineParam {aV: Param, meanScale : Float, meanOffset: Float}

  -- delayed distributions where parameters are not sampled directly
  syn DsDist a =
  | DsDistBernoulli {p : Param}
  | DsDistBeta  {a : Param, b : Param}
  | DsDistGaussian {mu : Param, sigma : Param, meanScale : Float, meanOffset : Float}
  | DsDistMultinomial {n : Param, p : Param}
  | DsDistDirichlet {a: Param}
  | DsDistCategorical {p : Param}
  | DsDistPoisson {lambda : Param}
  | DsDistBinomial {n : Param, p : Param}
  | DsDistUniform {a : Param, b : Param}
  | DsDistGamma {shape : Param, scale : Param}
  | DsDistExponential {rate : Param}
  | DsDistLomax {scale : Param, shape : Param}

  sem getParentsH  =
  | RandomParam v -> Some v
  | AffineParam v -> match v.aV with RandomParam v in Some v
  | _ -> None ()

  sem getParams =
  | DsDistBernoulli d -> [d.p]
  | DsDistBeta d -> [d.a,d.b]
  | DsDistGaussian d -> [d.mu,d.sigma]
  | DsDistMultinomial d -> [d.n,d.p]
  | DsDistDirichlet d -> [d.a]
  | DsDistCategorical d -> [d.p]
  | DsDistPoisson d -> [d.lambda]
  | DsDistBinomial d -> [d.n,d.p]
  | DsDistUniform d -> [d.a,d.b]
  | DsDistGamma d -> [d.shape,d.scale]
  | DsDistExponential d -> [d.rate]
  | DsDistLomax d -> [d.scale,d.shape]
  | _ -> never

  sem getParents =
  | t -> let params = getParams t in
    foldl (lam acc. lam p. match getParentsH p with Some v then cons v acc else acc) [] (reverse params)

  sem getMargDist =
  | RandomVarV t -> match deref t.margDist with Some mDist in mDist

  sem createVertex =
  | d ->
    RandomVarV {state=ref 0, dist=unsafeCoerce d,value=unsafeCoerce (ref (None ())),margDist=unsafeCoerce (ref (None ())),terminal=ref false,next=ref (None ())}

  sem createObsVertex d =
  | value ->
    RandomVarV {state=ref 0, dist=unsafeCoerce d,value=unsafeCoerce (ref (Some value)),margDist=unsafeCoerce (ref (None ())),terminal=ref false,next=ref (None ())}

  sem d2str =
  | DsDistBernoulli d -> "DsDistBernoulli"
  | DsDistBeta d -> "DsDistBeta"
  | DsDistGaussian d ->  "DsDistGaussian"
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
  | RandomVarV n -> 
    let margDist = match deref n.margDist with Some d then d2str d else "no" in
    join ["RV Node ","dist ", d2str n.dist, " margDist " ,margDist,"state: ", int2string (deref n.state),"\n"]
 end

lang DelayedSampling = DelayedGraph

  sem getValue: all a. Vertex -> a
  sem getValue =
  | RandomVarV n ->
    match deref n.value with Some value then value
    else error "DelayedSampling:Random variable is not realized."

  sem value: all a. (Dist a -> a) -> Param -> a
  sem value sampleT =
  | RandomParam v ->
    valueDs sampleT v;
    getValue v
  | AffineParam v -> unsafeCoerce (addf (mulf (unsafeCoerce (value sampleT v.aV)) v.meanScale) v.meanOffset)
  | FloatParam v -> unsafeCoerce v
  | IntParam v -> unsafeCoerce v
  | SeqFParam v -> unsafeCoerce v

  sem valueDs: all a. (Dist a -> a) -> Vertex -> ()
  sem valueDs sampleT =
  | (RandomVarV v) & t ->
      if eqi (deref v.state) 2 then () else
      graft sampleT t;
      sampleDs sampleT t

  sem sampleDs: all a. (Dist a -> a) -> Vertex -> ()
  sem sampleDs sampleT =
  | (RandomVarV n)&t  ->
    --debugPrint (join ["sampling: ", (v2str t),"\n"]);
    (match deref n.value with None () then
      match deref n.margDist with Some margDist in
      let sampledV = sampleT (transformDsDist sampleT margDist) in
      modref n.value (Some sampledV) else ());
    realize sampleT t

  sem isTerminal =
  | (RandomVarV v) & t -> if eqi (deref v.state) 1 then deref v.terminal else false

  sem graft:  all a. (Dist a -> a) -> Vertex -> ()
  sem graft sampleT =
  | (RandomVarV v)&t ->
    --debugPrint (join ["grafting: ", (v2str t),"\n"]);
    (if eqi (deref v.state) 1 then -- if v is marginalized
      (let child = deref v.next in
      match child with Some child then -- if it has a marginalized child, prune the child
        prune sampleT child
      else ())
    else -- if v is not marginalized
      let parents = filter (lam p. match p with RandomVarV p in neqi (deref p.state) 2) (getParents v.dist) in
      if null parents then marginalize sampleT t -- if no parents, directly marginalize
      else
        let parent = get parents 0 in
        graft sampleT parent;
        marginalize sampleT t);
        modref v.terminal true

  sem marginalize: all a. (Dist a -> a) -> Vertex -> ()
  sem marginalize sampleT =
  | (RandomVarV v)&t ->
   --debugPrint (join ["marginalizing: ", (v2str t),"\n"]);
    let parents = filter (lam p. isTerminal p) (getParents v.dist) in
    --(digraphPredeccessors t (deref g)) in
      if null parents then
        --debugPrint (join ["with noparent: ","\n"]);
        modref v.state 1;
        modref v.margDist (Some v.dist)
      else
        let parent = get parents 0 in
        match parent with RandomVarV p in
        match deref p.margDist with Some pDist in
        let mDist = posteriorPredictive (pDist, v.dist) in
        let mDist = match mDist with None () then
          valueDs sampleT parent;Some v.dist
          else modref p.next (Some t);mDist in
        modref p.terminal false;
        modref v.state 1;
        modref v.margDist mDist

  sem realize: all a. (Dist a -> a) -> Vertex -> ()
  sem realize sampleT =
  | (RandomVarV v)&t ->
    --debugPrint (join ["realizing: ", (v2str t),"\n"]);
    let parents = filter (lam p. match p with RandomVarV p in eqi (deref p.state) 1) (getParents v.dist) in
    --(digraphPredeccessors t (deref g)) in
    modref v.state 2;
    modref v.terminal false;
    if null parents then ()
    else
     --if gti (length parents) 1 then error "too many parents" else
      let parent = get parents 0 in
      --debugPrint (join ["with parent: ", (v2str parent),"\n"]);
      match parent with RandomVarV p in
      match deref p.margDist with Some mDist in
      let ppDist = posterior (getValue t) (mDist, v.dist) in
      modref p.margDist ppDist;
      modref p.next (None ())

  sem prune: all a. (Dist a -> a) -> Vertex -> ()
  sem prune sampleT =
  | (RandomVarV v)&t ->
      let child = deref v.next in
      (match child with Some child then
        prune sampleT child
      else ());
      sampleDs sampleT t

  sem unwrap:all a. Param -> a
  sem unwrap =
  | RandomParam r -> unsafeCoerce (getValue r)
  | FloatParam f -> unsafeCoerce f
  | IntParam i -> unsafeCoerce i
  | SeqFParam s -> unsafeCoerce s

  -- TODO : Multinomial Dirichlet
  --  Categorical Dirichlet
  -- to marginalize
  sem posteriorPredictive =
  | (DsDistBeta p, DsDistBernoulli l) ->
    let a = unwrap p.a in
    let b = unwrap p.b in
    let pp = divf a (addf a b) in
    Some (DsDistBernoulli {l with p = FloatParam pp})
  | (DsDistGaussian p, DsDistGaussian l) ->
    let mu0 = addf (mulf (unwrap p.mu) l.meanScale) l.meanOffset in
    let s0 = mulf (unwrap p.sigma) (absf l.meanScale) in
    let s = unwrap l.sigma in
    let s2 = mulf s s in
    let s02 = mulf s0 s0 in
    let ppM = mulf s02 (divf mu0 s02) in
    let ppS = externalSqrt (addf s02 s2) in
    Some (DsDistGaussian {mu = FloatParam ppM, sigma= FloatParam ppS,meanScale=1.,meanOffset=0.})
  | (DsDistGamma p, DsDistExponential l) ->
    let shape = unwrap p.shape in
    let scale = unwrap p.scale in
    let pScale = divf 1. scale in
    Some (DsDistLomax {scale = FloatParam pScale, shape = FloatParam shape})
  | (_,_) -> None ()

  -- TODO 
  -- Multinomial Dirichlet
  --  Categorical Dirichlet
  -- to condition
  sem posterior: all a1. all a. a -> (DsDist a1, DsDist a) -> Option (DsDist a1)
  sem posterior obs =
  | (DsDistBeta p, DsDistBernoulli l) ->
    let a = unwrap p.a in
    let b = unwrap p.b in
    let pAB = if unsafeCoerce obs then (addf a 1., b) else (a, addf b 1.) in
    Some (DsDistBeta {a=FloatParam pAB.0,b=FloatParam pAB.1})
  | (DsDistGaussian p, DsDistGaussian l) ->
    let mu0 = addf (mulf (unwrap p.mu) l.meanScale) l.meanOffset in
    let s0 = mulf (unwrap p.sigma) (absf l.meanScale) in
    let s = unwrap l.sigma in
    let s2 = mulf s s in
    let s02 = mulf s0 s0 in
    let muRHS = addf (divf mu0 s02) (divf (unsafeCoerce obs) s2) in
    let muLHS = divf 1. (addf (divf 1. s02) (divf 1. s2)) in
    let pMu = subf (divf (mulf muRHS muLHS) l.meanScale) l.meanOffset in
    let pSigma = divf (externalSqrt (muLHS)) (absf l.meanScale) in
    Some (DsDistGaussian {mu=FloatParam pMu, sigma= FloatParam pSigma, meanScale=1., meanOffset=0.})
  | (DsDistGamma p, DsDistExponential l) ->
    let shape = unwrap p.shape in
    let scale = unwrap p.scale in
    let pSh = addf shape 1. in
    let pSc = addf 1. (mulf (unsafeCoerce obs) scale) in
    let pSc = divf scale pSc in
    Some (DsDistGamma {shape = FloatParam pSh, scale = FloatParam pSc})
  | _ -> None () --neverr


  -- TODO add the scale factors for Gaussian
  sem transformDsDist sampleT =
  | DsDistBernoulli t -> DistBernoulli {p = value (unsafeCoerce sampleT) t.p}
  | DsDistBeta t -> DistBeta {a = value (unsafeCoerce sampleT) t.a, b = value (unsafeCoerce sampleT) t.b}
  | DsDistGaussian t -> DistGaussian {mu = addf t.meanOffset (value (unsafeCoerce sampleT) t.mu), sigma = value (unsafeCoerce sampleT)  t.sigma}
  | DsDistCategorical t -> DistCategorical { p = value (unsafeCoerce sampleT) t.p}
  | DsDistPoisson t -> DistPoisson {lambda = value (unsafeCoerce sampleT)  t.lambda}
  | DsDistBinomial t -> DistBinomial {n = value (unsafeCoerce sampleT) t.n, p = value (unsafeCoerce sampleT) t.p}
  | DsDistUniform t -> DistUniform {a = value (unsafeCoerce sampleT) t.a, b = value (unsafeCoerce sampleT) t.b}
  | DsDistGamma t -> DistGamma {shape = value (unsafeCoerce sampleT) t.shape, scale =  value (unsafeCoerce sampleT) t.scale}
  | DsDistExponential t -> DistExponential {rate = value  (unsafeCoerce sampleT)  t.rate}
  | DsDistLomax t -> DistLomax {shape = value (unsafeCoerce sampleT) t.shape, scale = value (unsafeCoerce sampleT) t.scale}
  | DsDistDirichlet t -> DistDirichlet {a = value (unsafeCoerce sampleT) t.a}
  | DsDistMultinomial t -> DistMultinomial {n = value (unsafeCoerce sampleT) t.n, p = value (unsafeCoerce sampleT) t.p}
  | _ -> error "not supported currently."

end

let marginalize = lam a. lam t.
  use DelayedSampling in
  marginalize a t

let graft = lam a. lam t.
  use DelayedSampling in
  graft a t

let prune = lam a. lam t.
  use DelayedSampling in
  prune a t

let getMargDist = lam v.
  use DelayedSampling in
  getMargDist v

let sampleDs = lam a. lam t.
  use DelayedSampling in
  sampleDs a t

let valueDs = lam a. lam t.
  use DelayedSampling in
  valueDs a t

let realize = lam a. lam t.
  use DelayedSampling in
  realize a t

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

let getValue = lam v.
  use DelayedSampling in
  getValue v

let value = lam a. lam v.
  use DelayedSampling in
  value a v

let transformDsDist = lam a. lam d.
  use DelayedSampling in
  transformDsDist a d

let createVertex = lam d.
  use DelayedSampling in
  createVertex d

let createObsVertex = lam d. lam o.
  use DelayedSampling in
  createObsVertex d o


