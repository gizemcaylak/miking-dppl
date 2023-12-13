lang MExprPPLDsANF = MExprPPL + MExprANFAll
  -- specialized normalize for assume and observe
  sem normalize (k:Expr -> Expr) =
  | TmAssume ({ dist = TmDist ({ dist = dist } & td) } & t) ->
    normalizeDist
      (lam dist. k (TmAssume { t with dist = TmDist { td with dist = dist } }))
      dist
  | TmObserve ({ value = value, dist = TmDist ({ dist = dist } & td) } & t) ->
    normalizeName
      (lam value.
        normalizeDist
          (lam dist.
             k (TmObserve {{ t with value = value }
                               with dist = TmDist { td with dist = dist}}))
          dist)
      value
 end

lang TransformDsDist = TransformDist + DPPLParser

  syn EnvParam =
  | FloatParam ()
  | IntParam ()
  | RandomParam ()
  | SeqFParam ()

 /-
  -- If an observe or assume term is encountered, set the type as RandomParam;otherwise,
  -- Depending on if it is float or integer set it as FloatParam, IntParam, SeqFParam respectively
  -/
  sem createEnvParam: Map Name EnvParam -> Expr -> Map Name EnvParam
  sem createEnvParam env =
  | TmLet ({body = (TmAssume _ | TmObserve _)} & t) ->
    let env = mapInsert t.ident (RandomParam ()) env in
    createEnvParam (createEnvParam env t.body) t.inexpr
  | TmLet t ->
    let env = match tyTm (t.body) with TyFloat _ then
        mapInsert t.ident (FloatParam ()) env
      else match tyTm (t.body) with TyInt _ then
        mapInsert t.ident (IntParam ()) env
      else match tyTm (t.body) with TySeq {ty=TyFloat _,info=_} then
        mapInsert t.ident (SeqFParam ()) env
      else env in
    createEnvParam (createEnvParam env t.body) t.inexpr
  | TmLam t ->
    let env = match t.tyParam with TyFloat _ then
        mapInsert t.ident (FloatParam ()) env
      else match t.tyParam with TyInt _ then
        mapInsert t.ident (IntParam ()) env
      else match t.tyParam with TySeq {ty=TyFloat _,info=_} then
        mapInsert t.ident (SeqFParam ()) env
      else env in
    (createEnvParam env t.body)

  | t -> sfold_Expr_Expr createEnvParam env t

  sem transformDsDistributions env =
  | t ->
    let t = mapPre_Expr_Expr (transformTmDistDs env) t in
    replaceTyDist t

  sem transformTmDistDs: Map Name EnvParam -> Expr -> Expr
  sem transformTmDistDs env =
  | TmDist t -> transformDsDist (withInfo t.info) env t.dist
  | TmConst {val = c &
      ( CDistEmpiricalSamples _
      | CDistEmpiricalDegenerate _
      | CDistEmpiricalNormConst _
      | CDistEmpiricalAcceptRate _
      )
    } -> var_ (getConstStringCode 0 c)
  | t -> t

  sem assignCons: (Map Name EnvParam) -> Expr -> Option Expr
  sem assignCons env =
  | TmVar v ->
    let varType = mapLookup v.ident env in
    match varType with Some varType then
      Some (assignConsH (TmVar v) varType)
    else None ()
  | t -> error "not in ANF-form"

  sem assignConsH t =
  | FloatParam _ -> (conapp_ "DelayedGraph_FloatNum" t)
  | IntParam _ ->  (conapp_ "DelayedGraph_IntNum" t)
  | RandomParam _ -> (conapp_ "DelayedGraph_RandomVar" t)
  | SeqFParam _ -> (conapp_ "DelayedGraph_SeqFParam" t)

  sem transformDsDist: (Expr -> Expr) -> (Map Name EnvParam) -> Dist -> Expr
  sem transformDsDist i env =
  | DBeta {a = a, b = b} ->
    let a = match assignCons env a with Some x then x else (conapp_ "DelayedGraph_FloatNum" a) in
    let b = match assignCons env b with Some x then x else (conapp_ "DelayedGraph_FloatNum" b) in
    i (conapp_ "DelayedGraph_DsDistBeta" (i (urecord_ [("a", a), ("b", b)])))
  | DBernoulli {p = p} ->
    let p = match assignCons env p with Some x then x else (conapp_ "DelayedGraph_FloatNum" p) in
    i (conapp_ "DelayedGraph_DsDistBernoulli" (i (urecord_ [("p", p)])))
  | DGaussian {mu = mu, sigma = sigma} ->
    let mu = match assignCons env mu with Some x then x else (conapp_ "DelayedGraph_FloatNum" mu) in
    let sigma = match assignCons env sigma with Some x then x else (conapp_ "DelayedGraph_FloatNum" sigma) in
    i (conapp_ "DelayedGraph_DsDistGaussian" (i (urecord_ [("mu", mu), ("sigma", sigma)])))
  | DCategorical {p = p} ->
    let p = match assignCons env p with Some x then x else (conapp_ "DelayedGraph_SeqFParam" p) in
    i (conapp_ "DelayedGraph_DsDistCategorical" (i (urecord_ [("p", p)])))
  | DUniform {a = a, b = b} ->
    let a = match assignCons env a with Some x then x else (conapp_ "DelayedGraph_FloatNum" a) in
    let b = match assignCons env b with Some x then x else (conapp_ "DelayedGraph_FloatNum" b) in
    i (conapp_ "DelayedGraph_DsDistUniform" (i (urecord_ [("a", a), ("b", b)])))
  | DPoisson {lambda = lambda} ->
    let lambda = match assignCons env lambda with Some x then x else (conapp_ "DelayedGraph_FloatNum" lambda) in
    i (conapp_ "DelayedGraph_DsDistPoisson" (i (urecord_ [("lambda", lambda)])))
  | DBinomial {n = n, p = p} ->
    let n = match assignCons env n with Some x then x else (conapp_ "DelayedGraph_IntNum" n) in
    let p = match assignCons env p with Some x then x else (conapp_ "DelayedGraph_FloatNum" p) in
    i (conapp_ "DelayedGraph_DsDistBinomial" (i (urecord_ [("n", n), ("p", p)])))
  | DGamma {k = shape, theta = scale} ->
    let shape = match assignCons env shape with Some x then x else (conapp_ "DelayedGraph_FloatNum" shape) in
    let scale = match assignCons env scale with Some x then x else (conapp_ "DelayedGraph_FloatNum" scale) in
    i (conapp_ "DelayedGraph_DsDistGamma" (i (urecord_ [("shape", shape), ("scale", scale)])))
  | DExponential {rate = rate} ->
    let rate = match assignCons env rate with Some x then x else (conapp_ "DelayedGraph_FloatNum" rate) in
    i (conapp_ "DelayedGraph_DsDistExponential" (i (urecord_ [("rate", rate)])))
  | _ -> error "No support for that dist"


end
lang DPPLDelayedSampling = MExprPPL + TransformDsDist + MExprPPLDsANF

  sem replaceWithValue env =
  | TmLet ({body = TmAssume _} &t) ->
    TmLet {t with inexpr = replaceWithValue env t.inexpr}
  | TmLet ({body = TmObserve _} &t) ->
    TmLet {t with inexpr = replaceWithValue env t.inexpr}
  | TmVar a ->
    let sampleT = (ulam_ "d" (assume_ (var_ "d"))) in
    let varType = mapLookup a.ident env in
    match varType with Some (RandomParam _) then
      appf3_ (var_ "value") sampleT (var_ "graph") (conapp_ "DelayedGraph_RandomVar" (TmVar a))
    else (TmVar a)
  | t -> smap_Expr_Expr (replaceWithValue env) t

  sem delayedSampling =
  | prog ->
    -- apply ANF first
    let prog = normalizeTerm prog in
    --print (mexprPPLToString prog);
    -- get the types for the distribution parameters
    let env = createEnvParam (mapEmpty nameCmp) prog in
    -- if a random variable 'x' needs to be sampled, replace those places with 'value x'
    let prog = replaceWithValue env prog in
    -- transform distrubutions to delayed distributions that will not be sampled directly at runtime
    let transformedP = transformDsDistributions env prog in
    -- apply delayed sampling
    delayedTransform env transformedP

  sem delayedTransform : Map Name EnvParam -> Expr -> Expr
  sem delayedTransform env =
  /-
  -- When encountered with TmAssume, replace it with the vertex representation.
  -- createVertex: create a vertex with DsDist
  -- addVertex: add the vertex to the graph as well as the edges (dependencies)
  -/
  | TmLet ({body = TmAssume a} &t) ->
    let g = var_ "graph" in
    let tbody = appf1_ (var_ "createVertex") a.dist in
    let tinexpr =
      bindall_
      [ ulet_ "" (appf2_ (var_ "addVertex") g (nvar_ t.ident))
      , t.inexpr] in
    TmLet {{{t with body = tbody} with inexpr=delayedTransform env tinexpr} with tyAnnot = tyunknown_}
  /-
  -- When encountered with TmObserve,
  -- createObsVertex: create a vertex with DsDist and observed value
  -- addVertex: add the vertex to the graph as well as the edges (dependencies)
  -- value: call the value function to graft and realize the node
  -- get the marginalized dist and update the TmObserve with its marginalized dist
  -/
  | TmLet ({body = TmObserve a} &t) ->
    let g = var_ "graph" in
    let tbody = appf2_ (var_ "createObsVertex") a.dist a.value in
    let sampleT = (ulam_ "d" (assume_ (var_ "d"))) in
    let tinexpr =
      bindall_
      [ ulet_ "" (appf2_ (var_ "addVertex") g (nvar_ t.ident))
      , nulet_ t.ident (appf3_ (var_ "valueDs") sampleT g (nvar_ t.ident))
      , ulet_ "" (TmObserve {a with dist =
          appf3_ (var_ "transformDsDist") sampleT g (appf2_ (var_ "getMargDist") g (nvar_ t.ident))
        })]
       in
    TmLet {{{t with body = tbody} with inexpr=bind_ tinexpr (delayedTransform env t.inexpr)} with tyAnnot = tyunknown_}

  | t -> smap_Expr_Expr (delayedTransform env) t

end

