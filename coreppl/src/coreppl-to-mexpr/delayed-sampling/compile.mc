lang MExprPPLDsANF = MExprPPL + DPPLParser + Externals + MExprANFAll
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
  | TmApp ({lhs=TmApp ({lhs=TmConst ({val=CAddf ()}&c),rhs=v1}&a2),rhs=v2}&a1) ->
    normalizeName
      (lam v1. normalizeName (lam v2. k (TmApp {{a1 with lhs=TmApp {{a2 with lhs=TmConst c} with rhs=v1}} with rhs=v2})) v2) v1
  | TmApp ({lhs=TmApp ({lhs=TmConst ({val=CMulf ()}&c),rhs=v1}&a2),rhs=v2}&a1) ->
    normalizeName
      (lam v1. normalizeName (lam v2. k (TmApp {{a1 with lhs=TmApp {{a2 with lhs=TmConst c} with rhs=v1}} with rhs=v2})) v2) v1

 end

lang TransformDsDist = TransformDist + MExprPPL +DPPLParser

  -- a parameter of a distribution can be either
  syn EnvParam =
  | FloatParam () -- a float, e.g. Gaussian 3.2 1.
  | IntParam () -- an integer, e.g. UniformDisc 1 5
  | RandomParam () -- a distribution, e.g Gaussian a 1. where a ~ Gaussian 3. 2.
  | SeqFParam () -- a sequence, e.g. Categorical [0.3,0.7]
  | AffineParam {v:Expr,meanScale:Expr,meanOffset:Expr}

  sem affineAddTransform env id v =
  | (Some (RandomParam _), None ()) -> mapInsert id (AffineParam {v=v.0,meanScale=float_ 1.,meanOffset=v.1}) env
  | (Some (RandomParam _), Some (FloatParam _)) -> mapInsert id (AffineParam {v=v.0,meanScale=float_ 1.,meanOffset=v.1}) env
  | (None (), Some (RandomParam _)) -> mapInsert id (AffineParam {v=v.1,meanScale=float_ 1.,meanOffset=v.0}) env
  | (Some (FloatParam _), Some (RandomParam _)) -> mapInsert id (AffineParam {v=v.1,meanScale=float_ 1.,meanOffset=v.0}) env
  | (Some (AffineParam p), None ()) -> mapInsert id (AffineParam {v=p.v,meanScale=p.meanScale,meanOffset=addf_ p.meanOffset v.1}) env
  | (Some (AffineParam p), Some (FloatParam ())) -> mapInsert id (AffineParam {v=p.v,meanScale=p.meanScale,meanOffset=addf_ p.meanOffset v.1}) env
  | (None (), Some (AffineParam p)) -> mapInsert id (AffineParam {v=p.v,meanScale=p.meanScale,meanOffset=addf_ p.meanOffset v.0}) env
  | (Some (FloatParam _), Some (AffineParam p)) -> mapInsert id (AffineParam {v=p.v,meanScale=p.meanScale,meanOffset=addf_ p.meanOffset v.0}) env
  | _ -> mapInsert id (FloatParam ()) env

  sem affineScaleTransform env id v =
  | (Some (RandomParam _), None ()) -> mapInsert id (AffineParam {v=v.0,meanScale=v.1,meanOffset=float_ 0.}) env
  | (Some (RandomParam _), Some (FloatParam _)) -> mapInsert id (AffineParam {v=v.0,meanScale=v.1,meanOffset=float_ 0.}) env
  | (None (), Some (RandomParam _)) -> mapInsert id (AffineParam {v=v.1,meanScale=v.0,meanOffset=float_ 0.}) env
  | (Some (FloatParam _), Some (RandomParam _)) -> mapInsert id (AffineParam {v=v.1,meanScale=v.0,meanOffset=float_ 0.}) env
  | (Some (AffineParam p), None ()) -> mapInsert id (AffineParam {v=p.v,meanScale=mulf_ p.meanScale v.1,meanOffset=mulf_ p.meanOffset v.1}) env
  | (Some (AffineParam p), Some (FloatParam ())) -> mapInsert id (AffineParam {v=p.v,meanScale=mulf_ p.meanScale v.1,meanOffset=mulf_ p.meanOffset v.1}) env
  | (None (), Some (AffineParam p)) -> mapInsert id (AffineParam {v=p.v,meanScale=mulf_ p.meanScale v.1,meanOffset=mulf_ p.meanOffset v.0}) env
  | (Some (FloatParam _), Some (AffineParam p)) -> mapInsert id (AffineParam {v=p.v,meanScale=mulf_ p.meanScale v.1,meanOffset=mulf_ p.meanOffset v.0}) env
  | _ -> mapInsert id (FloatParam ()) env
  /-
  -- If an observe or assume term is encountered, set the type as RandomParam;otherwise,
  -- Depending on if it is float or integer set it as FloatParam, IntParam, SeqFParam respectively
  -/
  sem createEnvParam: Map Name EnvParam -> Expr -> Map Name EnvParam
  sem createEnvParam env =
  | TmLet ({body = (TmAssume _ | TmObserve _)} & t) ->
    let env = mapInsert t.ident (RandomParam ()) env in
    createEnvParam (createEnvParam env t.body) t.inexpr
  | TmLet ({body= TmApp ({lhs = TmApp ({lhs=TmConst ({val= (CAddf ())}&c),rhs=TmVar v1}&a2), rhs=TmVar v2}&a1)}&t) ->
    let v1Type = mapLookup v1.ident env in
    let v2Type = mapLookup v2.ident env in
    let env = affineAddTransform env t.ident (TmVar v1,TmVar v2) (v1Type, v2Type) in
    createEnvParam (createEnvParam env t.body) t.inexpr
  | TmLet ({body= TmApp ({lhs = TmApp ({lhs=TmConst ({val= (CMulf ())}&c),rhs=TmVar v1}&a2), rhs=TmVar v2}&a1)}&t) ->
    let v1Type = mapLookup v1.ident env in
    let v2Type = mapLookup v2.ident env in
    let env = affineScaleTransform env t.ident (TmVar v1,TmVar v2) (v1Type, v2Type) in
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

  sem transformDsDistributions: Map Name EnvParam -> Expr -> Expr
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
  | FloatParam _ -> (conapp_ "DelayedGraph_FloatParam" t)
  | IntParam _ ->  (conapp_ "DelayedGraph_IntParam" t)
  | RandomParam _ -> (conapp_ "DelayedGraph_RandomParam" t)
  | SeqFParam _ -> (conapp_ "DelayedGraph_SeqFParam" t)
  | AffineParam _ ->  t

  sem transformDsDist: (Expr -> Expr) -> (Map Name EnvParam) -> Dist -> Expr
  sem transformDsDist i env =
  | DBeta {a = a, b = b} ->
    let a = match assignCons env a with Some x then x else (conapp_ "DelayedGraph_FloatParam" a) in
    let b = match assignCons env b with Some x then x else (conapp_ "DelayedGraph_FloatParam" b) in
    i (conapp_ "DelayedGraph_DsDistBeta" (i (urecord_ [("a", a), ("b", b)])))
  | DBernoulli {p = p} ->
    let p = match assignCons env p with Some x then x else (conapp_ "DelayedGraph_FloatParam" p) in
    i (conapp_ "DelayedGraph_DsDistBernoulli" (i (urecord_ [("p", p)])))
  | DGaussian {mu = mu, sigma = sigma} ->
    match mu with TmVar v in
    let res = match mapLookup v.ident env with Some (AffineParam p) then
        let mu = match assignCons env p.v with Some x then x else (conapp_ "DelayedGraph_FloatParam" p.v) in
        (mu,p.meanScale,p.meanOffset)
      else let mu = match assignCons env mu with Some x then x else (conapp_ "DelayedGraph_FloatParam" mu) in
        (mu, float_ 1.,float_ 0.) in
    let sigma = match assignCons env sigma with Some x then x else (conapp_ "DelayedGraph_FloatParam" sigma) in
    i (conapp_ "DelayedGraph_DsDistGaussian" (i (urecord_ [("mu", res.0), ("sigma", sigma), ("meanScale", res.1), ("meanOffset",res.2)])))
  | DCategorical {p = p} ->
    let p = match assignCons env p with Some x then x else (conapp_ "DelayedGraph_SeqFParam" p) in
    i (conapp_ "DelayedGraph_DsDistCategorical" (i (urecord_ [("p", p)])))
  | DUniform {a = a, b = b} ->
    let a = match assignCons env a with Some x then x else (conapp_ "DelayedGraph_FloatParam" a) in
    let b = match assignCons env b with Some x then x else (conapp_ "DelayedGraph_FloatParam" b) in
    i (conapp_ "DelayedGraph_DsDistUniform" (i (urecord_ [("a", a), ("b", b)])))
  | DPoisson {lambda = lambda} ->
    let lambda = match assignCons env lambda with Some x then x else (conapp_ "DelayedGraph_FloatParam" lambda) in
    i (conapp_ "DelayedGraph_DsDistPoisson" (i (urecord_ [("lambda", lambda)])))
  | DBinomial {n = n, p = p} ->
    let n = match assignCons env n with Some x then x else (conapp_ "DelayedGraph_IntParam" n) in
    let p = match assignCons env p with Some x then x else (conapp_ "DelayedGraph_FloatParam" p) in
    i (conapp_ "DelayedGraph_DsDistBinomial" (i (urecord_ [("n", n), ("p", p)])))
  | DGamma {k = shape, theta = scale} ->
    let shape = match assignCons env shape with Some x then x else (conapp_ "DelayedGraph_FloatParam" shape) in
    let scale = match assignCons env scale with Some x then x else (conapp_ "DelayedGraph_FloatParam" scale) in
    i (conapp_ "DelayedGraph_DsDistGamma" (i (urecord_ [("shape", shape), ("scale", scale)])))
  | DExponential {rate = rate} ->
    let rate = match assignCons env rate with Some x then x else (conapp_ "DelayedGraph_FloatParam" rate) in
    i (conapp_ "DelayedGraph_DsDistExponential" (i (urecord_ [("rate", rate)])))
  | DDirichlet {a = a} -> let a = match assignCons env a with Some x then x else (conapp_ "DelayedGraph_SeqFParam" a) in
    i (conapp_ "DelayedGraph_DsDistDirichlet" (i (urecord_ [("a", a)])))
  | DMultinomial {n = n, p = p} ->
    let n = match assignCons env n with Some x then x else (conapp_ "DelayedGraph_IntParam" n) in
    let p = match assignCons env p with Some x then x else (conapp_ "DelayedGraph_FloatParam" p) in
    i (conapp_ "DelayedGraph_DsDistMultinomial" (i (urecord_ [("n", n), ("p", p)])))
  | _ -> error "No support for that dist"
end

lang DPPLDelayedTransform = TransformDsDist

  -- if a random variable x needs to be sampled, i.e. its value is needed, we replace it with value x
  sem replaceWithValue env =
  | TmLet ({body = TmAssume _} &t) ->
    TmLet {t with inexpr = replaceWithValue env t.inexpr}
  | TmLet ({body = TmObserve _} &t) ->
    TmLet {t with inexpr = replaceWithValue env t.inexpr}
  | TmLet ({body=TmApp ({lhs = TmApp ({lhs=TmConst ({val= (CAddf ())}&c),rhs=TmVar v1}&a2), rhs=TmVar v2}&a1)}&t) ->
    TmLet {t with inexpr = replaceWithValue env t.inexpr}
  | TmLet ({body=TmApp ({lhs = TmApp ({lhs=TmConst ({val= (CMulf ())}&c),rhs=TmVar v1}&a2), rhs=TmVar v2}&a1)}&t) ->
    TmLet {t with inexpr = replaceWithValue env t.inexpr}
  | TmVar a -> -- equivalent to value(X)
    let sampleT = (ulam_ "d" (assume_ (var_ "d"))) in
    let varType = mapLookup a.ident env in
    /-match varType with Some (AffineParam p) then
      appf2_ (var_ "value") sampleT (conapp_ "DelayedGraph_AffineParam" (TmVar a))
    else-/ match varType with Some (RandomParam _) then
      appf2_ (var_ "value") sampleT (conapp_ "DelayedGraph_RandomParam" (TmVar a))
    else (TmVar a)
  | t -> smap_Expr_Expr (replaceWithValue env) t

  sem affineAddTransformBody tbody sampleT v =
  | (Some (RandomParam _), Some (RandomParam _)) -> affineTransformBodyH sampleT addf_ v
  | (Some (RandomParam _), Some (AffineParam _)) -> affineTransformBodyH sampleT addf_ v
  | (Some (AffineParam _), Some (AffineParam _)) -> affineTransformBodyH sampleT addf_ v
  | (Some (AffineParam _), Some (RandomParam _)) -> affineTransformBodyH sampleT addf_ v
  | (Some (RandomParam _), None ()) -> (conapp_ "DelayedGraph_AffineParam" (urecord_ [("aV", conapp_ "DelayedGraph_RandomParam" v.0), ("meanScale",float_ 1. ), ("meanOffset",v.1)]))
  | (Some (RandomParam _), Some (FloatParam _)) -> (conapp_ "DelayedGraph_AffineParam" (urecord_ [("aV", conapp_ "DelayedGraph_RandomParam" v.0), ("meanScale",float_ 1. ), ("meanOffset",v.1)]))
  | (None (), Some (RandomParam _)) -> (conapp_ "DelayedGraph_AffineParam" (urecord_ [("aV", conapp_ "DelayedGraph_RandomParam" v.1), ("meanScale",float_ 1. ), ("meanOffset",v.0)]))
  | (Some (FloatParam _), Some (RandomParam _)) -> (conapp_ "DelayedGraph_AffineParam" (urecord_ [("aV", conapp_ "DelayedGraph_RandomParam" v.1), ("meanScale",float_ 1. ), ("meanOffset",v.0)]))
  | (Some (AffineParam p), None ()) -> (conapp_ "DelayedGraph_AffineParam" (urecord_ [("aV", conapp_ "DelayedGraph_RandomParam" p.v), ("meanScale",p.meanScale ), ("meanOffset",addf_ v.1 p.meanOffset)]))
  | (Some (AffineParam p), Some (FloatParam _)) -> (conapp_ "DelayedGraph_AffineParam" (urecord_ [("aV", conapp_ "DelayedGraph_RandomParam" p.v), ("meanScale",p.meanScale ), ("meanOffset",addf_ v.1 p.meanOffset)]))
  | (None (), Some (AffineParam p)) -> (conapp_ "DelayedGraph_AffineParam" (urecord_ [("aV", conapp_ "DelayedGraph_RandomParam" p.v), ("meanScale",p.meanScale ), ("meanOffset",addf_ v.0 p.meanOffset)]))
  | (Some (FloatParam ()), Some (AffineParam p)) -> (conapp_ "DelayedGraph_AffineParam" (urecord_ [("aV", conapp_ "DelayedGraph_RandomParam" p.v), ("meanScale",p.meanScale ), ("meanOffset",addf_ v.0 p.meanOffset)]))
  | t -> tbody

  sem affineScaleTransformBody tbody sampleT v =
  | (Some (RandomParam _), Some (RandomParam _)) -> affineTransformBodyH sampleT mulf_ v
  | (Some (RandomParam _), Some (AffineParam _)) -> affineTransformBodyH sampleT mulf_ v
  | (Some (AffineParam _), Some (AffineParam _)) -> affineTransformBodyH sampleT mulf_ v
  | (Some (AffineParam _), Some (RandomParam _)) -> affineTransformBodyH sampleT mulf_ v
  | (Some (RandomParam _), None ()) -> (conapp_ "DelayedGraph_AffineParam" (urecord_ [("aV", conapp_ "DelayedGraph_RandomParam" v.0), ("meanScale",v.1 ), ("meanOffset",float_ 0.)]))
  | (Some (RandomParam _), Some (FloatParam _)) -> (conapp_ "DelayedGraph_AffineParam" (urecord_ [("aV", conapp_ "DelayedGraph_RandomParam" v.0), ("meanScale",v.1 ), ("meanOffset",float_ 0.)]))
  | (None (), Some (RandomParam _)) -> (conapp_ "DelayedGraph_AffineParam" (urecord_ [("aV", conapp_ "DelayedGraph_RandomParam" v.1), ("meanScale", v.0 ), ("meanOffset",float_ 0.)]))
  | (Some (FloatParam _), Some (RandomParam _)) -> (conapp_ "DelayedGraph_AffineParam" (urecord_ [("aV", conapp_ "DelayedGraph_RandomParam" v.1), ("meanScale", v.0 ), ("meanOffset", float_ 0.)]))
  | (Some (AffineParam p), None ()) -> (conapp_ "DelayedGraph_AffineParam" (urecord_ [("aV", conapp_ "DelayedGraph_RandomParam" p.v), ("meanScale",mulf_ p.meanScale v.1 ), ("meanOffset",mulf_ v.1 p.meanOffset)]))
  | (Some (AffineParam p), Some (FloatParam _)) -> (conapp_ "DelayedGraph_AffineParam" (urecord_ [("aV", conapp_ "DelayedGraph_RandomParam" p.v), ("meanScale",mulf_ p.meanScale v.1), ("meanOffset",mulf_ v.1 p.meanOffset)]))
  | (None (), Some (AffineParam p)) -> (conapp_ "DelayedGraph_AffineParam" (urecord_ [("aV", conapp_ "DelayedGraph_RandomParam" p.v), ("meanScale",mulf_ v.0 p.meanScale ), ("meanOffset",mulf_ v.0 p.meanOffset)]))
  | (Some (FloatParam ()), Some (AffineParam p)) -> (conapp_ "DelayedGraph_AffineParam" (urecord_ [("aV", conapp_ "DelayedGraph_RandomParam" p.v), ("meanScale",mulf_ v.0 p.meanScale ), ("meanOffset",mulf_ v.0 p.meanOffset)]))
  | t -> tbody

  sem affineTransformBodyH sampleT op =
  | v -> op (appf2_ (var_ "value") sampleT (conapp_ "DelayedGraph_RandomParam" v.0)) (appf2_ (var_ "value") sampleT (conapp_ "DelayedGraph_RandomParam" v.1))

  sem delayedTransform : Map Name EnvParam -> Expr -> Expr
  sem delayedTransform env =
  /-
  -- When encountered with TmAssume, replace it with the vertex representation.
  -- createVertex: create a vertex with DsDist
  -/
  | TmLet ({body = TmAssume a} &t) ->
    let sampleT = (ulam_ "d" (assume_ (var_ "d"))) in
    -- create a node
    let tbody = appf1_ (var_ "createVertex") a.dist in
    TmLet {{{t with body = tbody} with inexpr=delayedTransform env t.inexpr} with tyAnnot = tyunknown_}
  /-
  -- When encountered with TmObserve,
  -- createObsVertex: create a vertex with DsDist and observed value
  -- value: call the valueDs function to graft and realize the node
  -- get the marginalized dist and update the TmObserve with its marginalized dist
  -/
  | TmLet ({body = TmObserve a} &t) ->
    let tbody = appf2_ (var_ "createObsVertex") a.dist a.value in
    let sampleT = (ulam_ "d" (assume_ (var_ "d"))) in
    let tinexpr =
      bindall_
      [ ulet_ "" (appf2_ (var_ "valueDs") sampleT (nvar_ t.ident))
      , ulet_ "" (TmObserve {a with dist =
          appf2_ (var_ "transformDsDist") sampleT (appf1_ (var_ "getMargDist") (nvar_ t.ident))
        })
        ]
       in
    TmLet {{{t with body = tbody} with inexpr=bind_ tinexpr (delayedTransform env t.inexpr)} with tyAnnot = tyunknown_}
  | TmLet ({body=TmApp ({lhs = TmApp ({lhs=TmConst ({val= (CAddf ())}&c),rhs=TmVar v1}&a2), rhs=TmVar v2}&a1)}&t) ->
    let v1Type = mapLookup v1.ident env in
    let v2Type = mapLookup v2.ident env in
    let sampleT = (ulam_ "d" (assume_ (var_ "d"))) in
    let tbody = affineAddTransformBody t.body sampleT (TmVar v1, TmVar v2) (v1Type,v2Type) in
    TmLet {{{t with body = tbody} with inexpr=(delayedTransform env t.inexpr)} with tyAnnot = tyunknown_}
  | TmLet ({body=TmApp ({lhs = TmApp ({lhs=TmConst ({val= (CMulf ())}&c),rhs=TmVar v1}&a2), rhs=TmVar v2}&a1)}&t) ->
    let v1Type = mapLookup v1.ident env in
    let v2Type = mapLookup v2.ident env in
    let sampleT = (ulam_ "d" (assume_ (var_ "d"))) in
    let tbody = affineScaleTransformBody t.body sampleT (TmVar v1, TmVar v2) (v1Type,v2Type) in
    TmLet {{{t with body = tbody} with inexpr=(delayedTransform env t.inexpr)} with tyAnnot = tyunknown_}
  | t -> smap_Expr_Expr (delayedTransform env) t

end

lang DPPLDelayedSampling 
  sem delayedSampling =
  | prog ->
    -- apply ANF first
    let prog = (lam prog. use MExprPPLDsANF in normalizeTerm prog) prog in
    use DPPLDelayedTransform in
    -- get the types for the distribution parameters
    let env = createEnvParam (mapEmpty nameCmp) prog in
    -- if a random variable 'x' needs to be sampled, replace those places with 'value x'
    let prog = replaceWithValue env prog in
    -- transform distrubutions to delayed distributions that will not be sampled directly at runtime
    let transformedP = transformDsDistributions env prog in
    -- apply delayed sampling
    delayedTransform env transformedP
end

