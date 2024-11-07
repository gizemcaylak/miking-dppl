include "../dists.mc"
include "../../inference/smc.mc"
include "../../dppl-arg.mc"
include "mexpr/ast-builder.mc"

lang MExprPPLNaiveMCMC = MExprPPL + Resample + TransformDist

  ----------------
  -- NAIVE MCMC --
  ----------------

  -- NOTE(dlunde,2022-05-04): No way to distinguish between CorePPL and MExpr
  -- AST types here. Optimally, the type would be Options -> CorePPLExpr ->
  -- MExprExpr or similar.
  sem compile : Options -> (Expr,Expr) -> Expr
  sem compile options =
  | (t,_) ->

    -- Transform distributions to MExpr distributions
    let t = mapPre_Expr_Expr transformTmDist t in

    -- Transform samples, observes, and weights to MExpr
    let t = mapPre_Expr_Expr transformProb t in

    t

  sem compileTempered options =
  | (t,_) ->

    -- Transform distributions to MExpr distributions
    let t = mapPre_Expr_Expr transformTmDist t in

    -- Transform samples, observes, and weights to MExpr
    let t = mapPre_Expr_Expr transformProbTempered t in

    t

  sem transformProb =
  | TmAssume t ->
    let i = withInfo t.info in
    i (app_ (i (var_ "sample")) t.dist)
  -- NOTE(dlunde,2022-05-16): Note that we cannot stop immediately when the
  -- weight becomes 0 (-inf in log-space). For this, we need CPS, PCFGs, or
  -- maybe some type of exception handler.
  | TmObserve t ->
    let i = withInfo t.info in
    let weight = i (appf2_ (i (var_ "logObserve")) t.dist t.value) in
    i (appf2_ (i (var_ "updateWeight")) weight (i (var_ "state")))
  | TmWeight t ->
    let i = withInfo t.info in
    i (appf2_ (i (var_ "updateWeight")) t.weight (i (var_ "state")))
  | TmResample t -> withInfo t.info unit_
  | t -> t

sem transformProbTempered =
  | TmLet ({ ident = ident, body = TmAssume ({ dist = dist }&a),
            inexpr = inexpr } & r) & t ->
    let i = withInfo a.info in
    let body = i (appf1_ (i (var_ "sample")) dist) in
    let weight = i (appf2_ (i (var_ "logObserve")) dist (nvar_ ident)) in
    let pWeight = ulet_ "" (i (appf1_ (i (var_ "updatePriorWeight")) weight)) in
    let inexpr = transformProbTempered r.inexpr in
    TmLet {r with body = body, inexpr = bind_ pWeight inexpr}

  | TmAssume r -> error "Impossible"
  -- NOTE(dlunde,2022-05-16): Note that we cannot stop immediately when the
  -- weight becomes 0 (-inf in log-space). For this, we need CPS, PCFGs, or
  -- maybe some type of exception handler.
  | TmObserve t ->
    let i = withInfo t.info in
    let weight = i (appf2_ (i (var_ "logObserve")) t.dist t.value) in
    i (appf1_ (i (var_ "updateWeight")) weight)
  | TmWeight t ->
    let i = withInfo t.info in
    i (appf1_ (i (var_ "updateWeight")) t.weight)
  | TmResample t -> withInfo t.info unit_
  | t -> t
  ----------------------
  -- NAIVE MCMC (CPS) --
  ----------------------

  -- TODO(dlunde,2022-08-22)

end

let compilerNaiveMCMC = lam options. use MExprPPLNaiveMCMC in
  if options.temper then
     ("mcmc-naive/runtime-tempered.mc", compileTempered options)
  else
    ("mcmc-naive/runtime.mc", compile options)
