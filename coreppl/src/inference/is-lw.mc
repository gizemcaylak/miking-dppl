include "../coreppl.mc"
include "../dppl-arg.mc"

lang ImportanceSamplingMethod = MExprPPL
  syn InferMethod =
  | Importance {particles : Expr}

  sem pprintInferMethod indent env =
  | Importance {particles = particles} ->
    let i = pprintIncr indent in
    match pprintCode i env particles with (env, particles) in
    (env, join ["(Importance {particles = ", particles, "})"])

  sem inferMethodFromCon info bindings =
  | "Importance" ->
    let expectedFields = [
      ("particles", int_ defaultArgs.particles)
    ] in
    match getFields info bindings expectedFields with [particles] in
    Importance {particles = particles}

  sem inferMethodFromOptions options =
  | "is-lw" ->
    Importance {particles = int_ options.particles}

  sem inferMethodConfig info =
  | Importance {particles = particles} ->
    fieldsToRecord info [("particles", particles)]

  sem typeCheckInferMethod env info sampleType =
  | Importance {particles = particles} ->
    let int = TyInt {info = info} in
    let particles = typeCheckExpr env particles in
    unify env [info, infoTm particles] int (tyTm particles);
    Importance {particles = particles}

  sem smapAccumL_InferMethod_Expr f acc =
  | Importance r ->
    match f acc r.particles with (acc, particles) in
    (acc, Importance {r with particles = particles})

  sem setRuns expr =
  | Importance r -> Importance {r with particles = expr}

end
