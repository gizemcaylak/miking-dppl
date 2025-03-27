include "../coreppl.mc"
include "../dppl-arg.mc"

lang BPFMethod = MExprPPL
  syn InferMethod =
  | BPF {particles : Expr
        ,freq : Expr}

  sem pprintInferMethod indent env =
  | BPF {particles = particles, freq = freq} ->
    let i = pprintIncr indent in
    match pprintCode i env particles with (env, particles) in
    match pprintCode i env freq with (env, freq) in
    (env, join ["(BPF {particles = ", particles,
                "freq =", freq, "})"])

  sem inferMethodFromCon info bindings =
  | "BPF" ->
    let expectedFields = [
      ("particles", int_ defaultArgs.particles),
      ("freq", float_ defaultArgs.freq)
    ] in
    match getFields info bindings expectedFields with [particles, freq] in
    BPF {particles = particles, freq = freq}

  sem inferMethodFromOptions options =
  | "smc-bpf" ->
    BPF {particles = int_ options.particles,
        freq = float_ options.freq}

  sem inferMethodConfig info =
  | BPF {particles = particles, freq = freq} ->
    fieldsToRecord info [
      ("particles", particles),
      ("freq", freq)
    ]

  sem inferMethodConfigType info =
  | BPF _ ->
    tyRecord info [
      ("particles", ityint_ info),
      ("freq", ityfloat_ info)
    ]

  sem typeCheckInferMethod env info =
  | BPF {particles = particles, freq = freq} ->
    let int = TyInt {info = info} in
    let float = TyFloat {info = info} in
    let particles = typeCheckExpr env particles in
    unify env [info, infoTm particles] int (tyTm particles);
    let freq = typeCheckExpr env freq in
    unify env [info, infoTm freq] float (tyTm freq);
    BPF {particles = particles, freq = freq}

  sem smapAccumL_InferMethod_Expr env =
  | BPF r ->
    match f acc r.particles with (acc, particles) in
    match f acc r.freq with (acc, freq) in
    (acc, BPF {r with particles = particles, freq = freq})

  sem setRuns expr =
  | BPF r -> BPF {r with particles = expr}

end
