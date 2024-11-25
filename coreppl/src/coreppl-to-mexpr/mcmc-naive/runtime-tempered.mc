include "common.mc"

include "ext/dist-ext.mc"
include "ext/math-ext.mc"
include "math.mc"
include "seq.mc"
include "string.mc"

include "../runtime-common.mc"
include "../runtime-dists.mc"

-- In naive MCMC, the state is simply the accumulated weight.
type State = {

  -- The weight of the current execution
  weight: Ref Float,

  -- The pdfs of priors of the current execution
  priorWeight: Ref Float
}

-- State (reused throughout inference)
let state: State = {
  weight = ref 0.,
  priorWeight = ref 0.
}

let updatePriorWeight = lam v.
  modref state.priorWeight (addf (deref state.priorWeight) v)

let updateWeight = lam v.
  modref state.weight (addf (deref state.weight) v)

-- General inference algorithm for naive MCMC
let run : all a. Unknown -> (State -> a) -> use RuntimeDistBase in Dist a =
  lam config. lam model.
  use RuntimeDist in

  let logPotential = lam sample. lam weight. lam priorWeight. lam beta.
    /-let weight = deref state.weight in
    let priorWeight = deref state.priorWeight in
    print (join ["weight:", (float2string weight),"\n"]);
    print (join ["sample:", (float2string (unsafeCoerce sample)),"\n"]);
    print (join ["priorWeight:", (float2string priorWeight),"\n"]);
-/
    let weight = mulf weight beta in
    let logPotential = addf weight priorWeight  in
  --  print (join ["log_potential(",(float2string beta),")=", (float2string logPotential),"\n\n"]);
    print (join ["response(", (float2string logPotential), ")\n"]);
    flushStdout ()
  in

  let callSampler = lam weights. lam samples. lam priorWeights. lam beta.
    modref state.weight 0.;
    modref state.priorWeight 0.;
    let sample = model state in
    let weight = deref state.weight in
    let priorWeight = deref state.priorWeight in
    if null weights then 
        mcmcAccept ();
        (weight,sample,priorWeight)
    else 
      let prevWeight = head weights in
      let prevSample = head samples in
      let prevPriorWeight = head priorWeights in
      let logMhAcceptProb: Float = minf 0. (mulf beta (subf weight prevWeight)) in
      if bernoulliSample (exp logMhAcceptProb) then
          mcmcAccept ();
          (weight, sample, priorWeight)
      else
          (prevWeight, prevSample, prevPriorWeight)
  in

  recursive let mh = lam weights. lam samples. lam priorWeights. 
      match externalReadLine externalStdin with (s, false) then
        -- if we read log_potential(beta), call it to calculate 
        if strStartsWith "log_potential" s then
          let str = get (strSplit "(" s) 1 in
        --  print (join ["log_potential_beta:", str,"\n"]);
          let beta = (string2float (strReplace ")" "" str)) in
         --print (join ["log_potential(", float2string beta,")","\n"]);
          logPotential (head samples) (head weights) (head priorWeights) beta;
          mh weights samples priorWeights
        -- if we read call_sampler!(beta), we call the sampler to sample a new value based on the 
        -- given beta 
        else if strStartsWith "call_sampler!" s then
          let str = get (strSplit "(" s) 1 in
         -- print (join ["call_sampler_beta:", str,"\n"]);
          let beta = (string2float (strReplace ")" "" str)) in
          --print (join ["call_sampler(", float2string beta,")\n\n"]);
          match (callSampler weights samples priorWeights beta) with (weight, sample, priorWeight) in

          print "response()\n";
          flushStdout ();
          mh (cons weight weights) (cons sample samples) (cons priorWeight priorWeights)
        else (weights, samples, priorWeights)
    else (weights, samples, priorWeights)
  in

  let runs = config.iterations in
  (if lti (length argv) 2 then () else setSeed runs);
  -- Used to keep track of acceptance ratio
  mcmcAcceptInit runs;

  
  let res = mh [] [] [] in

  -- Reverse to get the correct order
  let res = match res with (weights,samples,_) in
    (reverse weights, reverse samples)
  in

  -- Return
  constructDistEmpirical res.1 (create runs (lam. 1.))
    (EmpMCMC { acceptRate = mcmcAcceptRate () })
