mexpr
-- manual static transformation of the example from Jan's thesis pg.59
/-
-- Calculates the posterior parameters for Gaussian Dist. given
-- mu0: prior mean
-- v0: prior variance
-- v: known variance of likehood
-- n: the number of observations
-- x: the observations
-/
let postHyperGaussian = lam mu0:Float. lam v0:Float. lam v:Float.
                        lam x:[Float].
  let n = int2float (length x) in
  let mean = mulf (divf 1.0 (addf (divf 1.0 v0) (divf n v)))
                  (addf (divf mu0 v0) (divf (foldl addf 0.0 x) v)) in
  let variance = divf 1.0 (addf (divf 1.0 v0) (divf n v)) in
  (mean, variance)
in

/-
-- Calculates the posterior predictive parameters for Gaussian Dist. given
-- muP: posterior mean
-- vP: posterior variance
-- v: known variance
-/
let postPredGaussian = lam mu0:Float. lam v0:Float. lam v:Float.
                        lam x:[Float].
  let postP = postHyperGaussian mu0 v0 v x in
  (postP.0, addf postP.1 v)
in

let aMargParams = (0.0, 1.0) in
let bLikeParamVar = 1.0 in
let bMargParams =
  postPredGaussian aMargParams.0 aMargParams.1 bLikeParamVar []
in
let cLikeParamVar = 1.0 in
let cMargParams =
  postPredGaussian bMargParams.0 bMargParams.1 cLikeParamVar []
in
let eLikeParamVar = 1.0 in
let eMargParams =
  postPredGaussian cMargParams.0 cMargParams.1 eLikeParamVar []
in
let e = assume (Gaussian eMargParams.0 eMargParams.1) in
let cGivenEParams = postHyperGaussian cMargParams.0 cMargParams.1 eLikeParamVar [e] in
let c = assume (Gaussian cGivenEParams.0 cGivenEParams.1) in
let bGivenCParams = postHyperGaussian bMargParams.0 bMargParams.1 cLikeParamVar [c] in
let dLikeParamVar = 1.0 in
let dMargParams =
  postPredGaussian bGivenCParams.0 bGivenCParams.1 dLikeParamVar []
in
let d = assume (Gaussian dMargParams.0 dMargParams.1) in
let bGivenDParams = postHyperGaussian bMargParams.0 bMargParams.1 dLikeParamVar [d] in
let b = assume (Gaussian bGivenDParams.0 bGivenDParams.1) in -- should be removed at the end

let aGivenBParams = postHyperGaussian aMargParams.0 aMargParams.1 bLikeParamVar [b] in -- should be removed at the end
let f = assume (Gaussian d 1.0) -- should be removed at the end
[e,d]
