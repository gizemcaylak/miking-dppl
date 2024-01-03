mexpr
let p = 12. in
let c = 5. in
let d = 0.4 in
let a = assume (Beta c c) in
observe true (Bernoulli a)
--observe true (Bernoulli d)
--;observe 0.4 (Gaussian a p)

-- trasnfromation
--env:map name Param
/-
let p = 12. in
let a:Vertex = createVertex (DSBeta (FloatNum 5.) (FloatNum 5.)) in
let 
observe true (DSBernoulli (Node a));
observe true (DSBernoulli (FloatNum 0.4));
observe 0.4 (DSGaussian (Node a) (FloatNum p))
-/
