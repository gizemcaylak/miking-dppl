include "seq.mc"
mexpr
let theta = assume (Beta 10.0 10.0) in
iter (lam. observe true (Bernoulli theta)) (make 100 0);
theta

