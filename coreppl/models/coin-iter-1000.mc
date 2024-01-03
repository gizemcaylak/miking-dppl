include "seq.mc"
let model: () -> Float = lam.
  let theta = assume (Beta 10.0 10.0) in
  iter (lam. observe true (Bernoulli theta)) (make 1000 0);
  theta

mexpr
model ()
