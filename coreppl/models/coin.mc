let model: () -> Float = lam.
  let theta = assume (Beta 2.0 2.0) in
  --observe 0.5 ( (Beta 2.0 2.0));
  observe 6 (Binomial 6 theta);
  theta
  /-let a = assume (Gaussian 0. 1.) in
  observe 0.5 (Gaussian a 1.);
observe 0.5 (Gaussian a 1.);
observe 0.5 (Gaussian a 1.);
  a-/

mexpr
model ()
