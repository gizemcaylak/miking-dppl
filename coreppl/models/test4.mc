mexpr
let a = assume (Beta 5. 5.) in 
iter(lam x. observe true (Bernoulli a)) [0.1,0.4,0.4]
