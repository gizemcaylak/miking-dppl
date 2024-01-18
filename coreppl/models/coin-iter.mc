include "seq.mc"
mexpr
let theta = assume (Beta 10.0 10.0) in
let lst = create 5 (lam. theta) in
let x = 3. in
--let y = [x] in
iter (lam.
let z=assume (Beta 10.0 10.0) in
iter (lam.
let beta = [theta,z]  in
observe true (Bernoulli theta)) [x]
) [x];
theta 

