mexpr
/-
let a = assume (Gaussian 0. 1.) in
let b = assume (Gaussian a 1.) in
--let c = assume (Gaussian a 1.) in
observe 0.5 (Gaussian a 1.);
observe 1.5 (Gaussian b 1.)
-/

let a = assume (Gamma 1. 2.) in
let b = assume (Exponential a) in
--observe (addf b c) (Gaussian 0. 1.)
observe 0.1 (Exponential a);
observe 0.5 (Exponential a)


