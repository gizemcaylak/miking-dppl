mexpr
let a = assume (Gaussian 0. 3.) in
let b = assume (Gaussian a 1.) in
observe 0.5 (Gaussian b 1.);
b
