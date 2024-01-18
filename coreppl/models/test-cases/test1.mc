mexpr
let a = assume (Beta 5. 3.) in
let b = assume (Exponential a) in
observe 0.4 (Exponential b);
a
