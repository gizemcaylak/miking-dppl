mexpr
let a = assume (Gamma 5. 4.) in
let c = assume (Gamma 3. 5.) in
let b = assume (Beta a a) in
observe 0.6 (Exponential b);
b
