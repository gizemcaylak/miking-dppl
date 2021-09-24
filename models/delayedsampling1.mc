mexpr
let a = assume (Gaussian 0.0 1.0) in
let b = assume (Gaussian a 1.0) in
let c = assume (Gaussian b 1.0) in
let d = assume (Gaussian b 1.0) in
let e = assume (Gaussian c 1.0) in
let f = assume (Gaussian d 1.0) in
[e, d]
