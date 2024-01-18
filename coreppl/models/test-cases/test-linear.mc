--include "ext/math-ext.mc"
mexpr
/-let x = (assume (Gaussian 0. 1.))  in
--let z = addf x 2. in
observe 2. (Gaussian (addf x 2.) 1.)-/
/-let x = assume (Gaussian 0. 1.) in
let z = addf (mulf 3. x) 2. in
observe 2. (Gaussian 2. (externalSqrt 10.))-/

let x = assume (Gaussian 0. 1.) in
let z = addf x 2. in
observe 2. (Gaussian z 1.);
observe 0.5 (Gaussian x 1.)
/-
observe 2. (Gaussian 2. (externalSqrt 10.));
let x = assume (Gaussian 0. 1.) in
let z = addf (mulf 3. x) 2. in
observe 0.5 (Gaussian x 1.)-/
