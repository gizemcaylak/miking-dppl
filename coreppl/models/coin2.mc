 mexpr
let theta = assume (Gaussian 0.0 1.0) in
let beta = assume (Beta 5. 5.) in
let c = assume (Gaussian beta 1.) in
let d = assume (Beta beta 3.) in
observe 0.5 (Gaussian c 1.);
observe 0.7 (Gaussian theta 1.);
observe 0.8 (Gaussian beta 1.);
observe 0.2 (Gaussian d 1.);
observe 0.5 (Gaussian beta 1.);

--observes theta [true,false,true];
c

