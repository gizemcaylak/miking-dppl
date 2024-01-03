mexpr
let c = 5. in
let a = assume (Beta c c) in
--let c = addf a 1. in
let b = assume (Bernoulli a) in
b
/-
let a = createVertex (DsBeta (NumFloat 5.) (NumFloat 5.)) in
addVertex a;
let b = createVertex (DsBeta (RandomVar a)) in
addVertex b;
-/
