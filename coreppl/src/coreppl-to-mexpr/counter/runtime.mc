include "ext/math-ext.mc"
include "string.mc"

type Counter = Ref Int
let incrementCounter = lam c. modref c (addi (deref c) 1)
let printCounter = lam c.-- print (join ["Counter:",(int2string (deref c)),"\n"])
()
let resetCounter = lam c. modref c 0

let runSequential = lam model.
  let c = ref 0 in
  model c

let runParallel = lam model.
  (lam s. model (ref 0) s)

