include "tree-alcedinidae.mc"
include "crbd.mc"

let model: () -> () = lam.
  crbd tree rho

mexpr
model ()
