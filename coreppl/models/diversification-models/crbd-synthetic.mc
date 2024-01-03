include "tree-synthetic.mc"
include "crbd.mc"
include "digraph.mc"

let model: () -> () = lam.
  crbd tree rho

mexpr
model ()
