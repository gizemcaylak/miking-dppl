include "name.mc"
include "map.mc"
include "seq.mc"
lang GraphD
  syn Vertex =
  | Node {ident:Int}

  sem cmprVertex v1 =
  | Node v2 -> match v1 with Node v1 in
  subi v1.ident v2.ident
end

mexpr
use GraphD in
let gx = mapEmpty nameCmp in
let a = assume (Beta 5. 5.) in
let gx =foldl (lam acc. lam i. mapInsert (nameSym "") i acc) gx (range 0 100 1) in
--let gx = mapInsert (nameSym "") 10 gx in

--let gx = digraphAddVertex (Node{ident=5}) gx in
a
--digraphCountVertices gx
