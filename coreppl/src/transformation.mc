include "digraph.mc"
include "name.mc"
include "coreppl.mc"
include "ext/math-ext.mc"
include "mexpr/anf.mc"

type Label = Int
type QDist = Map Name Expr -- a map from random variable names to their marginalized distribution
type PQDist = Map Name QDist -- a map from plates to QDist,i.e. each plate has its own QDist

-- m: a mapping from a vertex ident to a corresponding vertex
type PBN = {
	g:Digraph Vertex Label,
	m:Map Name Vertex,
  targets:[Name]
}
--StaticAnalyzer: Expr -> 
--Expr -> PBN -> PBN -> Expr

lang MExprPPLStaticDelayedANF = MExprPPL + MExprANFAll
  sem normalize (k : Expr -> Expr) =
  | TmAssume ({ dist = TmDist ({ dist = dist } & td) } & t) ->
    normalizeDist
      (lam dist. k (TmAssume { t with dist = TmDist { td with dist = dist } }))
      dist
  | TmObserve ({ value = value, dist = TmDist ({ dist = dist } & td) } & t) ->
    normalizeName
      (lam value.
        normalizeDist
          (lam dist.
             k (TmObserve {{ t with value = value }
                               with dist = TmDist { td with dist = dist}}))
          dist)
      value

  | TmApp ({lhs=TmApp ({lhs=TmConst ({val=CGet ()}&c),rhs=seq}&a2),rhs=ind}&a1) ->
    normalizeName
      (lam seq.
        normalizeName
          (lam ind.
             k (TmApp {{a1 with lhs= TmApp {{a2 with lhs=TmConst c} with rhs=seq}} with rhs=ind}))
          ind)
      seq

  | TmApp ({lhs=TmApp ({lhs=TmConst ({val=CCreate ()}&c),rhs=rep}&a2),rhs=lmb}&a1) ->
    normalizeName
     (lam rep.
      k (TmApp {{a1 with lhs= TmApp {{a2 with lhs=TmConst c} with rhs=rep}} with rhs=lmb})
     ) rep

  | TmApp ({lhs=TmApp ({lhs=TmConst ({val=CIter ()}&c),rhs=TmLam l}&a2),rhs=lst}&a1) ->
    normalizeName
      (lam lst.
             k (TmApp {{a1 with lhs= TmApp {{a2 with lhs=TmConst c} with rhs=
             TmLam {l with body=normalize (lam lB. lB) l.body} }} with rhs=lst}))
      lst
  | TmApp ({lhs=TmApp ({lhs=TmConst ({val=CIteri ()}&c),rhs=lmb}&a2),rhs=lst}&a1) ->
    normalizeName
      (lam lst.
             k (TmApp {{a1 with lhs= TmApp {{a2 with lhs=TmConst c} with rhs=lmb}} with rhs=lst}))
      lst
end

lang PBNGraph
  syn Vertex =

  | RandomVarNode {ident:Name,
                    val:Option Expr,
                    color:Int, -- 0:blue (assume), 1:red (stable)
                    dist:Expr, 
                    list:Bool,  --if it belongs to a list
                    plateId:Option Name} --if it belongs to a plate
  | CodeBlockNode {ident:Name,
                    code:Expr,
                    ret:Bool,
                    list:Bool, --if it belongs to a list
                    plateId:Option Name} --if it belongs to a plate
  | ListNode {ident:Name,
              items:[Name],
              dist:Option Expr,
              plateId:Option Name}  --if it belongs to a plate
  | CreateNode {ident:Name,
                item:Name, 
                n:Name,
                dist:Option Expr,
                plateId:Option Name}
  | MultiplexerNode {ident:Name,
                      index:Name,
                      plateId:Option Name} --if it belongs to a plate
  | PlateNode {ident:Name,
               lamVar:[Name], -- new variables introduced
               iter:Name, -- name of the observations to iterate over
               vertices:Set Name, -- name set of vertices a plate contains
               plateId:Option Name}--if it belongs to a plate
  | FoldNode {ident:Name,
               lamVar:[Name], -- new variables introduced
               iter:Name, -- name of the observations to iterate over
               vertices:Set Name, -- name set of vertices a plate contains
               plateId:Option Name,
               ret:Name,
               acc:Name}

  sem cmprVertex (v1:Vertex) =
  | v2 -> cmprVertexH (v1,v2)

  sem cmprVertexH =
  | (RandomVarNode t1, RandomVarNode t2) -> nameCmp t1.ident t2.ident
  | (CodeBlockNode t1, CodeBlockNode t2) -> nameCmp t1.ident t2.ident
  | (ListNode t1, ListNode t2) -> nameCmp t1.ident t2.ident
  | (MultiplexerNode t1, MultiplexerNode t2) -> nameCmp t1.ident t2.ident
  | (PlateNode t1, PlateNode t2) -> nameCmp t1.ident t2.ident
  | (FoldNode t1, FoldNode t2) -> nameCmp t1.ident t2.ident
  | (CreateNode t1, CreateNode t2) -> nameCmp t1.ident t2.ident
  | (t1,t2) -> subi (constructorTag t1) (constructorTag t2)

  sem cmprEdge (e1:(Vertex,Vertex,Label)) =
  | (v1, v2, _) -> let cmprV1 = cmprVertex e1.0 v1 in
                   if eqi cmprV1 0 then cmprVertex e1.1 v2 else cmprV1

  sem getId =
  | RandomVarNode v -> v.ident
  | CodeBlockNode v -> v.ident
  | MultiplexerNode v -> v.ident
  | ListNode v -> v.ident
  | PlateNode v -> v.ident
  | FoldNode v -> v.ident
  | CreateNode v -> v.ident

  sem getDist =
  | RandomVarNode v -> Some (v.dist)
  | _ -> None ()

  sem plateToFold (acc:Name) (ret:Name) =
  | PlateNode p -> FoldNode {ident=p.ident,lamVar=p.lamVar,iter=p.iter,vertices=p.vertices,plateId=p.plateId,acc=acc,ret=ret}

  -- given a multiplexer m and a graph g, returns the list node that is an input to m
  sem inputMultiplexer (g:Digraph Vertex Label) =
  | MultiplexerNode m ->
    let parent = filter (lam v. match v with ListNode _ then true else (match v with CreateNode _ then true else false)) (digraphPredeccessors (MultiplexerNode m) g) in
    get parent 0
  | _ -> error "inputMultiplexer:given vertex is not a multiplexer"

  -- given a multiplexer m and a graph g, returns Some index node to m if it exists otherwise None ()
  sem indexMultiplexer (g:Digraph Vertex Label) =
  | MultiplexerNode m ->
    let parent = filter (lam v. match v with ListNode _ then false else match v with CreateNode _ then false else true) (digraphPredeccessors (MultiplexerNode m) g) in
    if null parent then None () else Some (get parent 0)
 | _ -> error "indexMultiplexer:given vertex is not a multiplexer"

end

-- for debug printing of vertices
recursive
let v2str = use PBNGraph in
  use MExprAst in use MExprPPL in
  lam v.
  match v with CodeBlockNode c then
    let id = c.ident in let ret = if c.ret then " true" else " false" in
    join ["\ncodeb", id.0, (int2string (sym2hash id.1)),"\ncode:",expr2str c.code, "\n",ret, "\n"]
  else match v with RandomVarNode r then
    let id = r.ident in join ["randomv ", id.0 , " ",(int2string (sym2hash id.1)), "color:", if eqi r.color 0 then "blue" else if eqi r.color 1 then "red" else "green" ," dist " , (mexprToString r.dist)]
  else match v with ListNode l then
    let id = l.ident in join ["listnodev ", id.0 , " ",(int2string (sym2hash id.1)),
      foldl (lam acc. lam v. join [acc, " ", v.0 ,":",(int2string (sym2hash v.1)),"\t"]) "" l.items]
  else match v with MultiplexerNode m then
    let id = m.ident in
    join ["muxnode ", id.0 , " ",(int2string (sym2hash id.1)),
      let iid = m.index in (int2string (sym2hash (iid.1)))]
  else match v with PlateNode p then
    let id = p.ident in join ["platenode", id.0, " ",(int2string (sym2hash id.1)),
      foldl (lam acc. lam v. join [acc, "",v.0,":" ,(int2string (sym2hash v.1)),"\t"]) "" (setToSeq p.vertices)]
  else
    never
end

lang ConjugatePrior = CorePPL + MExprAst + MExprPPL + PBNGraph

  -- (d1:likelihood,d2:prior) checks whether d1 and d2 are conjugate
  sem isConjugatePrior =
  | (TmDist ({dist=DBernoulli d1}&t1),TmDist ({dist=DBeta d2}&t2)) -> true
  | (TmDist ({dist=DGaussian d1}&t1),TmDist ({dist=DGaussian d2}&t2)) -> true
  | (TmDist ({dist=DCategorical d1}&t1),TmDist ({dist=DDirichlet d2}&t2)) -> true
  | _ -> false

  -- check if two distributions family is equivalent
  sem eqFamilyDist =
  | (TmDist ({dist=DBernoulli _}&t1),TmDist ({dist=DBernoulli _}&t2) ) -> true
  | (TmDist ({dist=DBeta _}&t1),TmDist ({dist=DBeta _}&t2) ) -> true
  | (TmDist ({dist=DGaussian _}&t1),TmDist ({dist=DGaussian _}&t2) ) -> true
  | (TmDist ({dist=DCategorical _}&t1),TmDist ({dist=DCategorical _}&t2) ) -> true
  | (TmDist ({dist=DDirichlet _}&t1),TmDist ({dist=DDirichlet _}&t2) ) -> true
  | _ -> false

  -- check whether a list consists of rvs with same distribution family
  sem validList (commonDist:Option Expr) =
  | [RandomVarNode t] ++ as -> match commonDist with Some dist1 then
                                match t.dist with dist2 then
                                  (if eqFamilyDist (dist1,dist2) then
                                    validList commonDist as
                                  else None ())
                                else never
                              else validList (Some t.dist) as
  | [] -> commonDist
  | [t] ++ as -> None ()

  sem getParams =
  | TmDist d -> getParamsHelper d.dist
  | _ -> error "not a distribution"

  sem getParamsHelper =
  | DBernoulli d -> utuple_ [d.p]
  | DBeta d -> utuple_ [d.a,d.b]
  | DGaussian d -> utuple_ [d.mu, d.sigma]
  | DCategorical d -> utuple_ [d.p]
  | DDirichlet d -> utuple_ [d.a]

  sem changeParams (id:Name) =
  | TmDist d -> TmDist {d with dist =changeParamsHelper id d.dist}
  | _ -> error "not a distribution"

  sem changeParamsHelper (id:Name) =
  | DBernoulli d -> DBernoulli {d with p= tupleproj_ 0 (nvar_ id) }
  | DBeta d -> DBeta {{d with a=tupleproj_ 0 (nvar_ id) } with b=tupleproj_ 1 (nvar_ id) }
  | DGaussian d -> DGaussian {{d with mu=tupleproj_ 0 (nvar_ id)} with sigma=tupleproj_ 1 (nvar_ id) }
  | DCategorical d -> DCategorical {d with p= tupleproj_ 0 (nvar_ id)}
  | DDirichlet d -> DDirichlet {d with a=tupleproj_ 0 (nvar_ id)}

  -- given the likelihood,the prior and the observartion calculates the posterior
  -- (d1: likelihood, d2: prior)
  sem posterior (obs: Option Expr) (indices:Option (Name,Expr)) (plateId:Option Name) =
  | (TmDist ({dist=DBernoulli d1}&t1),TmDist ({dist=DBeta d2}&t2)) ->
    let val = match obs with Some val then val else never in
    let aName = nameSym "" in
    let bName = nameSym "" in
    let postAlpha = nulet_ aName (if_ val (addf_ d2.a (float_ 1.)) d2.a) in
    let postBeta = nulet_ bName (if_ val d2.b (addf_ d2.b (float_ 1.))) in
    let code =
      match indices with Some (mInd, lInd) then
        if_ (eqi_ (nvar_ mInd) lInd) (bind_ postAlpha postBeta) (bind_ (nulet_ aName d2.a) (nulet_ bName d2.b))
      else ((bind_ postAlpha postBeta)) in
    let tName = nameSym "paramR" in
    let letT = nulet_ tName code in
    let rho = CodeBlockNode {ident=tName, code=letT, ret=false,list=false,plateId=plateId} in
    (rho, TmDist {t2 with dist=DBeta {{d2 with a=(nvar_ aName)} with b= (nvar_ bName)}})
  | (TmDist ({dist=DGaussian d1}&t1),TmDist ({dist=DGaussian d2}&t2) ) ->
    let val = match obs with Some val then val else never in
    let s02 = (mulf_ d2.sigma d2.sigma) in
    let s2 = (mulf_ d1.sigma d1.sigma) in
    let muRHS = addf_ (divf_ d2.mu s02) (divf_ val s2) in
    let muLHS = divf_ (float_ 1.0) (addf_ (divf_ (float_ 1.0) s02) (divf_ (float_ 1.0) s2)) in
    let postMu = mulf_ muRHS muLHS in
    let sigma = divf_ (float_ 1.0) (addf_ (divf_ (float_ 1.0) s02) (divf_ (float_ 1.0) s2)) in
    let postSigma = appf1_ (var_ "externalSqrt") sigma in
    let code =
      match indices with Some (mInd, lInd) then
        if_ (eqi_ (nvar_ mInd) lInd) (utuple_ [postMu, postSigma]) (utuple_ [d2.mu,d2.sigma])
      else (utuple_ [postMu, postSigma]) in
    let tName = nameSym "paramR" in
    let letT = nulet_ tName code in
    let rho = CodeBlockNode {ident=tName, code=letT, ret=false,list=false,plateId=plateId} in
    (rho, TmDist {t2 with dist=DGaussian {{d2 with mu= tupleproj_ 0 (nvar_ tName)} with sigma= tupleproj_ 1 (nvar_ tName)}})
  | (TmDist ({dist=DCategorical d1}&t1),TmDist ({dist=DDirichlet d2}&t2)) ->
    let val = match obs with Some val then val else never in
    let postA = mapi_ ( ulam_ "i" (ulam_ "e" (if_ (eqi_ (var_ "i") val) (addf_ (var_ "e") (float_ 1.0)) (var_ "e")))) d2.a in
    let code =
      match indices with Some (mInd, lInd) then
        if_ (eqi_ (nvar_ mInd) lInd) postA d2.a
      else postA in
    let tName = nameSym "paramR" in
    let letT = nulet_ tName code in
    let rho = CodeBlockNode {ident=tName, code=letT, ret=false,list=false,plateId=plateId} in
    (rho, TmDist {t2 with dist=DDirichlet {d2 with a=nvar_ tName}})
  | _ -> error "posterior:not supported"

  -- input (d1: likelihood, d2: prior)
  -- output (rho:Vertex, q:Expr)
  sem posteriorPredictive (plateId:Option Name) =
  | (TmDist ({dist=DBernoulli d1}&t1),TmDist ({dist=DBeta d2}&t2)) ->
    let postAlpha = d2.a in
    let postBeta = d2.b in
    let postP = divf_ postAlpha (addf_ postAlpha postBeta) in
    let tName = nameSym "param" in
    let letT = nulet_ tName postP in
    let rho = CodeBlockNode {ident=tName, code=letT, ret=false,list=false,plateId=plateId} in
    (rho,TmDist {t1 with dist=DBernoulli {d1 with p= nvar_ tName}})

  | (TmDist ({dist=DGaussian d1}&t1),TmDist ({dist=DGaussian d2}&t2) ) ->
    let s02 = (mulf_ d2.sigma d2.sigma) in
    let s2 = (mulf_ d1.sigma d1.sigma) in
    let postMu = mulf_ s02 (divf_ d2.mu s02) in
    let postSigma = appf1_ (var_ "externalSqrt") (addf_ s02 s2) in
    let tName = nameSym "param" in
    let letT = nulet_ tName (utuple_ [postMu, postSigma]) in
    let rho = CodeBlockNode {ident=tName, code=letT, ret=false,list=false,plateId=plateId} in
    (rho, TmDist {t1 with dist=DGaussian {{d1 with mu= tupleproj_ 0 (nvar_ tName)} with sigma= tupleproj_ 1 (nvar_ tName)}})

  | (TmDist ({dist=DCategorical d1}&t1),TmDist ({dist=DDirichlet d2}&t2)) ->
    let sumai = foldl_ (ulam_ "acc" (ulam_ "i" (addf_ (var_ "acc") (var_ "i")))) (float_ 0.0) (d2.a) in
    let postA = map_ (ulam_ "ai" (divf_ (var_ "ai") sumai)) d2.a in
    let tName = nameSym "param" in
    let letT = nulet_ tName postA in
    let rho = CodeBlockNode {ident=tName, code=letT, ret=false,list=false,plateId=plateId} in
    (rho, TmDist {t1 with dist=DCategorical {d1 with p=nvar_ tName}})
  | _ -> error "posteriorPredictive:not supported"

  sem listParam (cbId:Name)=
  | TmDist ({dist=DBernoulli d1}&t1) ->
    TmDist {t1 with dist=DBernoulli {d1 with p= nvar_ cbId}}

  | TmDist ({dist=DGaussian d1}&t1)->
    TmDist {t1 with dist=DGaussian {{d1 with mu= tupleproj_ 0 (nvar_ cbId)} with sigma= tupleproj_ 1 (nvar_ cbId)}}
  | TmDist ({dist=DCategorical d1}&t1)->
    TmDist {t1 with dist=DCategorical {d1 with p=nvar_ cbId}}

  | TmDist ({dist=DBeta d1}&t1) ->
    TmDist {t1 with dist=DBeta {{d1 with a= tupleproj_ 0 (nvar_ cbId)} with b = tupleproj_ 1 (nvar_ cbId)}}

  | TmDist ({dist=DDirichlet d1}&t1)->
    TmDist {t1 with dist=DDirichlet {d1 with a=nvar_ cbId}}
  | _ -> error "listParam:not supported"
end

-- Language fragment to create PBN from a given program
lang StaticAnalyzer = PBNGraph + MExprAst + MExprPPL + ConjugatePrior
  -- m2: a mapping from a variable name to its corresponding vertex id. Several let bindings can corresspond to a single code block vertex
  type CreateAcc = {
    m2:Map Name Name,
    env:Map Name Expr,
    blockIdent:Option Name,
    plateV:Option (Name,(Set Name)),
    vertexId:Option Name,
    inList:Bool,
    isRet:Bool
  }

  -- create edges based on the dependencies of vertex v
  sem createEdges (v:Vertex) (pbn:PBN) (cAcc:CreateAcc) (edges:Set (Vertex,Vertex,Label)) =
  | TmVar t ->
    -- find the corresponding vertex ident from the variable ident
    match mapLookup t.ident cAcc.m2 with Some vertexId then
      let vFrom:Vertex = mapLookupOrElse (lam. error "createEdges:Lookup failed") vertexId pbn.m in
      -- create an edge to the source vertex from the vertex that it depends on
      if digraphEqv pbn.g vFrom v then edges --check if they are in the same codeblock if so no need to create an edge
      else setInsert (vFrom, v, 0) edges
    else edges -- if cannot find id then it must be created with lambda scoping so ignore
  | t -> sfold_Expr_Expr (createEdges v pbn cAcc) edges t

  -- finds the random variable identities within an expresiion
  sem findRandomVariables (m:Map Name Vertex) (idents:[Name]) =
  | TmVar t -> match mapLookup t.ident m with Some (RandomVarNode _) then cons t.ident idents else idents
  | t -> sfold_Expr_Expr (findRandomVariables m) idents t

  sem plateAddVertex (id:Name) =
  | Some (idp,p) -> Some (idp, setInsert id p)
  | _ -> None ()

  sem createCodeBlock (m1:Map Name Vertex) (list:Bool) (plate:Option Name) (t:Expr) (isRet:Bool) =
  | (Some id, Some bid) -> let vertex = mapLookupOrElse (lam. error "Lookup failed") bid m1 in
                           match vertex with CodeBlockNode c then
                             let v = CodeBlockNode {c with code=bind_ c.code (nulet_ id t)} in
                             (v,c.ident)
                           else never
  | (Some id, None ()) -> let ident = nameSym "" in
                            let v = CodeBlockNode {ident=ident,code=(nulet_ id t),ret=false,list=list, plateId=plate} in
                            (v,ident)
  | _ -> let ident = nameSym "" in
         let v = CodeBlockNode {ident=ident,code=t,ret=isRet,list=false, plateId=plate} in
         (v,ident)

  -- given vertex, its id for pbn.m and id for cAcc.m2 and expr for env
  sem addVertex (pbn:PBN) (cAcc:CreateAcc) = 
  | (v,id,id2,expr) -> 
    let g = digraphAddUpdateVertex v pbn.g in
    let m1 = mapInsert id v pbn.m in
    let m2 = mapInsert id id2 cAcc.m2 in
    let env = mapInsert id expr cAcc.env in
    let pV = plateAddVertex id cAcc.plateV in
    ({{pbn with g=g} with m=m1}, {{{{cAcc with m2=m2} with env=env} with blockIdent=None ()} with plateV=pV})

  sem createPBN (pbn:PBN) (cAcc:CreateAcc) =
  | TmLet t ->
    let res = createPBNH pbn {cAcc with vertexId=(Some t.ident)} t.body in
    createPBN res.0 res.1 t.inexpr
  | (TmRecLets {inexpr=inexpr} | TmExt {inexpr=inexpr} | TmType {inexpr=inexpr} |TmConDef {inexpr=inexpr})& t ->
    let res = createPBNH pbn cAcc t in
    createPBN res.0 res.1 inexpr
  | t -> createPBNH pbn {cAcc with isRet=true} t


-- list:if items in a list create nodes
sem createPBNH (pbn:PBN) (cAcc:CreateAcc) =
  | (TmAssume {dist=dist} | TmObserve {dist=dist}) & t ->
    -- get the ident if it comes from a let expression
    let id = match cAcc.vertexId with Some id then id else nameSym "" in
    -- if an observe then get its value
    let val = match t with TmObserve t then Some t.value else None () in
    -- get the plate id if it is in a plate
    let pid = match cAcc.plateV with Some (id,_) then Some id else None () in
    -- create the vertex
    let v = RandomVarNode {ident = id, val = val, color = 0, dist = dist, list=cAcc.inList, plateId=pid} in
    -- add the vertex to the graph and to the context
    let res = addVertex pbn cAcc (v,id,id,t) in
    match res with (pbn,cAcc) in
    let res = 
      --if it is a return then also create a codeblock that returns created random variable
      if cAcc.isRet then
        let cb = createCodeBlock pbn.m false pid (nvar_ id) true (None(),None()) in
        addVertex pbn cAcc (cb.0,cb.1,cb.1,nvar_ id)
      else (pbn,cAcc) in
    match res with (pbn,cAcc) in
    -- if it is an observe, add it to targets
    let targets = match t with TmObserve _ then cons id pbn.targets else pbn.targets in
    -- create edges to the created random variable node v from the nodes that it depends on
    let edges = setToSeq (createEdges v pbn cAcc (setEmpty cmprEdge) t) in
    let g = digraphAddEdges edges pbn.g in
    ({{pbn with targets=targets} with g=g},cAcc,Some v)
  | TmVar t ->
    if cAcc.isRet then createPBNGeneric pbn cAcc (TmVar t)
    else
      -- get the ident if it comes from a let expression
      let id = match cAcc.vertexId with Some id then id else never in
      match pbn with {g=g,m=m1,targets=targets} in
      -- get the vertex id varible mapped to in cAcc.m2
      let id2 = mapLookupOrElse (lam. error "Lookup failed") t.ident cAcc.m2 in
      -- get the vertex
      let v = mapLookupOrElse (lam. error "") id2 m1 in
      -- now, id refers to the same vertex
      let m1 = mapInsert id v m1 in
      -- add that mapping from id to the vertex id to cAcc.m2
      let m2 = mapInsert id id2 cAcc.m2 in
      -- add the expression for id to env
      let env = mapInsert id (nvar_ id2) cAcc.env in
      -- a list can only consists of random variable nodes
      let v = if cAcc.inList then match v with (RandomVarNode _) then Some v else None () else Some v in
      ({pbn with m=m1},{{cAcc with m2=m2} with env=env},v)
  | TmSeq t ->
    if cAcc.inList then (pbn,cAcc,None ()) else
    -- get the ident if it comes from a let expression
    let id = match cAcc.vertexId with Some id then id else nameSym "" in
    -- get the plate ident if it is in a plate
    let pid = match cAcc.plateV with Some (id,_) then Some id else None () in
    let accP = {{{cAcc with blockIdent=None()} with inList=true} with isRet=false} in
    let res = mapAccumL (lam acc. lam e.
                    let id = match e with TmVar t then Some t.ident else None () in
                    let res = createPBNH acc.0 {acc.1 with vertexId=id} e in
                    ((res.0,res.1),res.2)) (pbn,accP) t.tms in
    match res with ((pbnV,cAccV),items) in
    let nvalidL = any (lam v. match v with None () then true else false) items in
    let valL =
      if nvalidL then None ()
      else
        let tms = map (lam v. match v with Some v then v else never) items in
        let ids = map getId tms in
        let dist = validList (None ()) tms in
        match dist with Some _ then Some (dist,ids) else None ()
    in
    let res = 
      match valL with Some (dist,ids) then
        let v = (ListNode {ident=id, items=ids,dist=dist,plateId=pid},id) in
        (pbnV,cAccV,v)
      else
        let v = createCodeBlock pbn.m cAcc.inList pid (nulet_ id (TmSeq t)) false (None (),cAcc.blockIdent) in
        (pbn,cAcc,v)
    in
    match res with (pbn,cAcc,v) in
    let res= addVertex pbn cAcc (v.0,id,v.1,TmSeq t) in
    match res with (pbn,cAcc) in
    let edges = setToSeq (createEdges v.0 pbn cAcc (setEmpty cmprEdge) (TmSeq t)) in
    let g = digraphMaybeAddEdges edges pbn.g in
    ({pbn with g=g},cAcc,Some v.0)
   --restrictive int
  | TmApp ({lhs=(TmApp ({lhs=TmConst ({val=CCreate()}&c),rhs=TmVar rep})&a1),rhs=TmLam l}&a2) ->
    if cAcc.inList then (pbn,cAcc,None ()) else
    let id = match cAcc.vertexId with Some id then id else nameSym "" in
    let pid = match cAcc.plateV with Some (id,_) then Some id else None () in
    let nvalidL = match l.body with TmAssume _ then false else match l.body with TmObserve _ then false else true in
    let res =
      if nvalidL then
        let v = createCodeBlock pbn.m cAcc.inList pid (nulet_ id (TmApp a2)) false (None (),cAcc.blockIdent) in
        (pbn,cAcc,v)
    else
      let env = mapInsert l.ident (nvar_ l.ident) cAcc.env in
      let accH = {{{{cAcc with blockIdent=None()} with vertexId=None()} with inList=true} with isRet=false} in
      let res = createPBNH pbn accH l.body in
      --g targets m1 m2 (mapInsert l.ident (nvar_ l.ident) env) (None ()) pres.0 (None ()) true false l.body in
      match res with (pbn,cAcc,Some item) in
      let itemId = getId item in
      let dist = getDist item in
      let v = (CreateNode {ident=id,item=itemId,n=rep.ident,dist=dist,plateId=pid},id) in
      (pbn,cAcc,v)
    in
    match res with (pbn,cAcc,v) in
    let res = addVertex pbn cAcc (v.0,id,v.1,TmApp a2) in
    match res with (pbn,cAcc) in
    let edges = setToSeq (createEdges v.0 pbn cAcc (setEmpty cmprEdge) (TmApp a2)) in
    let g = digraphMaybeAddEdges edges pbn.g in
    ({pbn with g=g},{cAcc with blockIdent=None()},Some v.0)
 | TmApp ({lhs=(TmApp ({lhs=TmConst ({val=CGet ()}&c),rhs=TmVar seq})&t2),rhs=TmVar ind}&a) ->
    if cAcc.inList then (pbn,cAcc,None ()) else
    let id = match cAcc.vertexId with Some id then id else nameSym "" in
    let pid = match cAcc.plateV with Some (id,p) then Some id else None () in
    match pbn with {g=g,m=m1,targets=targets} in
    let v =
      -- if there is no such list node created, create a codeblock
      match mapLookup seq.ident m1 with None () then
        createCodeBlock m1 cAcc.inList pid (TmApp a) cAcc.isRet (cAcc.vertexId,cAcc.blockIdent)
      else -- there is a list node created which consists of valid items
        let seqV = mapLookupOrElse (lam. error "Get:Lookup failed") seq.ident m1 in
        let m = MultiplexerNode {ident=id,index=ind.ident,plateId=pid} in
        (m,id)
    in
    let res = addVertex pbn cAcc (v.0,id,v.1,(TmApp a)) in
    match res with (pbn,cAcc) in
    let edges = setToSeq (createEdges v.0 pbn cAcc (setEmpty cmprEdge) (TmApp a)) in
    let g = digraphAddEdges edges pbn.g in
    ({pbn with g=g}, {cAcc with blockIdent=None()}, Some v.0)
 | TmApp ({lhs=(TmApp ({lhs=TmConst ({val=CIter()}&c),rhs=TmLam l})&a1),rhs=TmVar lst}&a2) ->
    createPlate pbn cAcc [l.ident] l.body lst.ident (TmApp a2)
  | TmApp ({lhs=(TmApp ({lhs=TmConst ({val=CIteri()}&c),rhs=TmLam ({body=TmLam l2}&l1)})&a1),rhs=TmVar lst}&a2) ->
    createPlate pbn cAcc [l1.ident,l2.ident] l2.body lst.ident (TmApp a2)
  | t-> createPBNGeneric pbn cAcc t

  sem createPlate (pbn:PBN) (cAcc:CreateAcc) (idents:[Name]) (body:Expr) (lstId:Name) =
  | t -> 
    if cAcc.inList then (pbn,cAcc,None ()) else
    let id = match cAcc.vertexId with Some id then id else nameSym "" in
    let env = foldl (lam acc. lam i. mapInsert i (nvar_ i) acc) cAcc.env idents in
    let res = createPBN pbn {{{cAcc with env=env} with blockIdent=None()} with plateV= (Some (id,(setEmpty nameCmp)))} body in
    match res with (pbnB,cAccB,_) in
    let vertices = match cAccB.plateV with Some (id,v) then v else never in
    let pid = match cAcc.plateV with Some (id,p) then Some id else None () in
    let v = PlateNode {ident=id, lamVar=idents,iter=lstId, vertices=vertices,plateId=pid} in
    let res = --if it is a return then also create a codeblock that returns created variable
      if cAcc.isRet then
        let idcb = nameSym "" in
        let cb = CodeBlockNode {ident=idcb,code=nvar_ id,ret=true,list=false,plateId=pid} in
        addVertex pbnB {cAccB with plateV=cAcc.plateV} (cb,idcb,idcb,nvar_ id)
      else (pbnB,{cAccB with plateV=cAcc.plateV}) in
    match res with (pbn,cAcc) in
    let res = addVertex pbn cAcc (v,id,id,body) in
    match res with (pbn,cAcc) in
    let edges = setToSeq (createEdges v pbn cAcc (setEmpty cmprEdge) (nvar_ lstId)) in
    let g = digraphAddEdges edges pbn.g in
    ({pbn with g=g},cAcc, Some v)

  sem createPBNGeneric (pbn:PBN) (cAcc:CreateAcc) =
  | t ->
    if cAcc.inList then (pbn,cAcc,None ()) else
    let pid = match cAcc.plateV with Some (id,p) then Some id else None () in
    let v = createCodeBlock pbn.m false pid t cAcc.isRet (cAcc.vertexId,cAcc.blockIdent) in
    let id = match cAcc.vertexId with Some id then id else v.1 in
    let res = addVertex pbn cAcc (v.0,id,v.1,t) in
    match res with (pbn,cAcc) in
    let edges = setToSeq (createEdges v.0 pbn cAcc (setEmpty cmprEdge) t) in
    let g = digraphMaybeAddEdges edges pbn.g in
    let targets = findRandomVariables pbn.m pbn.targets t in
    ({{pbn with g=g} with targets=targets},cAcc,Some v.0)

end

lang Reconstructor = PBNGraph + MExprAst + MExprPPL
 
   sem recreateVertex (vRet:Option Vertex) (g:Digraph Vertex Label) (m:Map Name Vertex) (plate:Bool) (plateVertices:Map Name [Vertex])=
  | [CodeBlockNode t] ++ as -> 
                  let pl = match t.plateId with Some _ then true else false in 
  								if and (not plate) pl then 
  									recreateVertex vRet g m plate plateVertices as 
  								else bind_ t.code (recreateVertex vRet g m plate plateVertices as)
  | [RandomVarNode v] ++ as ->
                        let pl = match v.plateId with Some _ then true else false in 
                        if and (not plate) (pl) then
                         recreateVertex vRet g m false plateVertices as
                        else
                         match v.val with Some val then -- observe
                          TmLet { ident = v.ident,
                                tyBody = tyunknown_,
                                body = (TmObserve {dist=v.dist, value=val,ty=tyunknown_, info = NoInfo ()}),
                                inexpr=(recreateVertex vRet g m plate plateVertices as),
                                ty=tyunknown_,
                                info = NoInfo (),
                                tyAnnot = tyunknown_}
                        else
                          TmLet { ident = v.ident,
                                tyBody = tyunknown_,
                                body = (TmAssume {dist=v.dist, ty=tyunknown_, info = NoInfo ()}),
                                inexpr=(recreateVertex vRet g m plate plateVertices as),
                                ty=tyunknown_,
                                info= NoInfo (),
                                tyAnnot = tyunknown_}
  | [ListNode l] ++ as -> TmLet { ident = l.ident,
                                  tyBody = tyunknown_,
                                  body = (TmSeq {tms=(map (lam i. nvar_ i) l.items), ty=tyunknown_,info=NoInfo ()}),
                                  inexpr =(recreateVertex vRet g m plate plateVertices as),
                                  ty = tyunknown_,
                                  info = NoInfo (),
                                  tyAnnot = tyunknown_}
  | [CreateNode c] ++ as -> TmLet { ident = c.ident,
                                  tyBody = tyunknown_,
                                  body = (create_ (nvar_ c.n) (ulam_ "" (nvar_ c.item))),
                                  inexpr =(recreateVertex vRet g m plate plateVertices as),
                                  ty = tyunknown_,
                                  info = NoInfo (),
                                  tyAnnot = tyunknown_}

  | [MultiplexerNode mu] ++ as ->  let listnode = inputMultiplexer g (MultiplexerNode mu) in
                                    match listnode with ListNode l then
                                      TmLet { ident = mu.ident,
                                        tyBody = tyunknown_,
                                        body = get_ (nvar_ l.ident) (nvar_ mu.index),
                                        inexpr=(recreateVertex vRet g m plate plateVertices as),
                                        ty=tyunknown_,
                                        info= NoInfo (),
                                        tyAnnot = tyunknown_}
                                    else never
  | [PlateNode p] ++ as ->
     let pl = match p.plateId with Some _ then true else false in
     if and (not plate) pl then recreateVertex vRet g m false plateVertices as else
      let vItems = mapLookupOrElse (lam. error "Recreate-plate:Lookup failed") p.ident plateVertices in
      let vPRet = get (filter (lam v. match v with CodeBlockNode c then c.ret else false) vItems) 0 in
      let vItems = filter (lam v. match v with CodeBlockNode c then not c.ret else true) vItems in
      let bdyIn = (recreateVertex (Some vPRet) g m true plateVertices vItems) in
      let bdy = foldl (lam acc. lam l. nulam_ l acc) bdyIn (reverse p.lamVar) in
      let tlet =
        match length p.lamVar with 1 then
          TmLet { ident = p.ident,
                                  tyBody = tyunknown_,
                                  body = (iter_
                                    (nulam_ (get p.lamVar 0)
                                      (recreateVertex (Some vPRet) g m true plateVertices vItems)) (nvar_ p.iter)),
                                  inexpr =(recreateVertex vRet g m false plateVertices as),
                                  ty = tyunknown_,
                                  info = NoInfo (),
                                  tyAnnot = tyunknown_}
        else
          TmLet { ident = p.ident,
                                  tyBody = tyunknown_,
                                  body = (iteri_ (nulam_ (get p.lamVar 0) (nulam_ (get p.lamVar 1)
                                      (recreateVertex (Some vPRet) g m true plateVertices vItems))) (nvar_ p.iter)),
                                  inexpr =(recreateVertex vRet g m false plateVertices as),
                                  ty = tyunknown_,
                                  info = NoInfo (),
                                  tyAnnot = tyunknown_} in tlet  
  | [FoldNode f] ++ as ->
      let pl = match f.plateId with Some _ then true else false in 
                        if and (not plate) pl then
                         recreateVertex vRet g m false plateVertices as
                        else
  let vItems = mapLookupOrElse (lam. error "Recreate-plate:Lookup failed") f.ident plateVertices in
  let vPRet = get (filter (lam v. match v with CodeBlockNode c then c.ret else false) vItems) 0 in
  let vItems = filter (lam v. match v with CodeBlockNode c then not c.ret else true) vItems in
  let bdyIn = (recreateVertex (Some vPRet) g m true plateVertices vItems) in
  let bdy = foldl (lam acc. lam l. nulam_ l acc) bdyIn (reverse f.lamVar) in
  let ret = f.ret in
  let accName = f.acc in
    TmLet { ident = ret,
                                  tyBody = tyunknown_,
                                  body = foldl_ bdy (nvar_ accName) (nvar_ f.iter),
                                  inexpr =(recreateVertex vRet g m false plateVertices as),
                                  ty = tyunknown_,
                                  info = NoInfo (),
                                  tyAnnot = tyunknown_}


  | [] -> match vRet with Some (CodeBlockNode c) then c.code else error "no return"

end

let debug = true
lang PBNTransformer = StaticAnalyzer + ConjugatePrior

type TAcc =
{
  qDist:QDist,
  pqDist:PQDist
}

sem handleMultipleParents (pbn:PBN) (accT:TAcc) =
| t ->

    -- get its random variable or list parents
    let parents = filter (lam v. match v with RandomVarNode v then eqi v.color 0 else
                            match v with MultiplexerNode m then
                              match inputMultiplexer pbn.g v with ListNode l then true
                              else false
                            else false) (digraphPredeccessors t pbn.g) in
    if null parents then (pbn, accT, None ())
    else
      let parent = get parents 0 in
      let res = foldl (lam acc. lam p.
        match p with RandomVarNode _ then
          let res = graft acc.0 acc.1 p in
          reorder res.0 res.1 p
        else match p with MultiplexerNode m then
          let pbn = acc.0 in
          let lst = inputMultiplexer pbn.g p in
          match lst with ListNode l then
            foldl (lam acc. lam e.
              let pbn = acc.1 in
              let e = mapLookupOrElse (lam. error "handle:Lookup failed") e pbn.m in
              reorder acc.0 acc.1 e) acc l.items
          else never
        else never
      ) (pbn,accT) (tail parents) in
      (res.0,res.1,Some parent)

sem graft (pbn:PBN) (accT:TAcc) =
| (RandomVarNode v) & t ->
  -- if t is not a random variable then do not change
    (if debug then print (join ["Graft(", v2str t,")\n"]) else ());
    -- if t is marginalized
    if mapMem v.ident accT.qDist then
      -- get its children
      let children = digraphSuccessors t pbn.g in
      -- get its marginalized random variable child if any
      let child = filter (lam u. match u with RandomVarNode u then mapMem u.ident accT.qDist else false) children in
      -- if it does not have a marginalized child, then do nothing and return the graph
      (if null child then (pbn,accT)
      else
        -- if it has more than one marginalized child, then there is something wrong
        (if not (eqi (length child) 1) then error "Graft: can only have one marginalized child"
         else -- if it has one marginalized child
           let child = get child 0 in -- get that child
          (if debug then print (join ["child node ", (v2str child), " to be pruned\n"]) else ());
           -- prune the child so t will become the terminal node on its marginalized path
          prune pbn accT child))
    -- if t is not marginalized
    else
      (if debug then print "Graft: RV t is not marginalized\n" else ());
      let res = handleMultipleParents pbn accT t in
      let pbn = res.0 in
      let accT = res.1 in
      let parent = res.2 in
      match parent with None () then marginalize pbn accT
      else
        match parent with Some parent then
          match parent with RandomVarNode p then
            (if debug then print (join ["Graft:parent ",v2str parent,"\nchild ",v2str t ,"\n"]) else ());
             (if debug then print "Graft: parent of t is a rv\n" else ());
              let res = graft pbn accT parent in
              marginalize res.0 res.1 t
          else -- if its parent is from a list then
            match parent with MultiplexerNode _ then
              (if debug then print "Graft: t's parent comes from a list\n" else ());
              let l = inputMultiplexer pbn.g parent in
              let items = match l with ListNode l then
                filter (lam e. let e = mapLookupOrElse (lam. error "Marginalize:Lookup failed") e pbn.m in
              match e with RandomVarNode r then eqi r.color 0 else false) l.items
              else never in
              let res =
                match l with ListNode l then
                  foldl (lam acc. lam e.
                    let e = mapLookupOrElse (lam. error "Marginalize:Lookup failed") e pbn.m in
                    graft acc.0 acc.1 e
                   ) (pbn,accT) items
                else never in
              marginalize res.0 res.1 t
            else never -- no other case
          else never

  sem prune (pbn:PBN) (accT:TAcc) =
  | (RandomVarNode v) & t ->
    -- pruned RV should already be marginalized
    (match mapMem v.ident accT.qDist with false then error "Prune: t is not marginalized"
    else
      -- get its marginalized child
      let child = filter (lam u. match u with RandomVarNode u then mapMem u.ident accT.qDist else false) (digraphSuccessors t pbn.g) in
      -- if it does not have a marginalized child then reorder it.
      (if null child then reorder pbn accT t
      else
        match eqi (length child) 1 with false then error "Prune: t has more than one marginalized child" else
          -- if it has a marginalized child then prune it first.
          let res = prune pbn accT (get child 0) in
          reorder res.0 res.1 t))

  sem marginalize (pbn:PBN) (accT:TAcc) =
  | _ -> never


  sem reorder (pbn:PBN) (accT:TAcc) =
  | _ -> never

end

let modifiedBFS : all v. all l. v -> v -> Digraph v l -> Bool
  = lam source. lam dst. lam g.
  recursive let work = lam fs. lam level. lam dist:Map v Int. lam u.
    if null fs then u else
    match
      foldl (lam acc:([v], Map v Int,Bool). lam f.
        foldl (lam acc:([v], Map v Int,Bool). lam v.
          if mapMem v acc.1 then
            if digraphEqv g dst v then
              (acc.0,acc.1, false)
            else acc
          else (cons v acc.0, mapInsert v level acc.1,u)
        ) acc (digraphSuccessors f g)) ([],dist,u) fs
      with (ns, dist, u) then
        if not u then u
        else
          work ns (addi level 1) dist u
      else never
    in
    work [source] 1 (mapInsert source 0 (mapEmpty (digraphCmpv g))) true

let getRoots = lam g:Digraph Vertex Label.
  let vertices = digraphVertices g in
  filter (lam v. null (digraphEdgesTo v g)) vertices


let modifyGraph = use StaticAnalyzer in
  lam g:Digraph Vertex Label. lam m:Map Name Vertex.
  let lists = filter (lam v. match v with ListNode _ then true else false) (digraphVertices g) in
  let g = foldl (lam g. lam l.
          match l with ListNode r then
            foldl (lam g:Digraph Vertex Label. lam id:Name.
                    let i = mapLookupOrElse (lam. error "modify:Lookup failed") id m in
                    let edges = digraphEdgesTo i g in
                    digraphMaybeAddEdges (map (lam e. (e.0,l,e.2)) edges) g) g r.items else never) g lists in
let plates = filter (lam v. match v with PlateNode _ then true else false) (digraphVertices g) in
foldl (lam g. lam pl.
  match pl with PlateNode p then
    foldl (lam g. lam id.
      let i = mapLookupOrElse (lam. error "modify:Lookup failed") id m in
      let edges = digraphEdgesTo i g in
      digraphMaybeAddEdges (map (lam e. (e.0,pl,e.2)) edges) g) g (setToSeq p.vertices) else never) g plates

let emptyCreateAcc =
  let emptyM = (lam. mapEmpty nameCmp) in
  {m2=(emptyM ()),env=(emptyM ()),blockIdent=(None ()), plateV=(None ()),vertexId=None (),inList=false,isRet=false}
-- a mapping of types for each function
-- name:create --
let create = lam prog:Expr.
  use StaticAnalyzer in
  let emptyG = digraphEmpty cmprVertex eqi in
  let emptyM = (lam. mapEmpty nameCmp) in
  createPBN {g=emptyG,targets=[],m=(emptyM ())} emptyCreateAcc prog

let transformPBN = lam pbn:PBN.
  use ConjugatePrior in
  let tAcc = {qDist=mapEmpty nameCmp,qpDist=mapEmpty nameCmp} in 
  --let qpDist = mapEmpty nameCmp in
  if null pbn.targets then (pbn, tAcc)
  else
    let roots = getRoots pbn.g in
    (if debug then print "Root nodes:\n";iter (lam r. print (join [(v2str r),"\n"])) roots else ());
    (pbn, tAcc)
/-
  -- fold the graph over targets
  -- res.0 : marginalized distributions
  -- res.1 : transformed graph
  let res:(Map Name Expr, Digraph Vertex Label,Map Name Vertex) = foldl (lam acc:(Map Name Expr,Digraph Vertex Label,Map Name Vertex). lam t.
  let qDist = acc.0 in
  let g = acc.1 in
  let m = acc.2 in
  let t = get (filter (lam v. digraphEqv g v t) (digraphVertices g)) 0 in
  let graftRes:PBN = graft qDist g m t in
  let qDist = graftRes.0 in
  /-print "\n qDIST\n";
  iter (lam b. print (join [let id= b.0 in id.0," ",  (expr2str b.1), "\n"])) (mapBindings qDist);
  print "\n GRAPH\n";
  digraphPrintDot graftRes.1 v2str int2string;
  print "\n\n";-/
 let t = get (filter (lam v. digraphEqv graftRes.1 v t) (digraphVertices graftRes.1)) 0 in
  let reorderRes:PBN = reorder graftRes.0 graftRes.1 graftRes.2 t in
  reorderRes
  ) (qDist, g, m) targets in
  res-/

let recreate = lam pbn:PBN.
  use Reconstructor in
  let g = modifyGraph pbn.g pbn.m in
  let order = digraphTopologicalOrder g in
  let vRet = filter (lam v.match v with CodeBlockNode c then let np = match c.plateId with Some _ then false else true in and c.ret np else false) order in
  let plates = filter (lam e. match e with PlateNode _ then true else false) order in
  let plateVertices = foldl (lam mp. lam p.
    match p with PlateNode p then
      let orderedV = filter (lam e. let id = getId e in setMem id p.vertices) order in
      mapInsert p.ident orderedV mp
    else never
    ) (mapEmpty nameCmp) plates in
  let order = filter (lam v. match v with CodeBlockNode c then not c.ret else true) order in
  recreateVertex (Some (get vRet 0)) pbn.g pbn.m false plateVertices order

let transformM = lam model:Expr.
  use ConjugatePrior in
  print (mexprToString model);
  let res = create model in
  match res with (pbn,cAcc,_) in
  let targets = map (lam i. mapLookupOrElse (lam. error "target:Lookup failed") i pbn.m) (pbn.targets) in
  let targetObserves = filter (lam v. match v with RandomVarNode v then (match v.val with Some _ then true else false) else false) targets in
  let targets = filter (lam v. match v with RandomVarNode v then (match v.val with Some _ then false else true) else true) targets in
  let targets = (concat targetObserves targets) in
  let targetIds = map getId targets in
  (if debug then print "Target nodes:\n";iter (lam r. print (join [(v2str r),"\n"])) targets else ());
  print "\nTRANSFORM PBN\n";
  let res = transformPBN {pbn with targets=targetIds} in
  let pbn = res.0 in
  let tAcc = res.1 in
  print "\nRECREATE\n";
  let rProg = recreate pbn in
  --let rProg = recreate g m1 in
  rProg

lang Transformation = ConjugatePrior + MExprPPLStaticDelayedANF

  sem isAstLetBinding =
    | TmLet t -> match t.inexpr with TmLet t2 then
                      (print (expr2str (TmLet t)));isLastLetBinding t2.inexpr
                    else false
    | TmRecLets t -> false
    | TmConDef t -> false
    | TmType t -> false
    | TmExt t -> false
    | _ -> true

  sem isLastLetBinding =
    | TmLet t -> false
    | TmRecLets t -> false
    | TmConDef t -> false
    | TmType t -> false
    | TmExt t -> false
    | _ -> true

  sem transform =
  | prog -> transformM (normalizeTerm prog)
end

mexpr
use Transformation in

let list1 =
  bindall_
  [ ulet_ "l1" (seq_ [(assume_ (gaussian_ (float_ 0.0) (float_ 1.0)))
  , (assume_ (gaussian_ (float_ 2.0) (float_ 1.0)))])
  , ulet_ "mu" (get_ (var_ "l1") (int_ 0))
  , var_ "mu"
  ] in

let list2 =
  bindall_
  [ ulet_ "l1" (seq_ [(assume_ (gaussian_ (float_ 0.0) (float_ 1.0)))
  , (assume_ (beta_ (float_ 2.0) (float_ 1.0)))])
  , ulet_ "mu" (get_ (var_ "l1") (int_ 0))
  , var_ "mu"
  ] in

let case1 =
  bindall_
  [ ulet_ "x" (assume_ (beta_ (float_ 10.0) (float_ 5.0)))
  , ulet_ "" (observe_ true_ (bern_ (var_ "x")))
  , var_ "x"
  ] in

let case11 =
  bindall_
  [ ulet_ "x" (assume_ (beta_ (float_ 10.0) (float_ 5.0)))
  , ulet_ "y" (assume_ (bern_ (var_ "x")))
  , var_ "y"
  ] in

let case2 =
  bindall_
  [  ulet_ "z" (float_ 3.0)
  , ulet_ "f" (ulam_ "x" (addi_  (var_ "x") (float_ 10.0)))

   ,ulet_ "a" (assume_ (beta_  (var_ "z") (float_ 10.0)))
  , ulet_ "" (observe_ true_ (bern_ (var_ "a")))
  , var_ "a"
  ] in

let case3 =
  bindall_
  [ ulet_ "x" (assume_ (beta_ (float_ 10.0) (float_ 10.0)))
  , ulet_ "y" (assume_ (bern_ (var_ "x")))
  , var_ "y"
  ] in

let case4 =
  bindall_
  [ --next_ ("externalSqrt", gensym()) (false_) tyunknown_
   ulet_ "z" (float_ 10.0)
  , ulet_ "x" (assume_ (beta_ (var_ "z") (var_ "z")))
  , ulet_ "y" (assume_ (bern_ (var_ "x")))
  , var_ "y"
  ] in
let case4_1 = bindall_
  [ --next_ ("externalSqrt", gensym()) (false_) tyunknown_
   ulet_ "x" (assume_ (gaussian_ (float_ 0.0) (float_ 1.0)))
  , ulet_ "" (observe_ (float_ 1.0) (gaussian_ (var_ "x") (float_ 1.0)))
  , var_ "x"
  ] in

let case5 =
  bindall_
  [ ulet_ "z" (float_ 10.0)
  , ulet_ "x" (assume_ (gaussian_ (float_ 0.0) (var_ "z")))
  , ulet_ "y" (assume_ (gaussian_ (var_ "x") (var_ "z")))
  , var_ "y"
  ] in

let case6 =
  bindall_
  [ ulet_ "z" (float_ 10.0)
  , ulet_ "x" (assume_ (beta_ (var_ "z") (var_ "z")))
  , ulet_ "y" (assume_ (bern_ (var_ "x")))
  , var_ "y"
  ] in

let case7 =
  bindall_
  [ --ulet_ "a" (assume_ (gaussian_ (float_ 0.0) (float_ 1.0)))
  ulet_ "a" (float_ 2.0)
  , ulet_ "lst" (seq_ [(assume_ (gaussian_ (var_ "a") (float_ 1.0)))
  ,  (assume_ (gaussian_ (var_ "b") (float_ 1.0)))
  , (assume_ (gaussian_ (var_ "c") (float_ 1.0)))])
  , var_ "d"
  ] in
let case7_2 =
  bindall_
  [  ulet_ "x" (seq_ [(assume_ (gaussian_ (float_ 1.0) (float_ 1.0)))
  ,  (assume_ (gaussian_ (float_ 2.0) (float_ 1.0)))
  ])
  , get_ (var_ "x") (int_ 0)
  ] in
let case7_3 =
  bindall_
  [ ulet_ "a" (float_ 2.0)
  , ulet_ "x" (seq_ [(assume_ (gaussian_ (var_ "a") (float_ 1.0)))
  , (assume_ (gaussian_ (float_ 2.0) (float_ 1.0)))
  ])
  --, get_ (var_ "x") (int_ 0)
  , var_ "a"
  ] in

let case7_4 =
  bindall_
  [ ulet_ "a" (float_ 2.0)
  , ulet_ "x" (seq_ [(assume_ (gaussian_ (var_ "a") (float_ 1.0)))
  , (assume_ (gaussian_ (float_ 2.0) (float_ 1.0)))
  ])
  , ulet_ "b" (get_ (var_ "x") (int_ 0))
  , var_ "b"
  ] in

let case8_1 =
  bindall_
  [ ulet_ "a" (assume_ (beta_ (float_ 1.0) (float_ 1.0)))
  , ulet_ "" (observe_ true_ (bern_ (var_ "a")))
  , ulet_ "" (observe_ true_ (bern_ (var_ "a")))

  , ulet_ "" (observe_ true_ (bern_ (var_ "a")))

  , ulet_ "" (observe_ true_ (bern_ (var_ "a")))

  , ulet_ "" (observe_ true_ (bern_ (var_ "a")))

  , ulet_ "" (observe_ true_ (bern_ (var_ "a")))

  , ulet_ "" (observe_ true_ (bern_ (var_ "a")))
  , ulet_ "" (observe_ true_ (bern_ (var_ "a")))
  , ulet_ "" (observe_ true_ (bern_ (var_ "a")))

  , ulet_ "" (observe_ true_ (bern_ (var_ "a")))

  , ulet_ "" (observe_ true_ (bern_ (var_ "a")))

  , ulet_ "" (observe_ true_ (bern_ (var_ "a")))

  , ulet_ "" (observe_ true_ (bern_ (var_ "a")))

  , ulet_ "" (observe_ true_ (bern_ (var_ "a")))

  , ulet_ "" (observe_ true_ (bern_ (var_ "a")))
  , ulet_ "" (observe_ true_ (bern_ (var_ "a")))

  , ulet_ "" (observe_ true_ (bern_ (var_ "a")))

  , ulet_ "" (observe_ true_ (bern_ (var_ "a")))

  , ulet_ "" (observe_ true_ (bern_ (var_ "a")))

  , ulet_ "" (observe_ true_ (bern_ (var_ "a")))

  , ulet_ "" (observe_ true_ (bern_ (var_ "a")))
 , ulet_ "" (observe_ true_ (bern_ (var_ "a")))

  , ulet_ "" (observe_ true_ (bern_ (var_ "a")))

  , ulet_ "" (observe_ true_ (bern_ (var_ "a")))

  , ulet_ "" (observe_ true_ (bern_ (var_ "a")))

  , ulet_ "" (observe_ true_ (bern_ (var_ "a")))

  , ulet_ "" (observe_ true_ (bern_ (var_ "a")))
  , ulet_ "" (observe_ true_ (bern_ (var_ "a")))

  , ulet_ "" (observe_ true_ (bern_ (var_ "a")))

  , ulet_ "" (observe_ true_ (bern_ (var_ "a")))

  , ulet_ "" (observe_ true_ (bern_ (var_ "a")))

  , ulet_ "" (observe_ true_ (bern_ (var_ "a")))

  , ulet_ "" (observe_ true_ (bern_ (var_ "a")))

  , var_ "a"
  ] in

let case9 =
  bindall_
  [ ulet_ "a" (assume_ (beta_ (float_ 1.0) (float_ 1.0)))
  , ulet_ "b" (assume_ (beta_ (var_ "a") (float_ 1.0)))
  , ulet_ "c" (assume_ (beta_ (var_ "b") (float_ 1.0)))
  , ulet_ "d" (assume_ (beta_ (var_ "c") (float_ 1.0)))
  , var_ "d"
  ] in
let case10 =
  bindall_
  [ ulet_ "a" (assume_ (beta_ (float_ 1.0) (float_ 1.0)))
  , ulet_ "b" (assume_ (gaussian_ (var_ "a") (float_ 1.0)))
  , var_ "b"
  ] in


let case8_2 =
  bindall_
  [ ulet_ "a" (assume_ (beta_ (float_ 1.0) (float_ 1.0)))
  , ulet_ "" (observe_ (float_ 1.0) (gaussian_ (var_ "a") (float_ 1.0)))
  , var_ "a"
  ] in
let cases = [case1,case2,case3,case4,case5,case6,case7,case9,case10] in

()
