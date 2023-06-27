include "digraph.mc"
include "coreppl.mc"
include "ext/math-ext.mc"

type Label = Int
type QDist = Map Name Dist -- a map from random variable names to their marginalized distribution
type PQDist = Map Name QDist -- a map from plates to QDist,i.e. each plate has its own QDist

let getRoots = lam g:Digraph Vertex Label.
  let vertices = digraphVertices g in
  filter (lam v. null (digraphEdgesTo v g)) vertices
--StaticAnalyzer: Expr -> 
--Expr -> PBN -> PBN -> Expr
lang MExprPPLStaticDelayedANF = MExprPPL + MExprANFAll
 -- sem normalize: (Expr -> Expr) -> Expr
  sem normalize (k:Expr -> Expr) =
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

lang PBNGraph = MExprAst + MExprPPL
  -- m: a mapping from a vertex ident to a corresponding vertex
  type PBN = {
    g:Digraph Vertex Label,
    m:Map Name Vertex,
    targets:[Name]
  }

  syn Vertex =
  | RandomVarNode {ident:Name,
                    val:Option Expr,
                    color:Int, -- 0:blue (assume), 1:red (stable)
                    dist:Dist,
                    plateId:Option Name} --if it belongs to a plate
  | CodeBlockNode {ident:Name,
                    code:Expr,
                    ret:Bool,
                    plateId:Option Name} --if it belongs to a plate
  | ListNode {ident:Name,
              items:[Name],
              dist:Option Dist,
              plateId:Option Name}  --if it belongs to a plate
  | CreateNode {ident:Name,
                item:Name,
                n:Name,
                dist:Option Expr,
                plateId:Option Name}
  | MultiplexerNode {ident:Name,
                      indexId:Name,
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

  sem v2str: Vertex -> String
  sem v2str =
  | RandomVarNode v -> let id = v.ident in 
                       join ["\nRandomVarNode ident: (", id.0, ", ",(int2string (sym2hash id.1)), ")",
                       "\ncolor:", if eqi v.color 0 then "blue" else "red" 
                       ," dist " , (mexprToString (dist_ v.dist))]
  | CodeBlockNode v -> let id = v.ident in 
                       let ret = if v.ret then " true" else " false" in
                      join ["\nCodeBlockNode ident: (", id.0, ", ",(int2string (sym2hash id.1)), ")",
                            "\nCode:",expr2str v.code, "\nIsRet:",ret, "\n"]
  | ListNode v -> let id = v.ident in 
                  join ["\nListNode ident: (", id.0, ", ",(int2string (sym2hash id.1)), ")",
                  foldl (lam acc. lam v. join [acc, " ", v.0 ,":",(int2string (sym2hash v.1)),"\t"]) "" v.items]
  | CreateNode v -> let id = v.ident in 
                    join ["\nCreateNode ident: (", id.0, ", ",(int2string (sym2hash id.1)), ")"]
  | MultiplexerNode v -> let id = v.ident in
                        join ["\nMultiplexerNode ident: (", id.0, ", ",(int2string (sym2hash id.1)), ")"]
  | PlateNode v -> let id = v.ident in 
                        join ["\nPlateNode ident: (", id.0, ", ",(int2string (sym2hash id.1)), ")",
      foldl (lam acc. lam v. join [acc, "",v.0,":" ,(int2string (sym2hash v.1)),"\t"]) "" (setToSeq v.vertices)]
  | FoldNode v -> let id = v.ident in 
                        join ["\nFoldNode ident: (", id.0, ", ",(int2string (sym2hash id.1)), ")",
      foldl (lam acc. lam v. join [acc, "",v.0,":" ,(int2string (sym2hash v.1)),"\t"]) "" (setToSeq v.vertices)]

  sem cmprVertex: Vertex -> Vertex -> Int
  sem cmprVertex v1 =
  | v2 -> cmprVertexH (v1,v2)

  sem cmprVertexH: (Vertex,Vertex) -> Int
  sem cmprVertexH =
  | (RandomVarNode t1, RandomVarNode t2) -> nameCmp t1.ident t2.ident
  | (CodeBlockNode t1, CodeBlockNode t2) -> nameCmp t1.ident t2.ident
  | (ListNode t1, ListNode t2) -> nameCmp t1.ident t2.ident
  | (MultiplexerNode t1, MultiplexerNode t2) -> nameCmp t1.ident t2.ident
  | (PlateNode t1, PlateNode t2) -> nameCmp t1.ident t2.ident
  | (FoldNode t1, FoldNode t2) -> nameCmp t1.ident t2.ident
  | (CreateNode t1, CreateNode t2) -> nameCmp t1.ident t2.ident
  | (t1,t2) -> subi (constructorTag t1) (constructorTag t2)

  sem cmprEdge: (Vertex,Vertex,Label) -> (Vertex,Vertex,Label) -> Int
  sem cmprEdge e1 =
  | (v1, v2, _) -> let cmprV1 = cmprVertex e1.0 v1 in
                   if eqi cmprV1 0 then cmprVertex e1.1 v2 else cmprV1

  sem getId: Vertex -> Name
  sem getId =
  | RandomVarNode v -> v.ident
  | CodeBlockNode v -> v.ident
  | MultiplexerNode v -> v.ident
  | ListNode v -> v.ident
  | PlateNode v -> v.ident
  | FoldNode v -> v.ident
  | CreateNode v -> v.ident

  sem getDist: Vertex -> Option Dist
  sem getDist =
  | RandomVarNode v -> Some (v.dist)
  | _ -> None ()

  sem plateToFold: Name -> Name -> Vertex -> Vertex
  sem plateToFold acc ret =
  | PlateNode p -> FoldNode {ident=p.ident,lamVar=p.lamVar,iter=p.iter,vertices=p.vertices,plateId=p.plateId,acc=acc,ret=ret}

  -- given a multiplexer m and a graph g, returns the list node that is an input to m
  sem inputMultiplexer: Digraph Vertex Label -> Vertex -> Vertex
  sem inputMultiplexer g =
  | MultiplexerNode m ->
    let parent = filter (lam v. match v with ListNode _ then true else (match v with CreateNode _ then true else false))
    (digraphPredeccessors (MultiplexerNode m) g) in
    get parent 0
  | _ -> error "inputMultiplexer:given vertex is not a multiplexer"

  -- given a multiplexer m and a graph g, returns Some index node to m if it exists otherwise None ()
  sem indexMultiplexer: Digraph Vertex Label -> Vertex -> Vertex
  sem indexMultiplexer g =
  | MultiplexerNode m ->
    let parent = filter (lam v. match v with ListNode _ then false else match v with CreateNode _ then false else true) (digraphPredeccessors (MultiplexerNode m) g) in
    (get parent 0)
 | _ -> error "indexMultiplexer:given vertex is not a multiplexer"

end


lang ConjugatePrior = CorePPL + MExprAst + MExprPPL + PBNGraph

  -- (d1:likelihood,d2:prior) checks whether d1 and d2 are conjugate
  sem isConjugatePrior: (Dist,Dist) -> Bool
  sem isConjugatePrior =
  | (DBernoulli _,DBeta _) -> true
  | (DGaussian d1,DGaussian d2) -> true
  | (DCategorical d1,DDirichlet d2) -> true
  | _ -> false

  -- check if two distributions family is equivalent
  sem eqFamilyDist: (Dist,Dist) -> Bool
  sem eqFamilyDist =
  |(d1,d2) -> eqi (constructorTag d1) (constructorTag d2)

  -- check whether a list consists of rvs with same distribution family
  sem validList: Option Dist -> [Vertex] -> Option Dist
  sem validList commonDist =
  | [RandomVarNode t] ++ as -> match commonDist with Some dist1 then
                                match t.dist with dist2 then
                                  (if eqFamilyDist (dist1,dist2) then
                                    validList commonDist as
                                  else None ())
                                else never
                              else validList (Some t.dist) as
  | [] -> commonDist
  | [t] ++ as -> None ()

  sem getParams: Dist -> Expr
  sem getParams =
  | DBernoulli d -> utuple_ [d.p]
  | DBeta d -> utuple_ [d.a,d.b]
  | DGaussian d -> utuple_ [d.mu, d.sigma]
  | DCategorical d -> utuple_ [d.p]
  | DDirichlet d -> utuple_ [d.a]

  sem changeParams: Name -> Dist -> Dist
  sem changeParams id =
  | DBernoulli d -> DBernoulli {d with p= tupleproj_ 0 (nvar_ id) }
  | DBeta d -> DBeta {{d with a=tupleproj_ 0 (nvar_ id) } with b=tupleproj_ 1 (nvar_ id) }
  | DGaussian d -> DGaussian {{d with mu=tupleproj_ 0 (nvar_ id)} with sigma=tupleproj_ 1 (nvar_ id) }
  | DCategorical d -> DCategorical {d with p= tupleproj_ 0 (nvar_ id)}
  | DDirichlet d -> DDirichlet {d with a=tupleproj_ 0 (nvar_ id)}

  -- given the likelihood,the prior and the observartion calculates the posterior
  -- (d1: likelihood, d2: prior)
  sem posterior: Option Expr -> Option (Name,Expr) -> Option Name -> (Dist,Dist) -> (Vertex,Dist)
  sem posterior obs indices plateId =
  | (DBernoulli d1,DBeta d2) ->
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
    (rho, DBeta {{d2 with a=(nvar_ aName)} with b= (nvar_ bName)})
  | (DGaussian d1, DGaussian d2) ->
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
    (rho, DGaussian {{d2 with mu= tupleproj_ 0 (nvar_ tName)} with sigma= tupleproj_ 1 (nvar_ tName)})
  | (DCategorical d1,DDirichlet d2) ->
    let val = match obs with Some val then val else never in
    let postA = mapi_ ( ulam_ "i" (ulam_ "e" (if_ (eqi_ (var_ "i") val) (addf_ (var_ "e") (float_ 1.0)) (var_ "e")))) d2.a in
    let code =
      match indices with Some (mInd, lInd) then
        if_ (eqi_ (nvar_ mInd) lInd) postA d2.a
      else postA in
    let tName = nameSym "paramR" in
    let letT = nulet_ tName code in
    let rho = CodeBlockNode {ident=tName, code=letT, ret=false,list=false,plateId=plateId} in
    (rho, DDirichlet {d2 with a=nvar_ tName})
  | _ -> error "posterior:not supported"

  -- input (d1: likelihood, d2: prior)
  -- output (rho:Vertex, q:Expr)
  sem posteriorPredictive: Option Name -> (Dist,Dist) -> (Vertex,Dist)
  sem posteriorPredictive plateId =
  | (DBernoulli d1,DBeta d2) ->
    let postAlpha = d2.a in
    let postBeta = d2.b in
    let postP = divf_ postAlpha (addf_ postAlpha postBeta) in
    let tName = nameSym "param" in
    let letT = nulet_ tName postP in
    let rho = CodeBlockNode {ident=tName, code=letT, ret=false,list=false,plateId=plateId} in
    (rho,DBernoulli {d1 with p= nvar_ tName})

  | (DGaussian d1,DGaussian d2) ->
    let s02 = (mulf_ d2.sigma d2.sigma) in
    let s2 = (mulf_ d1.sigma d1.sigma) in
    let postMu = mulf_ s02 (divf_ d2.mu s02) in
    let postSigma = appf1_ (var_ "externalSqrt") (addf_ s02 s2) in
    let tName = nameSym "param" in
    let letT = nulet_ tName (utuple_ [postMu, postSigma]) in
    let rho = CodeBlockNode {ident=tName, code=letT, ret=false,list=false,plateId=plateId} in
    (rho, DGaussian {{d1 with mu= tupleproj_ 0 (nvar_ tName)} with sigma= tupleproj_ 1 (nvar_ tName)})

  | (DCategorical d1,DDirichlet d2) ->
    let sumai = foldl_ (ulam_ "acc" (ulam_ "i" (addf_ (var_ "acc") (var_ "i")))) (float_ 0.0) (d2.a) in
    let postA = map_ (ulam_ "ai" (divf_ (var_ "ai") sumai)) d2.a in
    let tName = nameSym "param" in
    let letT = nulet_ tName postA in
    let rho = CodeBlockNode {ident=tName, code=letT, ret=false,list=false,plateId=plateId} in
    (rho, DCategorical {d1 with p=nvar_ tName})
  | _ -> error "posteriorPredictive:not supported"

  sem listParam: Name -> Dist -> Dist
  sem listParam cbId =
  | DBernoulli d1 -> DBernoulli {d1 with p= nvar_ cbId}
  | DGaussian d1 -> DGaussian {{d1 with mu= tupleproj_ 0 (nvar_ cbId)} with sigma= tupleproj_ 1 (nvar_ cbId)}
  | DCategorical d1 ->  DCategorical {d1 with p=nvar_ cbId}
  | DBeta d1-> DBeta {{d1 with a= tupleproj_ 0 (nvar_ cbId)} with b = tupleproj_ 1 (nvar_ cbId)}
  | DDirichlet d1 -> DDirichlet {d1 with a=nvar_ cbId}
  | _ -> error "listParam:not supported"
end

-- Language fragment to create PBN from a given program
lang CreatePBN = ConjugatePrior
  -- m2: a mapping from a variable name to its corresponding vertex id. Several let bindings can corresspond to a single code block vertex
  type CreateAcc = {
    m2:Map Name Name,
    blockIdent:Option Name,
    plateV:Option (Name,(Set Name)),
    vertexId:Option Name,
    isRet:Bool
  }

  sem emptyCreateAcc: () -> CreateAcc
  sem emptyCreateAcc =
  | _ ->
    let emptyM = (lam. mapEmpty nameCmp) in
    {m2=(emptyM ()),blockIdent=(None ()), plateV=(None ()),vertexId=None (),isRet=false}

  -- a mapping of types for each function
  -- name:create --
  sem createM : Expr -> PBN
  sem createM =
  | prog ->
    let emptyG = digraphEmpty cmprVertex eqi in
    let res = createPBN {g=emptyG,targets=[],m=mapEmpty nameCmp} (emptyCreateAcc ()) prog in
    res.0

  -- create edges based on the dependencies of vertex v
  sem createEdges: Vertex -> PBN -> CreateAcc -> Set (Vertex,Vertex,Label) -> Expr -> Set (Vertex,Vertex,Label)
  sem createEdges v pbn cAcc edges =
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
  sem findRandomVariables: Map Name Vertex -> [Name] -> Expr -> [Name]
  sem findRandomVariables m idents =
  | TmVar t -> match mapLookup t.ident m with Some (RandomVarNode _) then cons t.ident idents else idents
  | t -> sfold_Expr_Expr (findRandomVariables m) idents t

  sem plateAddVertex: Name -> Option (Name, Set Name) -> Option (Name, Set Name)
  sem plateAddVertex (id:Name) =
  | Some (idp,p) -> Some (idp, setInsert id p)
  | _ -> None ()

  sem createCodeBlock: PBN -> CreateAcc -> Expr -> (Option Name, Option Name) -> (Vertex,Name)
  sem createCodeBlock pbn cAcc t =
  | (Some id, Some bid) -> let vertex = mapLookupOrElse (lam. error "Lookup failed") bid pbn.m in
                           match vertex with CodeBlockNode c then
                             let v = CodeBlockNode {c with code=bind_ c.code (nulet_ id t)} in
                             (v,c.ident)
                           else never
  | (Some id, None ()) -> let ident = nameSym "" in
                          let pid = match cAcc.plateV with Some (id,p) then Some id else None () in
                          let v = CodeBlockNode {ident=ident,code=(nulet_ id t),ret=false, plateId=pid} in
                          (v,ident)
  | _ -> let ident = nameSym "" in
         let pid = match cAcc.plateV with Some (id,p) then Some id else None () in
         let v = CodeBlockNode {ident=ident,code=t,ret=cAcc.isRet, plateId=pid} in
         (v,ident)

  -- given vertex, its id for pbn.m and id for cAcc.m2 and expr for env
  sem addVertex: PBN -> CreateAcc -> (Vertex,Name,Name) -> (PBN, CreateAcc)
  sem addVertex pbn cAcc =
  | (v,id,id2) ->
    let g = digraphAddUpdateVertex v pbn.g in
    let m = mapInsert id v pbn.m in
    let m2 = mapInsert id2 id cAcc.m2 in
    let pV = plateAddVertex id cAcc.plateV in
    ({{pbn with g=g} with m=m}, {{{cAcc with m2=m2} with blockIdent=None ()} with plateV=pV})
 
  sem createPBN: PBN -> CreateAcc -> Expr -> (PBN,CreateAcc)
  sem createPBN pbn cAcc =
  | TmLet t ->
    let res = createPBNH pbn {{cAcc with vertexId=(Some t.ident)} with isRet=false} t.body in
    createPBN res.0 res.1 t.inexpr
  | (TmRecLets {inexpr=inexpr} | TmExt {inexpr=inexpr} | TmType {inexpr=inexpr} |TmConDef {inexpr=inexpr})& t ->
    let res = createPBNH pbn {{cAcc with isRet=false} with vertexId=None ()}  t in
    createPBN res.0 res.1 inexpr
  | t -> createPBNH pbn {{cAcc with isRet=true} with vertexId=None ()}  t

  sem createPBNH:PBN -> CreateAcc -> Expr -> (PBN, CreateAcc)
  sem createPBNH pbn cAcc =
  | (TmAssume {dist=TmDist {dist=dist}} | TmObserve {dist=TmDist {dist=dist}}) & t ->
    -- get the ident if it comes from a let expression
    let id = match cAcc.vertexId with Some id then id else nameSym "" in
    -- if an observe then get its value
    let val = match t with TmObserve t then Some t.value else None () in
    -- get the plate id if it is in a plate
    let pid = match cAcc.plateV with Some (id,_) then Some id else None () in
    -- create the vertex
    let v = RandomVarNode {ident = id, val = val, color = 0, dist = dist, plateId=pid} in
    -- add the vertex to the graph and to the context
    let res = addVertex pbn cAcc (v,id,id) in
    match res with (pbn,cAcc) in
    let res =
      --if it is a return then also create a codeblock that returns created random variable
      if cAcc.isRet then
        let cb = createCodeBlock pbn cAcc (nvar_ id) (None(),None()) in
        let res = addVertex pbn cAcc (cb.0,cb.1,cb.1) in
        match res with (pbn,cAcc) in
        let g = digraphAddEdge v cb.0 0 pbn.g in
        ({pbn with g=g},cAcc)
      else (pbn,cAcc) in
    match res with (pbn,cAcc) in
    -- if it is an observe, add it to targets
    let targets = match t with TmObserve _ then cons id pbn.targets else pbn.targets in
    -- create edges to the created random variable node v from the nodes that it depends on
    let edges = setToSeq (createEdges v pbn cAcc (setEmpty cmprEdge) t) in
    let g = digraphAddEdges edges pbn.g in
    ({{pbn with targets=targets} with g=g},{cAcc with blockIdent=None()})
  | TmVar t ->
    if cAcc.isRet then createPBNGeneric pbn cAcc (TmVar t)
    else
      let id = match cAcc.vertexId with Some id then id else never in
      -- get the vertex id varible mapped to in cAcc.m2
      let id2 = mapLookupOrElse (lam. error "Lookup failed") t.ident cAcc.m2 in
      -- get the vertex
      let v = mapLookupOrElse (lam. error "") id2 pbn.m in
      -- now, id refers to the same vertex
      let m = mapInsert id v pbn.m in
      -- add that mapping from id to the vertex id to cAcc.m2
      let m2 = mapInsert id id2 cAcc.m2 in
      -- a list can only consists of random variable nodes
      ({pbn with m=m},{cAcc with m2=m2})
  | TmSeq t ->
    -- get the ident if it comes from a let expression
    let id = match cAcc.vertexId with Some id then id else nameSym "" in
    -- get the plate ident if it is in a plate
    let pid = match cAcc.plateV with Some (id,_) then Some id else None () in
    let items = map (lam e.
                    let id = match e with TmVar t then t.ident else never in
                    let v = mapLookup id pbn.m in
                    match v with Some r then match r with RandomVarNode _ then v else None () else None ()
                    )  t.tms in
    let nvalidL = any (lam v. match v with None () then true else false) items in
    let valL =
      if nvalidL then None ()
      else
        let tms = map (optionGetOrElse (lam. error "")) items in
        let dist = validList (None ()) tms in
        let ids = map getId tms in
        match dist with Some _ then Some (dist,ids) else None ()
    in
    let v =
      match valL with Some (dist,ids) then
        (ListNode {ident=id, items=ids,dist=dist,plateId=pid},id)
      else
        createCodeBlock pbn cAcc (TmSeq t) (cAcc.vertexId,cAcc.blockIdent)
    in
    let res= addVertex pbn cAcc (v.0,v.1,id) in
    match res with (pbn,cAcc) in
    (pbn,cAcc)
/-  | TmApp ({lhs=(TmApp ({lhs=TmConst ({val=CCreate()}&c),rhs=TmVar rep})&a1),rhs=TmLam l}&a2) ->
    if cAcc.inList then (pbn,cAcc,None ()) else
    let id = match cAcc.vertexId with Some id then id else nameSym "" in
    let pid = match cAcc.plateV with Some (id,_) then Some id else None () in
    let nvalidL = match l.body with TmAssume _ then false else match l.body with TmObserve _ then false else true in
    let res =
      if nvalidL then
        let v = createCodeBlock pbn.m cAcc.inList pid (nulet_ id (TmApp a2)) false (None (),cAcc.blockIdent) in
        (pbn,cAcc,v)
    else
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
    ({pbn with g=g},{cAcc with blockIdent=None()},Some v.0)-/
 | TmApp ({lhs=(TmApp ({lhs=TmConst ({val=CGet ()}&c),rhs=TmVar seq})&t2),rhs=TmVar ind}&a) ->
    let id = match cAcc.vertexId with Some id then id else nameSym "" in
    let pid = match cAcc.plateV with Some (id,p) then Some id else None () in
    let v =
      -- if there is no such list node created, create a codeblock
      match mapLookup seq.ident pbn.m with None () then
        createCodeBlock pbn cAcc (TmApp a) (cAcc.vertexId,cAcc.blockIdent)
      else -- there is a list node created which consists of valid items
        let seqV = mapLookupOrElse (lam. error "Get:Lookup failed") seq.ident pbn.m in
        let m = MultiplexerNode {ident=id,indexId=ind.ident,plateId=pid} in
        (m,id)
    in
    let res = addVertex pbn cAcc (v.0,v.1,id) in
    match res with (pbn,cAcc) in
    let edges = setToSeq (createEdges v.0 pbn cAcc (setEmpty cmprEdge) (TmApp a)) in
    let g = digraphAddEdges edges pbn.g in
    ({pbn with g=g}, {cAcc with blockIdent=None()})
  | TmApp ({lhs=(TmApp ({lhs=TmConst ({val=CIter()}&c),rhs=TmLam l})&a1),rhs=TmVar lst}&a2) ->
    createPlate pbn cAcc [l.ident] l.body lst.ident (TmApp a2)
  | TmApp ({lhs=(TmApp ({lhs=TmConst ({val=CIteri()}&c),rhs=TmLam ({body=TmLam l2}&l1)})&a1),rhs=TmVar lst}&a2) ->
    createPlate pbn cAcc [l1.ident,l2.ident] l2.body lst.ident (TmApp a2)
  | t-> createPBNGeneric pbn cAcc t

  sem createPlate: PBN -> CreateAcc -> [Name] -> Expr -> Name -> Expr -> (PBN,CreateAcc)
  sem createPlate pbn cAcc idents body lstId =
  | t ->
    let id = match cAcc.vertexId with Some id then id else nameSym "" in
    let res = createPBN pbn {{cAcc with blockIdent=None()} with plateV= (Some (id,(setEmpty nameCmp)))} body in
    match res with (pbnB,cAccB) in
    let vertices = match cAccB.plateV with Some (id,v) then v else never in
    let pid = match cAcc.plateV with Some (id,p) then Some id else None () in
    let v = PlateNode {ident=id, lamVar=idents,iter=lstId, vertices=vertices,plateId=pid} in
    let res = --if it is a return then also create a codeblock that returns created variable
      if cAcc.isRet then
        let idcb = nameSym "" in
        let cb = CodeBlockNode {ident=idcb,code=nvar_ id,ret=true,plateId=pid} in
        let res = addVertex pbnB {cAccB with plateV=cAcc.plateV} (cb,idcb,idcb) in
        match res with (pbnB,cAccB) in
        let g = digraphAddEdge v cb 0 pbnB.g in
        ({pbnB with g=g},cAccB)
      else (pbnB,{cAccB with plateV=cAcc.plateV}) in
    match res with (pbn,cAcc) in
    let res = addVertex pbn cAcc (v,id,id) in
    match res with (pbn,cAcc) in
    let edges = setToSeq (createEdges v pbn cAcc (setEmpty cmprEdge) (nvar_ lstId)) in
    let g = digraphAddEdges edges pbn.g in
    ({pbn with g=g},cAcc)

  sem createPBNGeneric: PBN -> CreateAcc -> Expr -> (PBN,CreateAcc)
  sem createPBNGeneric pbn cAcc =
  | t ->
    let pid = match cAcc.plateV with Some (id,p) then Some id else None () in
    let v = createCodeBlock pbn cAcc t (cAcc.vertexId,cAcc.blockIdent) in
    let id = match cAcc.vertexId with Some id then id else v.1 in
    let res = addVertex pbn cAcc (v.0,v.1,id) in
    match res with (pbn,cAcc) in
    let edges = setToSeq (createEdges v.0 pbn cAcc (setEmpty cmprEdge) t) in
    let g = digraphMaybeAddEdges edges pbn.g in
    let targets = findRandomVariables pbn.m pbn.targets t in
    ({{pbn with g=g} with targets=targets},cAcc)

end

lang RecreateProg = PBNGraph + MExprAst + MExprPPL
 
  sem recreate: PBN -> Expr
  sem recreate =
  | pbn ->
    (digraphPrintDot pbn.g v2str int2string);
    let pbn = modifyGraph pbn in
    let order = digraphTopologicalOrder pbn.g in
    let vRet = filter (lam v.match v with CodeBlockNode c then let np = match c.plateId with Some _ then false else true in and c.ret np else false) order in
    let plates = filter (lam e. match e with PlateNode _ then true else false) order in
    let plateVertices = foldl (lam mp. lam p.
      match p with PlateNode p then
        let orderedV = filter (lam e. let id = getId e in setMem id p.vertices) order in
        mapInsert p.ident orderedV mp
      else never
      ) (mapEmpty nameCmp) plates in
    let order = filter (lam v. match v with CodeBlockNode c then not c.ret else true) order in
    let vRet = if eqi (length vRet) 0 then error "recreate:no return" else (Some (get vRet 0)) in
    recreateVertex vRet false plateVertices pbn.g order


  sem recreateVertex: Option Vertex -> Bool -> Map Name [Vertex] -> Digraph Vertex Label -> [Vertex] -> Expr
  sem recreateVertex vRet plate plateVertices g =
  | [CodeBlockNode t] ++ as -> 
                  let pl = match t.plateId with Some _ then true else false in
  								if and (not plate) pl then
  									recreateVertex vRet plate plateVertices g as 
  								else bind_ t.code (recreateVertex vRet plate plateVertices g as)
  | [RandomVarNode v] ++ as ->
                        let pl = match v.plateId with Some _ then true else false in 
                        if and (not plate) (pl) then
                         recreateVertex vRet false plateVertices g as
                        else
                         match v.val with Some val then -- observe
                          TmLet { ident = v.ident,
                                tyBody = tyunknown_,
                                body = (TmObserve {dist=dist_ v.dist, value=val,ty=tyunknown_, info = NoInfo ()}),
                                inexpr=(recreateVertex vRet plate plateVertices g as),
                                ty=tyunknown_,
                                info = NoInfo (),
                                tyAnnot = tyunknown_}
                        else
                          TmLet { ident = v.ident,
                                tyBody = tyunknown_,
                                body = (TmAssume {dist=dist_ v.dist, ty=tyunknown_, info = NoInfo ()}),
                                inexpr=(recreateVertex vRet plate plateVertices g as),
                                ty=tyunknown_,
                                info= NoInfo (),
                                tyAnnot = tyunknown_}
  | [ListNode l] ++ as -> TmLet { ident = l.ident,
                                  tyBody = tyunknown_,
                                  body = (TmSeq {tms=(map (lam i. nvar_ i) l.items), ty=tyunknown_,info=NoInfo ()}),
                                  inexpr =(recreateVertex vRet plate plateVertices g as),
                                  ty = tyunknown_,
                                  info = NoInfo (),
                                  tyAnnot = tyunknown_}
  | [CreateNode c] ++ as -> TmLet { ident = c.ident,
                                  tyBody = tyunknown_,
                                  body = (create_ (nvar_ c.n) (ulam_ "" (nvar_ c.item))),
                                  inexpr =(recreateVertex vRet plate plateVertices g as),
                                  ty = tyunknown_,
                                  info = NoInfo (),
                                  tyAnnot = tyunknown_}

  | [MultiplexerNode mu] ++ as ->  
  print (v2str (MultiplexerNode mu));
  let listnode = inputMultiplexer g (MultiplexerNode mu) in
   match listnode with ListNode l then
                                      TmLet { ident = mu.ident,
                                        tyBody = tyunknown_,
                                        body = get_ (nvar_ l.ident) (nvar_ mu.indexId),
                                        inexpr=(recreateVertex vRet plate plateVertices g as),
                                        ty=tyunknown_,
                                        info= NoInfo (),
                                        tyAnnot = tyunknown_}
                                    else never
  | [PlateNode p] ++ as ->
     let pl = match p.plateId with Some _ then true else false in
     if and (not plate) pl then recreateVertex vRet false plateVertices g as else
      let vItems = mapLookupOrElse (lam. error "Recreate-plate:Lookup failed") p.ident plateVertices in
      let vPRet = filter (lam v. match v with CodeBlockNode c then c.ret else false) vItems in
      let vPRet = if eqi (length vPRet) 0 then error "recreate:plate-no return" else (Some (get vPRet 0)) in
      let vItems = filter (lam v. match v with CodeBlockNode c then not c.ret else true) vItems in
      let bdyIn = (recreateVertex vPRet true plateVertices g vItems) in
      let bdy = foldl (lam acc. lam l. nulam_ l acc) bdyIn (reverse p.lamVar) in
      let tlet =
        match length p.lamVar with 1 then
          TmLet { ident = p.ident,
                                  tyBody = tyunknown_,
                                  body = (iter_
                                    (nulam_ (get p.lamVar 0)
                                      (recreateVertex vPRet true plateVertices g vItems)) (nvar_ p.iter)),
                                  inexpr =(recreateVertex vRet false plateVertices g as),
                                  ty = tyunknown_,
                                  info = NoInfo (),
                                  tyAnnot = tyunknown_}
        else
          TmLet { ident = p.ident,
                                  tyBody = tyunknown_,
                                  body = (iteri_ (nulam_ (get p.lamVar 0) (nulam_ (get p.lamVar 1)
                                      (recreateVertex vPRet true plateVertices g vItems))) (nvar_ p.iter)),
                                  inexpr =(recreateVertex vRet false plateVertices g as),
                                  ty = tyunknown_,
                                  info = NoInfo (),
                                  tyAnnot = tyunknown_} in tlet  
  | [FoldNode f] ++ as ->
      let pl = match f.plateId with Some _ then true else false in 
                        if and (not plate) pl then
                         recreateVertex vRet false plateVertices g as
                        else
                          let vItems = mapLookupOrElse (lam. error "Recreate-plate:Lookup failed") f.ident plateVertices in
                          let vPRet = get (filter (lam v. match v with CodeBlockNode c then c.ret else false) vItems) 0 in
                          let vItems = filter (lam v. match v with CodeBlockNode c then not c.ret else true) vItems in
                          let bdyIn = (recreateVertex (Some vPRet) true plateVertices g vItems) in
                          let bdy = foldl (lam acc. lam l. nulam_ l acc) bdyIn (reverse f.lamVar) in
                          let ret = f.ret in
                          let accName = f.acc in
                            TmLet { ident = ret,
                                  tyBody = tyunknown_,
                                  body = foldl_ bdy (nvar_ accName) (nvar_ f.iter),
                                  inexpr =(recreateVertex vRet false plateVertices g as),
                                  ty = tyunknown_,
                                  info = NoInfo (),
                                  tyAnnot = tyunknown_}


  | [] -> match vRet with Some (CodeBlockNode c) then c.code else error "no return"

sem modifyGraph: PBN -> PBN
sem modifyGraph =
| pbn ->
  match pbn with {g=g,m=m,targets=targets} in
  let lists = filter (lam v. match v with ListNode _ then true else false) (digraphVertices g) in
  let g = foldl (lam g. lam l.
          match l with ListNode r then
            foldl (lam g:Digraph Vertex Label. lam id:Name.
                    let i = mapLookupOrElse (lam. error "modify:Lookup failed") id m in
                    let edges = digraphEdgesTo i g in
                    digraphMaybeAddEdges (map (lam e. (e.0,l,e.2)) edges) g) g r.items else never) g lists in
  let plates = filter (lam v. match v with PlateNode _ then true else false) (digraphVertices g) in
  let g = foldl (lam g. lam pl.
    match pl with PlateNode p then
      foldl (lam g. lam id.
        let i = mapLookupOrElse (lam. error "modify:Lookup failed") id m in
        let edges = digraphEdgesTo i g in
        digraphMaybeAddEdges (map (lam e. (e.0,pl,e.2)) edges) g) g (setToSeq p.vertices) else never) g plates in
  {pbn with g=g}
end

let debug = true
/-
lang TransformPBN = ConjugatePrior
  type TAcc =
  {
    qDist:QDist,
    pqDist:PQDist
  }

  sem transformPBN =
  | pbn ->
    let tAcc = {qDist=mapEmpty nameCmp,qpDist=mapEmpty nameCmp} in 
    --let qpDist = mapEmpty nameCmp in
    if null pbn.targets then pbn
    else
      let roots = getRoots pbn.g in
      (if debug then print "Root nodes:\n";iter (lam r. print (join [(v2str r),"\n"])) roots else ());
      pbn
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
-/
let printVertices = lam g. lam v2str.
  iter (lam v. print (join [(v2str v), "\n"])) (digraphVertices g)
lang Transformation = CreatePBN /-+ TransformPBN-/ + RecreateProg + MExprPPLStaticDelayedANF
  sem transform: Expr -> Expr
  sem transform =
  | prog ->
    let model = (normalizeTerm prog) in
    print (mexprToString model);
    let pbn = createM model in
    digraphPrintDot pbn.g v2str int2string;
    let targets = map (lam i. mapLookupOrElse (lam. error "target:Lookup failed") i pbn.m) (pbn.targets) in
    let targetObserves = filter (lam v. match v with RandomVarNode v then (match v.val with Some _ then true else false) else false) targets in
    let targets = filter (lam v. match v with RandomVarNode v then (match v.val with Some _ then false else true) else true) targets in
    let targets = (concat targetObserves targets) in
    let targetIds = map getId targets in
    --(if debug then print "Target nodes:\n";iter (lam r. print (join [(v2str r),"\n"])) targets else ());
   -- print "\nTRANSFORM PBN\n";
    --let pbn = transformPBN {pbn with targets=targetIds} in
    print "\nRECREATE\n";
    let rProg = recreate pbn in
    rProg
  end

