include "digraph.mc"
include "coreppl.mc"
include "ext/math-ext.mc"

type Label = Int
type QDist = Map Name Dist -- a map from random variable names to their marginalized distribution
type QPDist = Map Name QDist -- a map from plates to QDist,i.e. each plate has its own QDist

let printVertices = lam g. lam v2str.
  iter (lam v. print (join [(v2str v), "\n"])) (digraphVertices g)

-- Restriction: CREATE HAS STATICALLY KNOWN LENGTH.
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
  | TmApp ({lhs=TmApp ({lhs=TmConst ({val=CCreate ()}&c),rhs=rep}&a2),rhs=TmLam l}&a1) ->
    k (TmApp a1)

  | TmApp ({lhs=TmApp ({lhs=TmConst ({val=CIter ()}&c),rhs=TmLam l}&a2),rhs=lst}&a1) ->
    normalizeName
      (lam lst.
             k (TmApp {{a1 with lhs= TmApp {{a2 with lhs=TmConst c} with rhs=
             TmLam {l with body=normalizeTerm l.body} }} with rhs=lst}))
      lst
  | TmApp ({lhs=TmApp ({lhs=TmConst ({val=CIteri ()}&c),rhs=TmLam ({body=TmLam l2}&l1)}&a2),rhs=lst}&a1) ->
    normalizeName
      (lam lst.
             k (TmApp {{a1 with lhs= TmApp {{a2 with lhs=TmConst c} with 
              rhs=TmLam {l1 with body=TmLam {l2 with body=normalizeTerm l2.body}}}} with rhs=lst}))
      lst
end

lang PBNGraph = MExprAst + MExprPPL
   type PBN = {
    g:Digraph Vertex Label,
    m:Map Name Vertex,  -- m: a mapping from a vertex ident to a corresponding vertex
    targets:[Name]
  }

  -- why ListNode has dist? all has same distribution
  -- keep the innermost id for plates or lists
  syn Vertex =
  | RandomVarNode {ident:Name,
                    val:Option Expr,
                    color:Int, -- 0:blue (assume), 1:red (stable)
                    dist:Dist,
                    listId:Option Name,
                    plateId:Option Name} --if it belongs to a plate
  | CodeBlockNode {ident:Name,
                    code:Expr,
                    ret:Bool,
                    plateId:Option Name} --if it belongs to a plate
  | ListNode {ident:Name,
              items:[Name],
              plateId:Option Name}  --if it belongs to a plate
  | MultiplexerNode {ident:Name,
                      indexId:Name,
                      listId:Name,
                      plateId:Option Name} --if it belongs to a plate
  | PlateNode {ident:Name,
               varIds:[Name], -- new variables introduced
               listId:Name, -- name of the observations to iterate over
               plateId:Option Name}--if it belongs to a plate
  | FoldNode {ident:Name,
               varIds:[Name], -- new variables introduced
               accId:Name, -- new variables introduced
               iter:Name, -- name of the observations to iterate over
               plateId:Option Name,
               ret:Name,
               retBlock:Name,
               acc:Name}

  sem v2str: Vertex -> String
  sem v2str =
  | RandomVarNode v -> let id = v.ident in 
                      let plateStr = match v.plateId with Some id then join ["(", id.0, ", ",(int2string (sym2hash id.1)), ")"] else "-" in
                       join ["\nRandomVarNode ident: (", id.0, ", ",(int2string (sym2hash id.1)), ")",
                       "\ncolor:", if eqi v.color 0 then "blue" else "red" 
                       ,"\n dist " , (mexprToString (dist_ v.dist))
                       ,"\n val " , match v.val with Some val then mexprToString val else "-"
                       ,"\nplateId: ", plateStr]
  | CodeBlockNode v -> let id = v.ident in 
                      let plateStr =match v.plateId with Some id then join ["(", id.0, ", ",(int2string (sym2hash id.1)), ")"] else "-" in                       let ret = if v.ret then " true" else " false" in
                      join ["\nCodeBlockNode ident: (", id.0, ", ",(int2string (sym2hash id.1)), ")",
                        --   "\nCode:",expr2str v.code,
                            "\nIsRet:",ret,
                            "\nplateId: ", plateStr,"\n"]
  | ListNode v -> let id = v.ident in
                  let plateStr =match v.plateId with Some id then join ["(", id.0, ", ",(int2string (sym2hash id.1)), ")"] else "-" in
                  join ["\nListNode ident: (", id.0, ", ",(int2string (sym2hash id.1)), ")",
                  "\nplateId: ", plateStr,
                  foldl (lam acc. lam v. join [acc, " ", v.0 ,":",(int2string (sym2hash v.1)),"\t"]) "" v.items]
  | MultiplexerNode v -> let id = v.ident in
                  let plateStr =match v.plateId with Some id then join ["(", id.0, ", ",(int2string (sym2hash id.1)), ")"] else "-" in
                        join ["\nMultiplexerNode ident: (", id.0, ", ",(int2string (sym2hash id.1)), ")",
                        "\nplateId: ", plateStr]
  | PlateNode v -> let id = v.ident in
                  let plateStr = match v.plateId with Some id then join ["(", id.0, ", ",(int2string (sym2hash id.1)), ")"] else "-" in
                        join ["\nPlateNode ident: (", id.0, ", ",(int2string (sym2hash id.1)), ")",
                              "\nplateId: ", plateStr]
  | FoldNode v -> let id = v.ident in
                  let plateStr = match v.plateId with Some id then join ["(", id.0, ", ",(int2string (sym2hash id.1)), ")"] else "-" in

                        join ["\nFoldNode ident: (", id.0, ", ",(int2string (sym2hash id.1)), ")"]

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

  sem getPlateId: Vertex -> Option Name
  sem getPlateId =
  | (RandomVarNode {plateId=pid} | CodeBlockNode {plateId=pid} | MultiplexerNode {plateId=pid} |
     ListNode {plateId=pid}| PlateNode {plateId=pid}| FoldNode {plateId=pid})-> pid

  sem getListId: Vertex -> Option Name
  sem getListId =
  | RandomVarNode l -> l.listId
  | _ -> None ()

  sem getDist: Vertex -> Option Dist
  sem getDist =
  | RandomVarNode v -> Some (v.dist)
  | _ -> None ()

  sem removeVertexPBN: PBN -> Vertex -> PBN
  sem removeVertexPBN pbn =
  | v -> let g = digraphRemoveVertex v pbn.g in
    let m = mapRemove (getId v) pbn.m in
    let pbn = {{pbn with m=m} with g=g} in
    pbn

  sem addVertexPBN: PBN -> Vertex -> PBN
  sem addVertexPBN pbn =
  | v -> let g = digraphAddUpdateVertex v pbn.g in
    let m = mapInsert (getId v) v pbn.m in
    {{pbn with g=g} with m=m}

end

lang ConjugatePrior = CorePPL + MExprAst + MExprPPL + PBNGraph

  -- (d1:likelihood,d2:prior) checks whether d1 and d2 are conjugate
  sem isConjugatePrior: Name -> (Dist,Dist) -> Bool
  sem isConjugatePrior pid =
  | (DBernoulli _,DBeta _) -> true
  | (DGaussian d1,DGaussian _) -> match d1.mu with TmVar v in nameEq v.ident pid
  | (DCategorical _,DDirichlet _) -> true
  | _ -> false

  -- check if two distributions family is equivalent
  sem eqFamilyDist: (Dist,Dist) -> Bool
  sem eqFamilyDist =
  | (d1,d2) -> eqi (constructorTag d1) (constructorTag d2)

  -- check whether a list consists of rvs with same distribution family
  sem validList: PBN -> [Option Vertex] -> Bool
  sem validList pbn =
  | [Some (RandomVarNode r)] ++ as ->
    match r.listId with Some _ then false
    else validListH pbn r.dist as
  | [t] ++ as -> false

  sem validListH: PBN -> Dist -> [Option Vertex] -> Bool
  sem validListH pbn dst =
  | [Some (RandomVarNode r)] ++ as ->
    match r.listId with Some _ then false
    else if eqFamilyDist (r.dist,dst) then validListH pbn dst as else false
  | [t] ++ as -> false
  | [] -> true

  sem getParams: Dist -> Expr
  sem getParams =
  | DBernoulli d -> utuple_ [d.p]
  | DBeta d -> utuple_ [d.a,d.b]
  | DGaussian d -> utuple_ [d.mu, d.sigma]
  | DCategorical d -> utuple_ [d.p]
  | DDirichlet d -> utuple_ [d.a]
  
  sem changeParams: Name -> Dist -> Dist
  sem changeParams param =
  | DBernoulli d -> DBernoulli {d with p=tupleproj_ 0 (nvar_ param)}
  | DBeta d -> DBeta {{d with a=tupleproj_ 0 (nvar_ param) } with b=tupleproj_ 1 (nvar_ param) }
  | DGaussian d -> DGaussian {{d with mu=tupleproj_ 0 (nvar_ param)} with sigma=tupleproj_ 1 (nvar_ param)}
  | DCategorical d -> DCategorical {d with p=tupleproj_ 0 (nvar_ param)}
  | DDirichlet d -> DDirichlet {d with a=tupleproj_ 0 (nvar_ param)}
  
  -- given the likelihood,the prior and the observartion calculates the posterior
  -- (d1: likelihood, d2: prior)
  sem posterior: Option Expr -> Option (Name,Expr) -> Option Name -> (Dist,Dist) -> (Vertex,Dist,[Name])
  sem posterior obs indices plateId =
  | (DBernoulli d1,DBeta d2) ->
    let val = match obs with Some val then val else never in
    let aName = nameSym "postA" in
    let bName = nameSym "postB" in
    let postAlpha = nulet_ aName (if_ val (addf_ d2.a (float_ 1.)) d2.a) in
    let postBeta = nulet_ bName (if_ val d2.b (addf_ d2.b (float_ 1.))) in
    let code =
      match indices with Some (mInd, lInd) then
      let eqN =(nameSym "eq") in
       bindall_ [nulet_ eqN ((eqi_ (nvar_ mInd) lInd)),
                nulet_ aName (if_ (nvar_ eqN) (if_ val (addf_ d2.a (float_ 1.)) d2.a) d2.a),
                nulet_ bName (if_ (nvar_ eqN) (if_ val d2.b (addf_ d2.b (float_ 1.))) d2.b)
                ]
        --if_ (eqi_ (nvar_ mInd) lInd) (bind_ postAlpha postBeta) (bind_ (nulet_ aName d2.a) (nulet_ bName d2.b))
      else ((bind_ postAlpha postBeta)) in
    let tName = nameSym "paramR" in
    let rho = CodeBlockNode {ident=tName, code=code, ret=false, plateId=plateId} in
    let paramNames = [aName,bName] in
    (rho, DBeta {{d2 with a=(nvar_ aName)} with b=(nvar_ bName)},paramNames)
  | (DGaussian d1, DGaussian d2) ->
    let muName = nameSym "postMu" in
    let sigmaName = nameSym "postSigma" in
    let val = match obs with Some val then val else never in
    let s02 = (mulf_ d2.sigma d2.sigma) in
    let s2 = (mulf_ d1.sigma d1.sigma) in
    let muRHS = addf_ (divf_ d2.mu s02) (divf_ val s2) in
    let muLHS = divf_ (float_ 1.0) (addf_ (divf_ (float_ 1.0) s02) (divf_ (float_ 1.0) s2)) in
    let postMu = nulet_ muName (mulf_ muRHS muLHS) in
    let sigma = divf_ (float_ 1.0) (addf_ (divf_ (float_ 1.0) s02) (divf_ (float_ 1.0) s2)) in
    let postSigma = nulet_ sigmaName (appf1_ (var_ "externalSqrt") sigma) in
    let code =
      match indices with Some (mInd, lInd) then
      let eqN =(nameSym "eq") in
       bindall_ [nulet_ eqN ((eqi_ (nvar_ mInd) lInd)),
                nulet_ muName ( if_ (nvar_ eqN) (mulf_ muRHS muLHS) d2.mu),
                nulet_ sigmaName (if_ (nvar_ eqN) (appf1_ (var_ "externalSqrt") sigma) d2.sigma)
                ]
                --nulet_ muName (if_ (eqi_ (nvar_ mInd) lInd) (mulf_ muRHS muLHS) d2.mu
        --(bind_ postMu postSigma) (bind_ (nulet_ muName d2.mu) (nulet_ sigmaName d2.sigma)))
      else (bind_ postMu postSigma) in
    let tName = nameSym "paramR" in
    let rho = CodeBlockNode {ident=tName, code=code, ret=false,plateId=plateId} in
    let paramNames = [muName,sigmaName] in
    (rho, DGaussian {{d2 with mu= nvar_ muName} with sigma= nvar_ sigmaName},paramNames)
  | (DCategorical d1,DDirichlet d2) ->
    let val = match obs with Some val then val else never in
    let aName = nameSym "postA" in
    let postA = nulet_ aName (mapi_ ( ulam_ "i" (ulam_ "e" (if_ (eqi_ (var_ "i") val) (addf_ (var_ "e") (float_ 1.0)) (var_ "e")))) d2.a) in
    let code =
      match indices with Some (mInd, lInd) then
      let eqN =(nameSym "eq") in
       bindall_ [nulet_ eqN ((eqi_ (nvar_ mInd) lInd)),
                nulet_ aName (if_ (nvar_ eqN) (mapi_ ( ulam_ "i" (ulam_ "e" (if_ (eqi_ (var_ "i") val) (addf_ (var_ "e") (float_ 1.0)) (var_ "e")))) d2.a) d2.a)  ]
        --if_ (eqi_ (nvar_ mInd) lInd) postA (nulet_ aName d2.a)
      else postA in
    let tName = nameSym "paramR" in
    let rho = CodeBlockNode {ident=tName, code=code, ret=false,plateId=plateId} in
   -- let tupleName = nameSym "ret" in
   -- let rhoF = CodeBlockNode {ident=tName, code=bindall_ [code,(nvar_ aName)], ret=true, plateId=plateId} in
    let paramNames = [aName] in
    (rho, DDirichlet {d2 with a=nvar_ aName},paramNames)
  | _ -> error "posterior:not supported"

  -- input (d1: likelihood, d2: prior)
  -- output (rho:Vertex, q:Expr)
  sem posteriorPredictive: Option Name -> (Dist,Dist) -> (Vertex,Dist)
  sem posteriorPredictive plateId =
  | (DBernoulli d1,DBeta d2) ->
    let postP = divf_ d2.a (addf_ d2.a d2.b) in
    let tName = nameSym "param" in
    let pName = nameSym "margP" in
    let letT = nulet_ pName postP in
    let rho = CodeBlockNode {ident=tName, code=letT, ret=false,plateId=plateId} in
    (rho, DBernoulli {d1 with p=nvar_ pName})

  | (DGaussian d1,DGaussian d2) ->
    let s02 = (mulf_ d2.sigma d2.sigma) in
    let s2 = (mulf_ d1.sigma d1.sigma) in
    let postMu = mulf_ s02 (divf_ d2.mu s02) in
    let postSigma = appf1_ (var_ "externalSqrt") (addf_ s02 s2) in
    let tName = nameSym "param" in
    let mName = nameSym "margMu" in
    let sName = nameSym "margSigma" in
    let letT = bind_ (nulet_ mName postMu) (nulet_ sName postSigma) in
    let rho = CodeBlockNode {ident=tName, code=letT, ret=false,plateId=plateId} in
    (rho, DGaussian {{d1 with mu=nvar_ mName} with sigma=nvar_ sName})

  | (DCategorical d1,DDirichlet d2) ->
    let sumai = foldl_ (ulam_ "acc" (ulam_ "i" (addf_ (var_ "acc") (var_ "i")))) (float_ 0.0) (d2.a) in
    let postP = map_ (ulam_ "ai" (divf_ (var_ "ai") sumai)) d2.a in
    let tName = nameSym "param" in
    let pName = nameSym "margP" in
    let letT = nulet_ pName postP in
    let rho = CodeBlockNode {ident=tName, code=letT, ret=false,plateId=plateId} in
    (rho, DCategorical {d1 with p=nvar_ pName})
  | _ -> error "posteriorPredictive:not supported"

  sem posteriorPredictiveL (plateId:Option Name) (indexId:Name) =
  | ([DBernoulli d]++as)&mDists -> 
    let lName = nameSym "" in
    let pName = nameSym "margP" in
    let params = map getParams mDists in
    let lLet = nulet_ lName (seq_ params) in
    let pLet = nulet_ pName (tupleproj_ 0 (get_ (nvar_ lName) (nvar_ indexId))) in
    let code = bindall_ [lLet,pLet] in
    let rho = CodeBlockNode {ident=nameSym "",code=code,ret=false,plateId=plateId} in
    (rho, DBernoulli {d with p=nvar_ pName})
  | ([DGaussian d]++as)&mDists -> 
      let lName = nameSym "" in
      let muName = nameSym "margMu" in
      let sigmaName = nameSym "margSigma" in
      let params = map getParams mDists in
      let lLet = nulet_ lName (seq_ params) in
      let muLet = nulet_ muName (tupleproj_ 0 (get_ (nvar_ lName) (nvar_ indexId))) in
      let sigmaLet = nulet_ sigmaName (tupleproj_ 1 (get_ (nvar_ lName) (nvar_ indexId))) in
      let code = bindall_ [lLet,muLet,sigmaLet] in
      let rho = CodeBlockNode {ident=nameSym "",code=code,ret=false,plateId=plateId} in
      (rho, DGaussian {{d with mu=nvar_ muName} with sigma=nvar_ sigmaName})
  | ([DCategorical d]++as)&mDists -> 
    let lName = nameSym "" in
    let pName = nameSym "margP" in
    let params = map getParams mDists in
    let lLet = nulet_ lName (seq_ params) in
    let pLet = nulet_ pName (tupleproj_ 0 (get_ (nvar_ lName) (nvar_ indexId))) in
    let code = bindall_ [lLet,pLet] in
    let rho = CodeBlockNode {ident=nameSym "",code=code,ret=false,plateId=plateId} in
    (rho, DCategorical {d with p=nvar_ pName})
end

-- Language fragment to create PBN from a given program
lang CreatePBN = ConjugatePrior
  -- m2: a mapping from a variable name to its corresponding vertex id. Several let bindings can corresspond to a single code block vertex
  type CreateAcc = {
    m2:Map Name Name,
    blockIdent:Option Name,
    vertexId:Option Name,
    plateId:Option Name,
    isRet:Bool
  }

  sem emptyCreateAcc: () -> CreateAcc
  sem emptyCreateAcc =
  | _ -> {m2=mapEmpty nameCmp,blockIdent=(None ()),vertexId=None (),isRet=false,plateId=None ()}

  -- a mapping of types for each function
  -- name:create --
  sem createM : Expr -> PBN
  sem createM =
  | prog ->
    let emptyG = digraphEmpty cmprVertex eqi in
    let emptyPBN = {g=emptyG,targets=[],m=mapEmpty nameCmp} in
    let res = createPBN emptyPBN (emptyCreateAcc ()) prog in
    res.0

  -- create edges based on the dependencies of vertex source, assumes ANF
  sem createEdges: Vertex -> PBN -> CreateAcc -> Set (Vertex,Vertex,Label) -> Expr -> Set (Vertex,Vertex,Label)
  sem createEdges source pbn cAcc edges =
  | TmVar t ->
    -- find the corresponding vertex ident from the variable ident
    match mapLookup t.ident cAcc.m2 with Some vertexId then
      let vFrom = mapLookupOrElse (lam. error "createEdges:Lookup failed") vertexId pbn.m in
      -- create an edge to the source vertex from the vertex that it depends on
      if digraphEqv pbn.g vFrom source then edges --check if they are in the same codeblock if so no need to create an edge
      else setInsert (vFrom, source, 0) edges
    else edges -- if cannot find id then it must be created with lambda scoping so ignore
  | t -> sfold_Expr_Expr (createEdges source pbn cAcc) edges t

  -- finds the random variable identities within an expression
  sem findTargetRVs: Map Name Vertex -> [Name] -> Expr -> [Name]
  sem findTargetRVs m idents =
  | TmVar t -> let v =  mapLookup t.ident m in
               match v with Some (RandomVarNode _) then cons t.ident idents else
               -- if a multiplexer is returned, every item becomes target
               match v with Some (MultiplexerNode v) then
                let l = mapLookupOrElse (lam. error "lookup failed") v.listId m in
                match l with ListNode l in
                foldl (lam ids. lam i. cons i idents) idents l.items
               else idents
  | t -> sfold_Expr_Expr (findTargetRVs m) idents t


  sem createCodeBlock: PBN -> CreateAcc -> Expr -> (Option Name, Option Name) -> (Vertex,Name)
  sem createCodeBlock pbn cAcc t =
  -- merge with a previously created block with ident 'bid'
  | (Some id, Some bid) -> let vertex = mapLookupOrElse (lam. error "createCodeBlock:Lookup failed") bid pbn.m in
                           match vertex with CodeBlockNode c in
                           let v = CodeBlockNode {c with code=bind_ c.code (nulet_ id t)} in
                           (v,bid)
  | (Some id, None ()) -> let v = CodeBlockNode {ident=id,code=(nulet_ id t),ret=false, plateId=cAcc.plateId} in
                          (v,id)
  | _ -> let ident = nameSym "" in
         let v = CodeBlockNode {ident=ident,code=t,ret=cAcc.isRet, plateId=cAcc.plateId} in
         (v,ident)

  -- given vertex, its id for pbn.m and id for cAcc.m2 and expr for env
  sem addVertex: PBN -> CreateAcc -> (Vertex,Name) -> (PBN, CreateAcc)
  sem addVertex pbn cAcc =
  | (v,id2) ->
    let pbn = addVertexPBN pbn v in
    let m2 = mapInsert id2 (getId v) cAcc.m2 in
    (pbn, {{cAcc with m2=m2} with blockIdent=None ()})

  sem createPBN: PBN -> CreateAcc -> Expr -> (PBN, CreateAcc)
  sem createPBN pbn cAcc =
  | TmLet t ->
    let res = createPBNH pbn {{cAcc with vertexId=(Some t.ident)} with isRet=false} t.body in
    createPBN res.0 res.1 t.inexpr
  | (TmRecLets {inexpr=inexpr} | TmExt {inexpr=inexpr} | TmType {inexpr=inexpr} |TmConDef {inexpr=inexpr})& t ->
    let res = createPBNH pbn {{cAcc with isRet=false} with vertexId=None ()} t in
    createPBN res.0 res.1 inexpr
  | t -> let res = createPBNH pbn {{cAcc with isRet=true} with vertexId=None ()} t in
         (res.0,res.1)


  sem createPBNH:PBN -> CreateAcc -> Expr -> (PBN, CreateAcc, Option Vertex)
  sem createPBNH pbn cAcc =
  | (TmAssume {dist=TmDist {dist=dist}} | TmObserve {dist=TmDist {dist=dist}}) & t ->
    -- get the ident if it comes from a let expression
    let id = match cAcc.vertexId with Some id then id else nameSym "rv" in
    -- if an observe then get its value
    let val = match t with TmObserve t then Some t.value else None () in
    -- create the vertex
    let v = RandomVarNode {ident = id, val = val, color = 0, dist = dist, plateId=cAcc.plateId, listId=None ()} in
    -- add the vertex to the graph and to the context
    let res = addVertex pbn cAcc (v,id) in
    match res with (pbn,cAcc) in
    -- if it is an observe, add it to the targets to be conditioned
    let targets = match t with TmObserve _ then cons id pbn.targets else pbn.targets in
    -- create edges to the created random variable node v from the nodes that it depends on
    let edges = setToSeq (createEdges v pbn cAcc (setEmpty cmprEdge) t) in
    let g = digraphAddEdges edges pbn.g in
    ({{pbn with targets=targets} with g=g},{{{cAcc with blockIdent=None()} with vertexId=None()} with isRet=false},Some v)
  | TmVar t -> if cAcc.isRet then createPBNGeneric pbn cAcc (TmVar t) else never -- aliases are removed
  | TmSeq t ->
    -- get the ident if it comes from a let expression
    let id = match cAcc.vertexId with Some id then id else nameSym "seq" in
    -- get the item vertices
    let items = map (lam v. match v with TmVar v in mapLookup v.ident pbn.m) t.tms in
    let v = if validList pbn items then
      let ids = map (lam v. match v with Some (RandomVarNode v) in v.ident) items in
        let items = map (lam r. match r with Some (RandomVarNode r) in RandomVarNode {r with listId=Some id}) items in
        let pbn = foldl (lam pbn. lam i.
          {{pbn with g=digraphAddUpdateVertex i pbn.g} with m=mapInsert id i pbn.m }
        ) pbn items in
        (ListNode {ident=id, items=ids,plateId=cAcc.plateId},pbn)
    else
        let res = createCodeBlock pbn cAcc (TmSeq t) (cAcc.vertexId,cAcc.blockIdent) in
        let edges = setToSeq (createEdges res.0 pbn cAcc (setEmpty cmprEdge) (TmSeq t)) in
        let g = digraphMaybeAddEdges edges pbn.g in
        (res.0,{pbn with g=g})
    in
    let res = addVertex v.1 cAcc (v.0,id) in
    let blockIdent = match v.0 with CodeBlockNode c then Some c.ident else None () in
    match res with (pbn,cAcc) in
    (pbn,{{cAcc with blockIdent=blockIdent} with vertexId=None()},Some v.0)
   | TmApp ({lhs=(TmApp ({lhs=TmConst ({val=CCreate()}&c),rhs=TmConst ({val=CInt {val=i}})})&a1),
              rhs=TmLam ({body=TmAssume {dist=TmDist {dist=dist}}}&l)}&a2) ->
    let id = match cAcc.vertexId with Some id then id else nameSym "create" in
    let accH = {{{cAcc with blockIdent=None()} with vertexId=None()} with isRet=false} in
    let res = mapAccumL (lam acc. lam. let res = createPBNH acc.0 acc.1 l.body in
                        ((res.0,res.1),res.2)) (pbn,accH) (make i 0) in
    match res with ((pbn,cAcc),items) in
    let items = map (lam i. match i with Some i then i else never) items in
    let itemIds = map getId items in
    let v = ListNode {ident=id,items=itemIds,plateId=cAcc.plateId} in
    let pbn = foldl (lam pbn. lam i. addVertexPBN pbn i) pbn items in
    let res = addVertex pbn cAcc (v,id) in
    match res with (pbn,cAcc) in
    let edges = setToSeq (createEdges v pbn cAcc (setEmpty cmprEdge) (TmApp a2)) in
    let g = digraphMaybeAddEdges edges pbn.g in
    ({pbn with g=g},{{cAcc with blockIdent=None ()} with vertexId=None()},Some v)
 | TmApp ({lhs=(TmApp ({lhs=TmConst ({val=CGet ()}&c),rhs=TmVar seq})&t2),rhs=TmVar ind}&a) ->
    let id = match cAcc.vertexId with Some id then id else nameSym "get" in
    let v =
      -- if there is no such list node created, create a codeblock
      match mapLookup seq.ident pbn.m with None () then
        (createCodeBlock pbn cAcc (TmApp a) (cAcc.vertexId,cAcc.blockIdent)).0
      else -- there is a list node created which consists of valid items
        MultiplexerNode {ident=id,indexId=ind.ident,listId=seq.ident,plateId=cAcc.plateId}
    in
    let res = addVertex pbn cAcc (v,id) in
    match res with (pbn,cAcc) in
    let edges = setToSeq (createEdges v pbn cAcc (setEmpty cmprEdge) (TmApp a)) in
    let g = digraphAddEdges edges pbn.g in
    let blockIdent = match v with CodeBlockNode c then Some c.ident else None () in
    ({pbn with g=g}, {{cAcc with blockIdent=blockIdent} with vertexId=None ()},Some v)
  | TmApp ({lhs=(TmApp ({lhs=TmConst ({val=CIter()}&c),rhs=TmLam l})&a1),rhs=TmVar lst}&a2) ->
    createPlate pbn cAcc [l.ident] l.body lst.ident (TmApp a2)
  | TmApp ({lhs=(TmApp ({lhs=TmConst ({val=CIteri()}&c),rhs=TmLam ({body=TmLam l2}&l1)})&a1),rhs=TmVar lst}&a2) ->
    createPlate pbn cAcc [l1.ident,l2.ident] l2.body lst.ident (TmApp a2)
  | t-> createPBNGeneric pbn cAcc t

  sem createPlate: PBN -> CreateAcc -> [Name] -> Expr -> Name -> Expr -> (PBN,CreateAcc,Option Vertex)
  sem createPlate pbn cAcc idents body lstId =
  | t ->
    let id = match cAcc.vertexId with Some id then id else never in
    let res = createPBN pbn {{{cAcc with blockIdent=None()} with plateId=Some id} with vertexId=None ()} body in
    match res with (pbnB,cAccB) in
    let v = PlateNode {ident=id, varIds=idents,listId=lstId, plateId=cAcc.plateId} in
    let res = addVertex pbnB cAcc (v,id) in
    match res with (pbn,cAcc) in
    let edges = setToSeq (createEdges v pbn cAcc (setEmpty cmprEdge) (nvar_ lstId)) in
    let g = digraphAddEdges edges pbn.g in
    ({pbn with g=g},{{{cAcc with vertexId= None ()} with blockIdent=None ()} with isRet=false},Some v)

  sem createPBNGeneric: PBN -> CreateAcc -> Expr -> (PBN,CreateAcc,Option Vertex)
  sem createPBNGeneric pbn cAcc =
  | t ->
    let t = match t with TmVar v then
      match mapLookup v.ident pbn.m with Some (PlateNode p) then unit_ else t else t in --?
    let v = createCodeBlock pbn cAcc t (cAcc.vertexId,cAcc.blockIdent) in
    let id = match cAcc.vertexId with Some id then id else v.1 in
    match addVertex pbn cAcc (v.0,id) with (pbn,cAcc) in
    let edges = setToSeq (createEdges v.0 pbn cAcc (setEmpty cmprEdge) t) in
    let g = digraphMaybeAddEdges edges pbn.g in
    let targets = findTargetRVs pbn.m pbn.targets t in
    let blockIdent = match v.0 with CodeBlockNode c then Some c.ident else None () in
    ({{pbn with g=g} with targets=targets},{{{cAcc with blockIdent=blockIdent} with vertexId=None ()} with isRet=false}, Some v.0)

end

lang RecreateProg = PBNGraph + MExprAst + MExprPPL

  sem extractPLVertices m v =
  | Some pid ->
      let vertices = mapLookupOrElse (lam. []) pid m in
      mapInsert pid (snoc vertices v) m
  | _ -> m

  sem recreate: PBN -> Expr
  sem recreate =
  | pbn ->
    let pbn = modifyGraph pbn in
    let order = digraphTopologicalOrder pbn.g in
    let vRet = filter (lam v.
      match v with CodeBlockNode c then
        let np = match c.plateId with Some _ then false else true in
        and c.ret np else false) order in
    let vRet = if eqi (length vRet) 0 then error "recreate:no return" else (get vRet 0) in
    let order = filter (lam v. match v with CodeBlockNode c then not c.ret else true) order in
    let plateVertices = foldl (lam acc. lam v. extractPLVertices acc v (getPlateId v)) (mapEmpty nameCmp) order in
    let order = filter (lam v. match getPlateId v with Some _ then false else true) order in
    recreateVertex plateVertices pbn (snoc order vRet)


  sem modifyGraph: PBN -> PBN
  sem modifyGraph =
  | pbn ->
    match pbn with {g=g,m=m,targets=targets} in
    let lists = filter (lam v. match v with ListNode _ then true else false) (digraphVertices g) in
    let g = foldl (lam g. lam l.
            match l with ListNode r in
            foldl (lam g:Digraph Vertex Label. lam id:Name.
                    let i = mapLookupOrElse (lam. error "modify:Lookup failed") id m in
                    let edges = digraphEdgesTo i g in
                    digraphMaybeAddEdges (map (lam e. (e.0,l,e.2)) edges) g) g r.items) g lists in
    {pbn with g=g}

  sem recreateCode plateVertices pbn =
  | CodeBlockNode t -> t.code
  | RandomVarNode v -> let body = match v.val with Some val then
    TmObserve {dist=dist_ v.dist, value=val,ty=tyunknown_, info = NoInfo ()}
    else TmAssume {dist=dist_ v.dist, ty=tyunknown_, info = NoInfo ()} in
    nulet_ v.ident body
  | MultiplexerNode m -> nulet_ m.ident (get_ (nvar_ m.listId) (nvar_ m.indexId))
  | ListNode l ->
    nulet_ l.ident (TmSeq {tms=(map (lam i. nvar_ i) l.items), ty=tyunknown_,info=NoInfo ()})
  | PlateNode p ->
    let vItems = mapLookupOrElse (lam. error "recreateCode:Lookup failed") p.ident plateVertices in
    let bdyIn = foldl (lam acc. lam v. bind_ acc (recreateCode plateVertices pbn v)) unit_ vItems in
    let body = if eqi (length p.varIds) 1 then (iter_ (nulam_ (get p.varIds 0) bdyIn) (nvar_ p.listId))
    else (iteri_ (nulam_ (get p.varIds 0) (nulam_ (get p.varIds 1) bdyIn)) (nvar_ p.listId)) in
    nulet_ p.ident body
  /-| FoldNode f ->
    let vItems = mapLookupOrElse (lam. error "recreateCode:Lookup failed") f.ident plateVertices in
    let vPRet = filter (lam v. match v with CodeBlockNode c then nameEq c.ident f.retBlock else false) vItems in
    let vPRet = get vPRet 0 in
    let vItems = filter (lam v. match v with CodeBlockNode c then not c.ret else true) vItems in
            let bdyIn = foldl (lam acc. lam v. bind_ acc (recreateVertex true plateVertices pbn [v])) unit_ (snoc vItems vPRet) in
            let bdy = foldl (lam acc. lam l. nulam_ l acc) bdyIn (snoc f.varIds f.accId ) in
            let ret = f.ret in
            let accName = f.acc in-/


  sem recreateVertex: Map Name [Vertex] -> PBN -> [Vertex] -> Expr
  sem recreateVertex plateVertices pbn =
  | [(CodeBlockNode v)&t] ++ as -> let code = (recreateCode plateVertices pbn t) in
    if v.ret then code else bind_ code (recreateVertex plateVertices pbn as)
  | [(RandomVarNode _)&t] ++ as -> bind_ (recreateCode plateVertices pbn t) (recreateVertex plateVertices pbn as)
  | [(MultiplexerNode _)&t] ++ as -> bind_ (recreateCode plateVertices pbn t) (recreateVertex plateVertices pbn as)
  | [(PlateNode _) & t] ++ as -> bind_ (recreateCode plateVertices pbn t) (recreateVertex plateVertices pbn as)
  | [(ListNode _) & t] ++ as -> bind_ (recreateCode plateVertices pbn t) (recreateVertex plateVertices pbn as)
  | [] -> unit_

end

let debug = false
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
          else (cons v acc.0, mapInsert v level acc.1,acc.2)
        ) acc (digraphSuccessors f g)) ([],dist,u) fs
      with (ns, dist, u) then
        if not u then u
        else
          work ns (addi level 1) dist u
      else never
    in
    work [source] 1 (mapInsert source 1 (mapEmpty (digraphCmpv g))) true


lang TransformPBN = ConjugatePrior
  type TAcc =
  {
    qDist:QDist,
    qpDist:QPDist,
    accName:Map Name Name,
    plateTBR:Set Name,
    plToAccParams:Map Name [Name],
    plToMV:Map Name (Set Name),
    plToRetParams:Map Name [Name],
    vToOutParams:Map Name Name,
    isConj:Bool
  }

  sem emptyTAcc: () -> TAcc
  sem emptyTAcc = 
  | _ -> {qDist=mapEmpty nameCmp, qpDist=mapEmpty nameCmp, accName=mapEmpty nameCmp,plateTBR=setEmpty nameCmp,plToAccParams=mapEmpty nameCmp,plToRetParams=mapEmpty nameCmp,vToOutParams=mapEmpty nameCmp,plToMV=mapEmpty nameCmp,isConj=true}

  sem plateToFold: PBN -> Name -> Name -> Name -> Name -> Vertex -> (PBN,Vertex)
  sem plateToFold pbn acc ret lamAcc retBlockName =
  | (PlateNode p)&plate -> 
    let foldN = FoldNode {ident=p.ident,varIds=p.varIds,accId=lamAcc,ret=ret,iter=p.listId,retBlock=retBlockName,plateId=p.plateId,acc=acc} in
    let edges = digraphEdgesTo plate pbn.g in
    let g = digraphRemoveVertex plate pbn.g in -- since constructor tag is diff should be removed
    let pbn = addVertexPBN {pbn with g=g} foldN in
    let g = foldl (lam g. lam e. 
                    match e with (e1,e2,l) in 
                    digraphAddEdge e1 foldN l g) pbn.g edges in
    ({pbn with g=g},foldN)
/-
  sem orderPlates: PBN -> [Name] -> [Name] -> [Name]  
  sem orderPlates pbn order =
  | [p] ++ as ->
    let plate = mapLookupOrElse (lam. error "Lookup failed") p pbn.m in
    match plate with PlateNode p in
    if any (lam v. mapMem v p.vertices) as then 
      snoc (orderPlates pbn order as) p.ident 
    else orderPlates pbn (snoc order p.ident) as 
  | [] -> order
-/
  sem transformPBN: (PBN,TAcc) -> PBN
  sem transformPBN  =
  | (pbn,tAcc) -> 
    let plates = filter (lam v. match v with PlateNode _ then true else false) (digraphVertices pbn.g) in
    /-let plateIds = (map getId plates) in
    let orderedPlates = orderPlates pbn [] plateIds in
    let targets = pbn.targets in
    let plateTargets = map (lam p. 
          let p = mapLookupOrElse (lam. error "Lookup failed") p pbn.m in
          match p with PlateNode p in
          filter (lam v. mapMem v p.vertices) targets) orderedPlates in
    let res = foldl (lam acc. lam targets.
      let res = transformPBNH acc targets in
      match res with (pbn,tAcc) in
      let res = transformPBNH (pbn,tAcc) (setToSeq tAcc.plateTBR) in
      match res with (pbn,tAcc) in
      if tAcc.isConj then res
      else acc) (pbn,tAcc) plateTargets in
    match res with (pbn,tAcc) in
    let plateIdsSet = setOfSeq nameCmp plateIds in
    let otherTargets = filter (lam t. not (mapMem t plateIdsSet)) pbn.targets in
    let res = transformPBNH pbn tAcc otherTargets in
    -/
    pbn

    sem transformPBNH: PBN -> TAcc -> [Name] -> PBN
    sem transformPBNH pbn tAcc =
    | [tId]++as -> 
      let t = mapLookupOrElse (lam. error "lookup failed.") tId pbn.m in
      let graftRes:(PBN,TAcc) = graft pbn tAcc t in
      match graftRes with (pbn,tAcc) in
      let t = mapLookupOrElse (lam. error "lookup failed.") tId pbn.m in
      let reorderRes:(PBN,TAcc) = reorder pbn tAcc  t in
      match reorderRes with (pbn,tAcc) in
      transformPBNH pbn tAcc as
    | [] -> pbn

  sem isMarginalized: TAcc -> Vertex -> Bool
  sem isMarginalized tAcc =
  | RandomVarNode v -> 
    match v.plateId with Some pid then
      if mapMem pid tAcc.qpDist then 
        let qDist = mapLookupOrElse (lam. error "Graft:Lookup failed.") pid tAcc.qpDist in
        mapMem v.ident qDist
      else false
    else mapMem v.ident tAcc.qDist

  sem isStabilized: PBN -> Vertex -> Bool
  sem isStabilized pbn =
  | RandomVarNode v -> if eqi v.color 0 then false else true
  | MultiplexerNode m -> 
    let l = mapLookupOrElse (lam. error "Marginalize:Lookup failed.") m.listId pbn.m in
    match l with ListNode l in
    foldl (lam acc. lam i.
      let i = mapLookupOrElse (lam. error "Marginalize:Lookup failed.") (get l.items 0) pbn.m in
      or acc (isStabilized pbn i)) false l.items
  
  sem checkList: PBN -> TAcc -> Vertex -> (PBN,TAcc,Vertex)
  sem checkList pbn tAcc =
  | (RandomVarNode v) & t ->
    match v.listId with Some lid then
      let children = digraphSuccessors t pbn.g in
      if null children then (pbn,tAcc,t)
      else 
        let lst = mapLookupOrElse (lam. error "Lookup failed") lid pbn.m in
        let res = graft pbn tAcc lst in
        let res = prune res.0 res.1 lst in
        match res with (pbn,tAcc) in
        (pbn,tAcc,mapLookupOrElse (lam. error "Lookup failed") v.ident pbn.m)
    else (pbn,tAcc,t)

  sem graft:PBN -> TAcc -> Vertex -> (PBN, TAcc)
  sem graft pbn tAcc =
  | (ListNode l) & t ->
      let children = digraphSuccessors t pbn.g in
      let res = foldl (lam acc. lam e.
            let e = mapLookupOrElse (lam. error "Marginalize:Lookup failed") e pbn.m in
            graft acc.0 acc.1 e) (pbn,tAcc) l.items in
      if gti (length children) 1 then 
        prune res.0 res.1 t
      else res
  | (RandomVarNode v) & t ->
    if eqi v.color 1 then (pbn,tAcc) else
    (if debug then print (join ["Graft(", v2str t,")\n"]) else ());
    -- if t is marginalized
    if isMarginalized tAcc t then
      (if debug then print "Graft: RV t is already marginalized\n" else ());
      -- get its children
      let children = digraphSuccessors t pbn.g in
      -- get its marginalized random variable child if any
      let child = filter (lam u. match u with RandomVarNode u then mapMem u.ident tAcc.qDist else false) children in
      -- if it does not have a marginalized child, then do nothing and return the graph
      (if null child then (pbn,tAcc)
      else
        -- it cannot have more than one marginalized child, throw error
        (if not (eqi (length child) 1) then error "Graft: can only have one marginalized child."
         else -- if it has one marginalized child
           let child = get child 0 in -- get that child
          (if debug then print (join ["child node ", (v2str child), " to be pruned\n"]) else ());
           -- prune the child so t will become the terminal node on its marginalized path
          prune pbn tAcc child))
    else
      (if debug then print "Graft: RV t is not marginalized\n" else ());
      let parents = filter (lam v. 
                          match v with (RandomVarNode _ | MultiplexerNode _) then
                            not (isStabilized pbn v)
                          else false) (digraphPredeccessors t pbn.g) in
      let children = digraphSuccessors t pbn.g in
      let children = filter (lam u. match u with RandomVarNode u then true else false) children in
      let hasListItemChild =
        any (lam c. match c with RandomVarNode r in match r.listId with Some _ then true else false) children in
      let res= if null parents then 
        (if debug then print (join ["Graft: t has no parents\n"]) else ());
        marginalize pbn tAcc t
      else
        let parent = get parents 0 in
        let res = 
          switch parent
          case RandomVarNode p then
            (if debug then print (join ["Graft: parent of t is a rv\n"]) else ());
            graft pbn tAcc parent
          case MultiplexerNode p then 
            (if debug then print "Graft: t's parent comes from a list\n" else ());
            let lst = mapLookupOrElse (lam. error "Lookup failed") p.listId pbn.m in
            graft pbn tAcc lst
          end
        in 
        marginalize res.0 res.1 t
      in
      let res = checkList res.0 res.1 t in
      match res with (pbn,tAcc,t) in
      (if hasListItemChild then prune pbn tAcc t else (pbn,tAcc))

  sem prune: PBN -> TAcc -> Vertex -> (PBN,TAcc)
  sem prune pbn tAcc =
  | (RandomVarNode v) & t ->
    -- pruned RV should already be marginalized
    (if debug then print (join ["Prune(", v2str t,")\n"]) else ());
    if not (isMarginalized tAcc t) then error "Prune: t is not marginalized"
    else
      -- get its marginalized child if any
      let children = filter (lam u. match u with RandomVarNode _ then 
          isMarginalized tAcc u else false) (digraphSuccessors t pbn.g) in
      -- if it does not have a marginalized child then reorder the vertex t.
      (if null children then reorder pbn tAcc t
      else
        match eqi (length children) 1 with false then error "Prune: t has more than one marginalized child" else
          -- if it has a marginalized child then prune it first.
          let res = prune pbn tAcc (get children 0) in
          reorder res.0 res.1 t)
  | (ListNode l) & t -> foldl (lam acc. lam e.
            let e = mapLookupOrElse (lam. error "Marginalize:Lookup failed") e pbn.m in
            prune acc.0 acc.1 e) (pbn,tAcc) l.items

  sem addToMarginalized: TAcc -> Name -> Dist -> Option Name -> TAcc
  sem addToMarginalized tAcc id q = 
  | Some pid ->
    if mapMem pid tAcc.qpDist then 
      let qDist = mapLookupOrElse (lam. error "Marginalize:Lookup failed.1") pid tAcc.qpDist in
      let qDist = mapInsert id q qDist in
      {tAcc with qpDist=mapInsert pid qDist tAcc.qpDist}
    else 
      let qDist = mapInsert id q (mapEmpty nameCmp) in
      {tAcc with qpDist=mapInsert pid qDist tAcc.qpDist}
  | None () -> {tAcc with qDist=mapInsert id q tAcc.qDist}

  sem marginalize: PBN -> TAcc -> Vertex -> (PBN,TAcc)
  sem marginalize pbn tAcc =
  | (RandomVarNode v) & t -> 
    (if debug then print (join ["Marginalize ", v2str t, "\n"]) else ());
    -- filter its random variable parents that are not stabilized
    let parents = filter (lam p. match p with RandomVarNode _ | MultiplexerNode _ then 
        not (isStabilized pbn p) else false) (digraphPredeccessors t pbn.g) in
    if null parents then
      (if debug then print (join ["Marginalize: no parents", "\n"]) else ());
      (pbn, addToMarginalized tAcc v.ident v.dist v.plateId)
    else
      (if debug then print (join ["Marginalize: has parents", "\n"]) else ());
      (let parent = get parents 0 in
     if not (modifiedBFS parent t pbn.g) then
        (if debug then print "Marginalize: can cause cycles reordering the parent\n" else ());
        let res = reorder pbn tAcc parent in
        marginalize res.0 res.1 t
      else
       let pdist = switch parent
        case RandomVarNode p then p.dist
        case MultiplexerNode p then
          let l = mapLookupOrElse (lam. error "Marginalize:Lookup failed.2") p.listId pbn.m in
          match l with ListNode l in l.dist
        end in
      if (isConjugatePrior (getId parent) (v.dist, pdist)) then
          let res = createMParameter pbn tAcc (t, parent) in
          match res with Some (pbn,tAcc,rho,q) then
            let g = digraphAddEdge rho t 0 pbn.g in
            let tAcc = addToMarginalized tAcc v.ident q v.plateId in
            ({pbn with g=g}, tAcc)
          else
            let res = reorder pbn tAcc parent in
            marginalize res.0 res.1 t
      else
        (if debug then print "Marginalize: no conjugate prior rel\n" else ());
        let res = reorder pbn tAcc parent in
        let res = marginalize res.0 res.1 t in
        (res.0,{res.1 with isConj=false}))

  sem isConnectedPl: PBN -> Name -> Name -> Bool
  sem isConnectedPl pbn outerPlate = 
  | innerPlate -> 
      match mapLookupOrElse (lam. error "Lookup failed.") innerPlate pbn.m with 
      (PlateNode {plateId=pid}|FoldNode {plateId=pid}) in
      match pid with Some pid then 
        or (nameEq pid outerPlate) (isConnectedPl pbn outerPlate pid)
      else false

  sem getPlateIdInOrder: PBN -> [Name] -> Option Name -> Option Name -> [Name]
  sem getPlateIdInOrder pbn plates stop =
  | innerPId ->  switch (stop,innerPId)
                        case (None (),Some pid) then 
                          let p = mapLookupOrElse (lam. error "") pid pbn.m in
                          getPlateIdInOrder pbn (cons pid plates) stop (getPlateId p)
                        case (None (), None ()) then plates 
                        case (Some pid, Some pid2) then
                          if nameEq pid pid2 then plates
                          else 
                            let p = mapLookupOrElse (lam. error "") pid2 pbn.m in
                            getPlateIdInOrder pbn (cons pid2 plates) stop (getPlateId p)
                        end

  sem createMParameter: PBN -> TAcc -> (Vertex,Vertex) -> Option (PBN,TAcc,Vertex,Dist)        
  sem createMParameter pbn tAcc =
  | (RandomVarNode v, RandomVarNode p) & t -> 
    switch (v.plateId, p.plateId)
    case (None (), None ()) then 
      createMParameterNP pbn tAcc t
    case (Some pid, Some pid2) then 
      if nameEq pid pid2 then
        createMParameterNP pbn tAcc t
      else
        if isConnectedPl pbn pid2 pid then
          --let res = createFoldParameters pbn tAcc t in
          createMParameterTDP pbn tAcc t
        else None ()
    case (Some pid, None ()) then 
        createMParameterTDP pbn tAcc t
    case (None (), Some pid) then None ()
    end
  | (RandomVarNode v, MultiplexerNode p) & t -> 
    let l = mapLookupOrElse (lam. error "Lookup failed.") p.listId pbn.m in
    match l with ListNode l in
    switch (v.plateId, p.plateId, l.plateId)
    case (None (), None (), None ()) then 
      (createMParameterNP pbn tAcc t)
    case (Some pid, None (), None ()) then 
        createMParameterTDP pbn tAcc t
    case (Some pid, Some pid2, None ()) then 
      if nameEq pid pid2 then
        createMParameterTDP pbn tAcc t --LDA case
      else None ()
    case (Some pid, Some pid2, Some pid3) then 
      if nameEq pid pid2 then
        if nameEq pid2 pid3 then
          (createMParameterNP pbn tAcc t)
        else 
          if isConnectedPl pbn pid3 pid2 then
            None () -- similar LDA case
          else None ()
      else 
        if nameEq pid2 pid3 then
          if isConnectedPl pbn pid2 pid then
              createMParameterTDP pbn tAcc t
          else None ()
        else None ()
    case (None (), Some pid2, Some pid3) then None ()
    case (None (), None (), Some pid3) then None ()
    case (None (), Some pid, None ()) then None ()
    case (Some pid, None (), Some pid2) then None ()
    end

  sem createMParameterTDP: PBN -> TAcc -> (Vertex, Vertex) ->  Option (PBN,TAcc,Vertex,Dist)
  sem createMParameterTDP pbn tAcc =
  | (RandomVarNode v, (RandomVarNode _ | MultiplexerNode _)&p) & t  ->
    (if debug then print (join ["createMParameterTDP",v2str t.0,"\n"]) else ());
    let outerPlateId = match p with MultiplexerNode m then
      match mapLookup m.listId pbn.m with Some (ListNode l) in l.plateId else (getPlateId p) in 
    let plateOrder = getPlateIdInOrder pbn [] outerPlateId v.plateId in
    let res = foldl (lam acc. lam p. 
      match acc with (pbn,tAcc,ppid,outNames) in 
      let res = createMFoldParameter pbn tAcc (p,ppid,t.1) in 
      (res.0,res.1,Some p,snoc outNames res.2 )
    ) (pbn,tAcc,outerPlateId,[]) plateOrder in
    match res with (pbn,tAcc,_,outNames) in
    let res = foldl (lam acc. lam p.
      match acc with (pbn,tAcc,i) in
      match mapLookup p pbn.m with Some (FoldNode f) in
      --print (v2str (FoldNode f));
      let outName = get outNames i in
      match outName with Some outName then
        let params = match mapLookup f.ident tAcc.plToRetParams with Some params then params else [] in
        let params = snoc params outName in
        let tAcc = {tAcc with plToRetParams=mapInsert f.ident params tAcc.plToRetParams} in
        let rbCode = utuple_ (map nvar_ params) in
        let returnBlock = CodeBlockNode {ident=f.retBlock,code=rbCode,ret=true,plateId=Some f.ident} in
        let pbn = addVertexPBN pbn returnBlock in 
      (pbn,tAcc,addi i 1)
      else (pbn,tAcc,addi i 1)
    ) (pbn,tAcc,1) (init plateOrder) in
    match res with (pbn,tAcc,_) in
    let tAcc =
      if null outNames then tAcc
      else match head outNames with Some outName then
       {tAcc with vToOutParams=mapInsert (getId t.1) outName tAcc.vToOutParams}
      else tAcc in
    createMParameterTDPH pbn tAcc t

  sem createMFoldParameter: PBN -> TAcc -> (Name, Option Name, Vertex) -> (PBN,TAcc,Option Name)
  sem createMFoldParameter pbn tAcc =
  | (tpid, ppid, (RandomVarNode _ | MultiplexerNode _)) & t  ->
    (if debug then print (join ["createMFoldParameter","\n"]) else ());
    let outerDependencies = match mapLookup tpid tAcc.plToMV with Some vertices then vertices else setEmpty nameCmp in
    let oldAcc = mapMem (getId t.2) outerDependencies in
    if oldAcc then  -- if the outside dependency already reordered within plate use those params
      (if debug then print (join ["createMFoldParameter:already in plate acc","\n"]) else ());
      (pbn,tAcc,None ())
    else
      let qDist = match ppid with Some pid then
          mapLookupOrElse (lam. error "Lookup failed") pid tAcc.qpDist else tAcc.qDist in
      -- checks whether fold already has an accumulator name
      let res = if mapMem tpid tAcc.accName then 
          (tAcc,mapLookupOrElse (lam. error "") tpid tAcc.accName)
        else let accVarName = (nameSym "acc") in
          ({tAcc with accName=mapInsert tpid accVarName tAcc.accName},accVarName) in
      match res with (tAcc, accVarName) in
      -- creates a codeblock getting the correct acc param, e.g. let param = get acc 0 in
      let pName = (nameSym "paramx") in
      let num = match mapLookup tpid tAcc.plToAccParams with Some accParams then length accParams else 0 in
      let cb = CodeBlockNode {ident=nameSym "", code=nulet_ pName (tupleproj_ num (nvar_ accVarName)),ret=false,plateId=Some tpid} in
      let pbn = addVertexPBN pbn cb in 
      let plate = mapLookupOrElse (lam. error "") tpid pbn.m in
      let retName = nameSym "ret" in
      let res = plateToFoldM pbn tAcc (nameSym "paramy") (nameSym "params") retName ppid (t.2,plate) in
      match res with (pbn,tAcc) in
      match mapLookup tpid pbn.m with Some (FoldNode f) in
      let outName = nameSym "postParam" in
      let num = match mapLookup tpid tAcc.plToRetParams with Some retParams then length retParams else 0 in
      let outputBlock = CodeBlockNode {ident=outName, code=nulet_ outName (tupleproj_ num (nvar_ f.ret)),ret=false,plateId=ppid} in
      let g = digraphAddEdge (FoldNode f) outputBlock 0 pbn.g in
      let pbn = addVertexPBN {pbn with g=g} outputBlock in

      let res = match t.2 with MultiplexerNode m then 
        match mapLookup m.listId pbn.m with Some (ListNode l) in
        let res = foldl (lam acc. lam i. match acc with (pbn,tAcc,cnt) in
          let pNameL = (nameSym "paramz") in
          match mapLookup i pbn.m with Some (RandomVarNode i) in
          let cb = CodeBlockNode {ident=nameSym "",code=nulet_ pNameL (get_ (nvar_ pName) (int_ cnt)),ret=false,plateId=Some tpid}  in
          let pbn = addVertexPBN pbn cb in 
          let pMarginalizedDist = mapLookupOrElse (lam. error "Lookup failed") i.ident qDist in
          let pChanged = changeParams pNameL pMarginalizedDist in
          let qtDist = match mapLookup tpid tAcc.qpDist with Some qDist then qDist else mapEmpty nameCmp in
          let qtDist = mapInsert i.ident pChanged qtDist in
          let qpDist = mapInsert tpid qtDist tAcc.qpDist in
          (pbn,{tAcc with qpDist=qpDist},addi cnt 1)
          ) (pbn,tAcc,0) l.items in (res.0,res.1)
      else 
        let pMarginalizedDist = mapLookupOrElse (lam. error "Lookup failed") (getId t.2) qDist in
        let pChanged = changeParams pName pMarginalizedDist in
        let qtDist = match mapLookup tpid tAcc.qpDist with Some qDist then qDist else mapEmpty nameCmp in
        let qtDist = mapInsert (getId t.2) pChanged qtDist in
        let qpDist = mapInsert tpid qtDist tAcc.qpDist in
        (pbn,{tAcc with qpDist=qpDist})
      in
      (res.0,res.1,Some outName)

  sem createMParameterTDPH: PBN -> TAcc -> (Vertex, Vertex) -> Option (PBN,TAcc,Vertex,Dist)
  sem createMParameterTDPH pbn tAcc =
  | (RandomVarNode t, RandomVarNode p)&v ->
    (if debug then print (join ["createMParameterTDPH",v2str v.0,"\n"]) else ());
    match t.plateId with Some tpid in
    let qtDist = match mapLookup tpid tAcc.qpDist with Some qDist then qDist else mapEmpty nameCmp in
    let pMarginalizedDist =
      -- if parent is already marginalized in the plate of t
      if mapMem p.ident qtDist then
        mapLookupOrElse (lam. error "Lookup failed") p.ident qtDist
      else
        let qDist = match p.plateId with Some pid then
          mapLookupOrElse (lam. error "Lookup failed") pid tAcc.qpDist else tAcc.qDist in
        mapLookupOrElse (lam. error "Lookup failed") p.ident qDist in
    let res = posteriorPredictive t.plateId (t.dist,pMarginalizedDist) in
    match res with (rho,q) in
    let pbn = addVertexPBN pbn rho in
    -- inherit the dependencies
    let pbn = inheritMDependencies pbn tAcc rho v.0 in
    let pbn = inheritMDependencies pbn tAcc rho v.1 in
    let tAcc = {tAcc with plateTBR=setInsert t.ident tAcc.plateTBR} in
    Some (pbn,tAcc,rho,q)
  | (RandomVarNode t, MultiplexerNode p)&v -> 
    let l = mapLookupOrElse (lam. error "createMParameterNP:lookup failed.4") p.listId pbn.m in
    match l with ListNode l in
    let res = foldl (lam acc. lam i.
      match acc with (pbn,tAcc,items,dists,cnt) in
      let i = mapLookupOrElse (lam. error "createMParameterNP:Lookup failed.5") i pbn.m in
      let res = createMParameterTDPH pbn tAcc (v.0,i) in
      match res with Some (pbn,tAcc,rho,dist) in
      (pbn,tAcc,snoc items rho,snoc dists dist,addi cnt 1)) (pbn, tAcc,[], [],0) l.items in 
    match res with (pbn,tAcc,items,dists,_) in
    let ppl = posteriorPredictiveL t.plateId p.indexId dists in
    match ppl with (rho, q) in
    let pbn = addVertexPBN pbn rho in
    let pbn = inheritMDependencies pbn tAcc rho v.1 in
    let g = foldl (lam g. lam i. digraphMaybeAddEdge i rho 0 g) pbn.g items in
    Some ({pbn with g=g},tAcc,rho,q) 

  sem createParentParam: PBN -> TAcc -> Option Name -> Vertex -> Expr
  sem createParentParam pbn tAcc ppid =
  | (RandomVarNode _ | MultiplexerNode _)&v->
    let qDist = match ppid with Some ppid then
        mapLookupOrElse (lam. error "plateToFoldM:Lookup failed.1") ppid tAcc.qpDist
      else tAcc.qDist in
    match v with MultiplexerNode p then
      match mapLookup p.listId pbn.m with Some (ListNode l) in
      (seq_ (foldl (lam params. lam id.
        let pMarginalizedDist = mapLookupOrElse (lam. error "Lookup failed") id qDist in 
        snoc params (getParams pMarginalizedDist)
      ) [] l.items))
    else 
      let pMarginalizedDist = mapLookupOrElse (lam. error "plateToFoldM:Lookup failed.2") (getId v) qDist in 
      (getParams pMarginalizedDist)

  sem plateToFoldM: PBN -> TAcc -> Name -> Name -> Name -> Option Name -> (Vertex,Vertex) -> (PBN,TAcc)
  sem plateToFoldM pbn tAcc paramId paramsId ret ppid =
  | ((RandomVarNode _ | MultiplexerNode _), (PlateNode _ | FoldNode _))&v->
    (if debug then print (join ["plateToFoldM:PL","\n"]) else ());
    let oldAcc = match mapLookup (getId v.1) tAcc.plToMV with Some vertices then
       mapMem (getId v.0) vertices else false in
    if oldAcc then (pbn,tAcc) else
    let param = createParentParam pbn tAcc ppid v.0 in
    let cbParentP = CodeBlockNode {ident=nameSym "",code=(nulet_ paramId param),ret=false,plateId=ppid} in
    let pbn = addVertexPBN pbn cbParentP in
    let res = plateToFoldMH pbn tAcc paramId paramsId ret ppid v in
    match res with (pbn,tAcc,cbAcc) in
    let pbn = inheritMDependencies pbn tAcc cbParentP v.0 in
    let g = digraphAddEdge cbParentP cbAcc 0 pbn.g in
    ({pbn with g=g},tAcc)

sem plateToFoldMH: PBN -> TAcc -> Name -> Name -> Name -> Option Name -> (Vertex,Vertex) -> (PBN,TAcc,Vertex)
sem plateToFoldMH pbn tAcc paramId paramsId ret ppid =
| ((RandomVarNode _ | MultiplexerNode _), PlateNode pl)&v->
    (if debug then print (join ["plateToFoldMH:PL","\n"]) else ());
    let cbAcc = CodeBlockNode {ident=paramsId ,code=(nulet_ paramsId (utuple_ [nvar_ paramId])),ret=false, plateId=ppid} in   
    let pbn = addVertexPBN pbn cbAcc in
    let accVarName = mapLookupOrElse (lam. error "plateToFoldMH:Lookup failed") pl.ident tAcc.accName in
    let res = plateToFold pbn paramsId ret accVarName (nameSym "retCB") v.1 in
    match res with (pbn, foldN) in
    let g = digraphAddEdge cbAcc foldN 0 pbn.g in
    let tAcc = {tAcc with plToAccParams = mapInsert pl.ident [paramId] tAcc.plToAccParams} in 
    ({pbn with g=g},tAcc,cbAcc)
  | ((RandomVarNode _ | MultiplexerNode _), FoldNode f)&v->
    (if debug then print (join ["plateToFoldMH:Fold","\n"]) else ());
    let params = snoc (mapLookupOrElse (lam. error "Lookup failed") f.ident tAcc.plToAccParams) paramId in
    match mapLookup f.acc pbn.m with Some (CodeBlockNode c) in
    let cbAcc = CodeBlockNode {c with code =(nulet_ f.acc (utuple_ (map nvar_ params)))} in
    let pbn = addVertexPBN pbn cbAcc in
    let tAcc = {tAcc with plToAccParams = mapInsert f.ident params tAcc.plToAccParams} in 
    (pbn,tAcc,cbAcc)

  sem createMParameterNP: PBN -> TAcc -> (Vertex, Vertex) -> Option (PBN,TAcc,Vertex,Dist)
  sem createMParameterNP pbn tAcc =
  | (RandomVarNode t, RandomVarNode p)&v ->
    let qDist = match p.plateId with Some pid then
      mapLookupOrElse (lam. error "createMParameterNP:Lookup failed.1") pid tAcc.qpDist
      else tAcc.qDist in
    let pMarginalizedDist = mapLookupOrElse (lam. error "createMParameterNP:Lookup failed.2") p.ident qDist in
    let res = posteriorPredictive t.plateId (t.dist, pMarginalizedDist) in
    match res with (rho,q) in
    let pbn = addVertexPBN pbn rho in
    -- inherit the dependencies
    let pbn = inheritMDependencies pbn tAcc rho v.0 in
    let pbn = inheritMDependencies pbn tAcc rho v.1 in
    Some (pbn, tAcc,rho, q)
  | (RandomVarNode t, MultiplexerNode p)&v -> 
    let l = mapLookupOrElse (lam. error "createMParameterNP:lookup failed.4") p.listId pbn.m in
    match l with ListNode l in
    let res = foldl (lam acc. lam i.
      match acc with (pbn,tAcc,items,dists) in
      let i = mapLookupOrElse (lam. error "createMParameterNP:Lookup failed.5") i pbn.m in
      match i with RandomVarNode r in
      let res = createMParameterNP pbn tAcc (v.0,i) in
      match res with Some (pbn,tAcc,rho,dist) in
      (pbn,tAcc,snoc items rho,snoc dists dist)) (pbn, tAcc,[], []) l.items in 
    match res with (pbn,tAcc,items,dists) in
    let ppl = posteriorPredictiveL t.plateId p.indexId dists in
    match ppl with (rho, q) in
    let pbn = addVertexPBN pbn rho in
    let pbn = inheritMDependencies pbn tAcc rho v.1 in
    let g = foldl (lam g. lam i. digraphMaybeAddEdge i rho 0 g) pbn.g items in
    Some ({pbn with g=g},tAcc,rho,q) 

  sem inheritMDependencies: PBN -> TAcc -> Vertex -> Vertex -> PBN
  sem inheritMDependencies pbn tAcc toV =
  | (MultiplexerNode m)&fromV -> 
    let parents = filter (lam v. match v with CodeBlockNode _ then true
                            else match v with RandomVarNode r then true
                            else false) (digraphPredeccessors fromV pbn.g) in
    let g = foldl (lam acc. lam gp. digraphMaybeAddEdge gp toV 0 acc) pbn.g parents in
    {pbn with g=g}
  | fromV ->
    -- get the codeblock parents and stabilized nodes of t
    let parents = filter (lam v. match v with CodeBlockNode _ then true
                            else match v with RandomVarNode r then
                              match r.plateId with Some pid then
                                  if mapMem pid tAcc.qpDist then
                                    let qDist = mapLookupOrElse (lam. error "Lookup failed.") pid tAcc.qpDist in
                                    not (mapMem r.ident qDist)
                                  else true
                                else
                                not (mapMem r.ident tAcc.qDist)
                            else /-match v with MultiplexerNode m then
                              match m.plateId with Some pid then 
                                let qDist = mapLookupOrElse (lam. error "Lookup failed.") pid tAcc.qpDist in
                                not (mapMem m.ident qDist)
                              else not (mapMem m.ident tAcc.qDist)
                            else-/
                            false) (digraphPredeccessors fromV pbn.g) in
    let g = foldl (lam acc. lam gp. digraphMaybeAddEdge gp toV 0 acc) pbn.g parents in
    {pbn with g=g}


  sem reorder: PBN -> TAcc -> Vertex -> (PBN,TAcc)
  sem reorder pbn tAcc =
  | (RandomVarNode v) & t -> 
    (if debug then print (join ["Reorder ", v2str t, "\n"]) else ());
    if eqi v.color 1 then (pbn,tAcc) else
    let parents = filter (lam v. 
                          match v with (RandomVarNode _ | MultiplexerNode _) then
                            not (isStabilized pbn v)
                          else false) (digraphPredeccessors t pbn.g) in
    if null parents then --if it has no rv parents then directly stabilize the node
      (if debug then print ("Random variable has no parents so directly stabilize") else ());
      -- change its color from 0 to 1 [from assumed to stabilized]
      -- set its distribution as its marginalized distribution
      let res = popFromMarginalized tAcc t in
      match res with (tAcc, sDist) in
      let stabilizedT = RandomVarNode {{v with color=1} with dist=sDist} in
      let pbn = addVertexPBN pbn stabilizedT in
      (pbn, tAcc)
    else 
      let parent = get parents 0 in
      let pbn = {pbn with g=digraphRemoveEdge parent t 0 pbn.g} in
      let res = createRParameter pbn tAcc (t,parent) in
      match res with (pbn,tAcc) in
      let qDist = match v.plateId with Some pid then
        mapLookupOrElse (lam. error "reorder:Lookup failed.") pid tAcc.qpDist
      else tAcc.qDist in
      let stabilizedT = RandomVarNode {{v with color=1} with dist=mapLookupOrElse (lam. error "reorder:Lookup failed") v.ident qDist} in
      let pbn = addVertexPBN pbn stabilizedT in
      let res = popFromMarginalized tAcc stabilizedT in
      (pbn,res.0)
  | MultiplexerNode p -> 
    let l = mapLookupOrElse (lam. error "Marginalize:Lookup failed.2") p.listId pbn.m in
    reorder pbn tAcc l
  | (ListNode l) & t -> 
    foldl (lam acc. lam i.
      let i = mapLookupOrElse (lam. error "Lookup failed") i pbn.m in
      reorder acc.0 acc.1 i) (pbn,tAcc) l.items
            
  sem popFromMarginalized: TAcc -> Vertex -> (TAcc,Dist)
  sem popFromMarginalized tAcc = 
  | RandomVarNode t ->
    match t.plateId with Some pid then
      let qDist = mapLookupOrElse (lam. error "popFromMarginalized:Lookup failed.") pid tAcc.qpDist in
      let dist = mapLookupOrElse (lam. error "popFromMarginalized:Lookup failed") t.ident qDist in
      let qDist = mapRemove t.ident qDist in
      let qpDist = mapInsert pid qDist tAcc.qpDist in
      ({tAcc with qpDist=qpDist},dist)
    else 
    let dist = mapLookupOrElse (lam. error "popFromMarginalized:Lookup failed") t.ident tAcc.qDist in
    let qDist = mapRemove t.ident tAcc.qDist in
    ({tAcc with qDist=qDist},dist)

  sem createRParameter: PBN -> TAcc -> (Vertex,Vertex) -> (PBN,TAcc)
  sem createRParameter pbn tAcc =
  | (RandomVarNode v, RandomVarNode p) & t -> 
    (if debug then print (join ["createRParameter ", v2str t.0, "\n"]) else ());
    switch (v.plateId, p.plateId)
    case (None (), None ()) then 
      createRParameterNP pbn tAcc (None ()) t
    case (Some pid, Some pid2) then 
      if nameEq pid pid2 then
        createRParameterNP pbn tAcc (None ()) t
      else 
        if isConnectedPl pbn pid2 pid then
          createRParameterTDP pbn tAcc t
        else never
    case (Some pid, None ()) then
      createRParameterTDP pbn tAcc t
    case (None (), Some pid) then never
    end
  | (RandomVarNode v, MultiplexerNode p) & t -> 
    (if debug then print (join ["createRParameterMux ", v2str t.0, "\n"]) else ());
    match mapLookup p.listId pbn.m with Some (ListNode l) in
    switch (v.plateId, p.plateId, l.plateId)
    case (None (), None (), None ()) then 
      createRParameterNP pbn tAcc (None ()) t
    case (Some pid, None (), None ()) then 
      createRParameterTDP pbn tAcc t
    case (Some pid, Some pid2, None ()) then 
      if nameEq pid pid2 then  
        let res = createRParameterTDP pbn tAcc t in
        let pbn = removeVertexPBN res.0 t.1 in
        (pbn,res.1)
      else never
     --LDA case
    case (Some pid, Some pid2, Some pid3) then
      if nameEq pid pid2 then
        if nameEq pid2 pid3 then
          (createRParameterNP pbn tAcc (None ()) t)
        else 
          if isConnectedPl pbn pid3 pid2 then
            never -- similar LDA case
          else never
      else 
        if nameEq pid2 pid3 then
          if isConnectedPl pbn pid2 pid then
            createRParameterTDP pbn tAcc t
          else never
        else never
    case (None (), Some pid2, Some pid3) then never
    case (None (), None (), Some pid3) then never
    case (None (), Some pid, None ()) then never
    case (Some pid, None (), Some pid2) then never
    end

  sem outerMostPlate: PBN -> (Option Name,Option Name)-> Vertex
  sem outerMostPlate pbn  = 
  | (Some innerPId, stop) -> match mapLookup innerPId pbn.m with Some ((FoldNode {plateId=pid} | PlateNode {plateId=pid})&v) in
                             match pid with Some p then
                              match stop with Some p2 then 
                                if nameEq p p2 then v 
                                else outerMostPlate pbn (pid,stop)
                              else outerMostPlate pbn (pid,stop) else v
  sem createRParameterTDP: PBN -> TAcc -> (Vertex,Vertex) -> (PBN,TAcc)
  sem createRParameterTDP pbn tAcc =
  | (RandomVarNode v, (RandomVarNode _ | MultiplexerNode _)) & t  -> 
    (if debug then print (join ["createRParameterTDP", v2str t.0, "\n"]) else ());
    let ppid = match t.1 with MultiplexerNode m then 
      match mapLookup m.listId pbn.m with Some (ListNode l) in l.plateId 
      else getPlateId t.1 in
    match v.plateId with Some tpid in
    let outerDependencies = match mapLookup tpid tAcc.plToMV with Some vertices then vertices else setEmpty nameCmp in
    let oldAcc = mapMem (getId t.1) outerDependencies in
    let tAcc = {tAcc with plToMV=mapInsert tpid (setInsert (getId t.1) outerDependencies) tAcc.plToMV} in
    --match outerMostPlate pbn (v.plateId,(getPlateId t.1)) with (FoldNode f) in
    let outName = mapLookup (getId t.1) tAcc.vToOutParams in
    let outputBlock = match outName with Some outName then mapLookup outName pbn.m else None () in
    let res = createRParameterTDPH pbn tAcc outName outputBlock (None ()) t in
    match res with (pbn,tAcc,paramName) in
    let params = match mapLookup tpid tAcc.plToRetParams with Some params then params else [] in
    let params = snoc params paramName in
    let tAcc = {tAcc with plToRetParams=mapInsert tpid params tAcc.plToRetParams} in
    let rbCode = if oldAcc then utuple_ [(nvar_ (last params))]
      else utuple_ (map nvar_ params) in
    match mapLookup tpid pbn.m with Some (FoldNode f) in
    let returnBlock = CodeBlockNode {ident=f.retBlock, code=rbCode,ret=true,plateId=v.plateId} in
    let pbn = addVertexPBN pbn returnBlock in
    (pbn,tAcc)

  sem createRParameterTDPH: PBN -> TAcc -> Option Name -> Option Vertex -> Option (Name,Expr) -> (Vertex,Vertex) -> (PBN,TAcc,Name)
  sem createRParameterTDPH pbn tAcc ret outBlock indices =
  | (RandomVarNode t, RandomVarNode p)&v ->
    (if debug then print (join ["createRParameterTDPH", v2str v.1, "\n"]) else ());
    let obs = match t.val with Some _ then t.val else Some (nvar_ t.ident) in
    match t.plateId with Some tpid in
    let qDist = mapLookupOrElse (lam. error "createRParameterTDPH:Lookup failed.1") tpid tAcc.qpDist in
    let pMarginalizedDist = mapLookupOrElse (lam. error "createRParameterTDPH:Lookup failed.2") p.ident qDist in
    let res = posterior obs indices t.plateId (t.dist,pMarginalizedDist) in
    match res with (rho,q,paramNames) in
    let pbn = addVertexPBN pbn rho in
    let paramName = nameSym "rP" in
    let paramBlock = CodeBlockNode {ident=paramName, code=nulet_ paramName (utuple_ (map nvar_ paramNames)),ret=false,plateId=t.plateId} in
    let pbn = addVertexPBN pbn paramBlock in
    let pbn = {pbn with g=digraphAddEdge rho paramBlock 0 pbn.g} in
    let tAcc = {tAcc with qpDist=mapInsert tpid (mapInsert p.ident q qDist) tAcc.qpDist} in
    let res = 
      match ret with Some ret then
        let q = changeParams ret q in
        let updatedP = RandomVarNode {p with dist=q} in
        let pbn = addVertexPBN pbn updatedP in
        let g = match outBlock with Some outBlock then 
          digraphMaybeAddEdge outBlock updatedP 0 pbn.g 
        else pbn.g in
        let tAcc = 
          match p.plateId with Some pid then
            let qDist = mapLookupOrElse (lam. error "createRParameterTDPH:Lookup failed.1") pid tAcc.qpDist in
            {tAcc with qpDist=mapInsert pid (mapInsert p.ident q qDist) tAcc.qpDist} 
          else
            {tAcc with qDist=mapInsert p.ident q tAcc.qDist}  in ({pbn with g=g},tAcc)
      else (pbn,tAcc) in
    match res with (pbn,tAcc) in
    --let pbn = inheritRDependencies pbn tAcc (v.0,v.1,rho) in
    let g = digraphAddEdge v.0 rho 0 pbn.g in
    ({pbn with g=g}, tAcc, paramName)
  | (RandomVarNode t, MultiplexerNode p)&v ->
    (if debug then print (join ["createRParameterTDPHMux", v2str v.0, "\n"]) else ());
    match t.plateId with Some tpid in
    match mapLookup tpid pbn.m with Some (FoldNode f) in
    match mapLookup p.listId pbn.m with Some (ListNode l) in
    let res = foldl (lam acc. lam i.
      match acc with (pbn,tAcc,rets,cnt) in
      let i = mapLookupOrElse (lam. error "createRParameterTDPHMux:Lookup failed.2") i pbn.m in
      let retN = (nameSym "r") in
      let pbn = match (ret,outBlock) with (Some ret,Some outputBlock) then
        let cb = CodeBlockNode {ident=nameSym "", code=nulet_ retN (get_ (nvar_ ret) (int_ cnt)),ret=false,plateId=l.plateId} in
        let pbn = addVertexPBN pbn cb in
        let g = digraphAddEdge outputBlock cb 0 pbn.g in
        {pbn with g=digraphAddEdge cb i 0 g}
      else pbn in
      let res = createRParameterTDPH pbn tAcc (Some retN) outBlock (Some (p.indexId,int_ cnt)) (v.0,i) in
      match res with (pbn,tAcc,paramName) in
      (res.0,res.1,snoc rets paramName,addi cnt 1)
      ) (pbn,tAcc,[],0) l.items in 
    let pName = nameSym "l" in
    let rb = CodeBlockNode {ident=nameSym "",code=nulet_ pName (seq_ (map nvar_ res.2)),ret=false,plateId=t.plateId} in
    let pbn = addVertexPBN res.0 rb in
    let g = foldl (lam g. lam p. digraphAddEdge (mapLookupOrElse (lam. error "") p pbn.m) rb 0 g) pbn.g res.2 in
   -- let g = digraphRemoveEdge (ListNode l) v.1 0 g in
    let g = match outBlock with Some outBlock then 
      digraphAddEdge outBlock (ListNode l) 0 g else g in
    ({pbn with g=g},res.1,pName)

  sem createRParameterNP: PBN -> TAcc -> Option (Name,Expr) -> (Vertex, Vertex) -> (PBN,TAcc)
  sem createRParameterNP pbn tAcc indices =
  | (RandomVarNode t, RandomVarNode p)&v ->
    (if debug then print (join ["createRParameterNP ", v2str v.0, "\n"]) else ());
    let obs = match t.val with Some _ then t.val else Some (nvar_ t.ident) in
    let qDist = match p.plateId with Some pid then
      mapLookupOrElse (lam. error "createRParameterNP:Lookup failed.1") pid tAcc.qpDist
      else tAcc.qDist in
    let pMarginalizedDist = mapLookupOrElse (lam. error "createRParameterNP:Lookup failed.2") p.ident qDist in
    let res = posterior obs indices t.plateId (t.dist,pMarginalizedDist) in
    match res with (rho,q,_) in
    let updatedP = RandomVarNode {p with dist=q} in
    let pbn = addVertexPBN pbn rho in
    let pbn = addVertexPBN pbn updatedP in
    let pbn = inheritRDependencies pbn tAcc (v.0,v.1,rho) in
    let g = digraphAddEdge rho updatedP 0 pbn.g in
    let g = digraphAddEdge v.0 rho 0 g in
    let tAcc = match p.plateId with Some pid then
      let qDist = mapInsert p.ident q qDist in
      {tAcc with qpDist=mapInsert pid qDist tAcc.qpDist}
      else {tAcc with qDist=mapInsert p.ident q tAcc.qDist} in
    ({pbn with g=g}, tAcc)
  | (RandomVarNode t, MultiplexerNode p)&v ->
    let l = mapLookupOrElse (lam. error "Lookup failed.") p.listId pbn.m in
    match l with ListNode l in
    let res = foldl (lam acc. lam i.
      match acc with (pbn,tAcc,cnt) in
      let i = mapLookupOrElse (lam. error "Marginalize:Lookup failed") i pbn.m in
      let res = createRParameterNP pbn tAcc (Some (p.indexId,int_ cnt)) (v.0,i) in
      (res.0,res.1,addi 1 cnt)
      ) (pbn,tAcc,0) l.items in
    (res.0,res.1)


  sem inheritRDependencies: PBN -> TAcc -> (Vertex, Vertex, Vertex) -> PBN
  sem inheritRDependencies pbn tAcc =
  | (t, p, rho) -> 
  let filterC = (lam v. match v with CodeBlockNode _ then true
                              else match v with RandomVarNode r then
                                match r.plateId with Some pid then
                                  if mapMem pid tAcc.qpDist then
                                    let qDist = mapLookupOrElse (lam. error "Lookup failed.") pid tAcc.qpDist in
                                    not (mapMem r.ident qDist)
                                  else true
                                else
                                not (mapMem r.ident tAcc.qDist)
                              else /-match v with MultiplexerNode m then
                                match m.plateId with Some pid then 
                                let qDist = mapLookupOrElse (lam. error "Lookup failed.") pid tAcc.qpDist in
                                not (mapMem m.ident qDist)
                              else not (mapMem m.ident tAcc.qDist)
                              else-/ false) in
  let parentsT = filter filterC (digraphPredeccessors t pbn.g) in
  -- get the codeblock parents and stabilized nodes of p
  let parentsP = filter filterC (digraphPredeccessors p pbn.g) in
  -- inherit the dependencies
  let g = foldl (lam acc. lam gp. digraphMaybeAddEdge gp rho 0 acc) pbn.g parentsT in
  let g = foldl (lam acc. lam gp. let g = digraphRemoveEdge gp p 0 acc in digraphMaybeAddEdge gp rho 0 g) g parentsP in
  {pbn with g=g}
end

lang Transformation = CreatePBN + TransformPBN + RecreateProg + MExprPPLStaticDelayedANF


  sem removeAlias env =
  | TmLet ({body=TmVar v}&t) ->
    let env = match mapLookup v.ident env with Some id then
    mapInsert t.ident id env else mapInsert t.ident v.ident env in
    removeAlias env t.inexpr
  | TmVar t -> match mapLookup t.ident env with Some id then nvar_ id else TmVar t
  | t -> smap_Expr_Expr (removeAlias env) t
  -- make sure to get the length for create
  sem constantFoldCreate: Map Name Expr -> Expr -> Expr
  sem constantFoldCreate env =
  | TmLet ({body=TmApp ({lhs=TmApp ({lhs=TmConst ({val=CCreate ()}&c),rhs=TmVar r}&a2),rhs=l}&a1)}&t) ->
    match mapLookup r.ident env with Some (TmConst ({val=CInt {val=i}}&iv)) then
      TmLet {{t with body=TmApp {a1 with lhs=TmApp {a2 with rhs=TmConst iv}}} with inexpr=constantFoldCreate env t.inexpr}
    else TmLet t
  | TmLet ({body=TmVar v}&t) -> match mapLookup v.ident env with Some expr then
      TmLet {t with inexpr=constantFoldCreate (mapInsert v.ident expr env) t.inexpr}
    else TmLet {t with inexpr=constantFoldCreate env t.inexpr}
  | TmLet t -> TmLet {t with inexpr=constantFoldCreate (mapInsert t.ident t.body env) t.inexpr}
  | t -> smap_Expr_Expr (constantFoldCreate env) t

  sem transform: Expr -> Expr
  sem transform =
  | prog ->
    let prog = removeAlias (mapEmpty nameCmp) prog in
    let model = (normalizeTerm prog) in
    let model = constantFoldCreate (mapEmpty nameCmp) model in
    let pbn = createM model in
    let targets = map (lam i. mapLookupOrElse (lam. error "target:Lookup failed") i pbn.m) (distinct nameEq pbn.targets) in
   /- let targetObserves = filter (lam v. match v with RandomVarNode v then (match v.val with Some _ then true else false) else false) targets in
    let targets = filter (lam v. match v with RandomVarNode v then (match v.val with Some _ then false else true) else true) targets in
    let targets = (concat targetObserves targets) in-/
    let targetIds = map getId targets in
    let pbn = transformPBN ({pbn with targets=targetIds},(emptyTAcc ())) in
    let rProg = recreate pbn in
    rProg
  end
  let transform = lam prog. use Transformation in
    transform prog

