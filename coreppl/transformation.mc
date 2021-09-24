include "pgm.mc"

type Env = Map Name Expr

lang MySeqOp = Eq + Sym + TypeAnnot + ANF + PrettyPrint
  syn Expr =
  | TmFoldl { f:Expr
            , acc:Expr
            , lst:Expr
            , ty:Type
            , info:Info
            }
  | TmRange { s:Expr
            , e:Expr
            , by:Expr
            , ty:Type
            , info:Info
            }

  sem infoTm =
  | TmFoldl t -> t.info
  | TmRange t -> t.info

  sem withInfo (info: Info) =
  | TmFoldl t -> TmFoldl { t with info = info}
  | TmRange t -> TmRange { t with info = info}

  sem withType (ty: Type) =
  | TmFoldl t -> TmFoldl {t with ty = ty}
  | TmRange t -> TmRange {t with ty = ty}

  sem smap_Expr_Expr (f: Expr -> a) =
  | TmFoldl t -> TmFoldl {{{ t with f = f t.f} with acc = f t.acc} with lst = f t.lst}
  | TmRange t -> TmRange {{{ t with s = f t.s} with e = f t.e} with by = f t.by}

  sem sfold_Expr_Expr (f: a-> b -> a) (acc: a) =
  | TmFoldl t -> f (f (f acc t.f) t.acc) t.lst
  | TmRange t -> f (f (f acc t.s) t.e) t.by

  sem eqExprH (env: EqEnv) (free: EqEnv) (lhs: Expr) =
  | TmFoldl r ->
    match lhs with TmFoldl l then
      match eqExprH env free l.f r.f with Some free then
        match eqExprH env free l.acc r.acc with Some free then
          eqExprH env free l.lst r.lst
        else None ()
      else None ()
    else None ()
  | TmRange r ->
    match lhs with TmRange l then
      match eqExprH env free l.s r.s with Some free then
        match eqExprH env free l.e r.e with Some free then
          eqExprH env free l.by r.by
        else None ()
      else None ()
    else None ()

  sem symbolizeExpr (env: SymEnv) =
  | TmFoldl t ->
    TmFoldl {{{{ t with f = symbolizeExpr env t.f }
                   with acc = symbolizeExpr env t.acc }
                   with lst = symbolizeExpr env t.lst }
                   with ty = symbolizeType env t.ty }
  | TmRange t ->
    TmRange {{{{ t with s = symbolizeExpr env t.s }
                   with e = symbolizeExpr env t.e }
                   with by = symbolizeExpr env t.by }
                   with ty = symbolizeType env t.ty }

  sem isValue =
  | TmFoldl _ -> false
  | TmRange _ -> false

  sem isAtomic =
  | TmFoldl _ -> false
  | TmRange _ -> false

  sem pprintCode (indent: Int) (env: PPrintEnv) =
  | TmFoldl t ->
    match pprintCode 0 env t.f with (env,f) then
      match pprintCode 0 env t.acc with (env,acc) then
        match pprintCode 0 env t.lst with (env,lst) then
          (env, join ["foldl ", f, acc , lst])
        else never
      else never
    else never
  | TmRange t ->
    match pprintCode 0 env t.s with (env,s) then
      match pprintCode 0 env t.e with (env,e) then
        match pprintCode 0 env t.by with (env,by) then
          (env, join ["range ", s, e , by])
        else never
      else never
    else never
end

let foldl_ = use MySeqOp in
  lam f. lam acc. lam lst. TmFoldl {f=f,acc=acc,lst=lst,ty=tyunknown_, info=NoInfo()}

let range_ = use MySeqOp in
  lam s. lam e. lam by. TmRange {s=s,e=e,by=by,ty=tyunknown_,info=NoInfo()}

lang Transformation = ProbabilisticGraphicalModel + MySeqOp

  sem potentialConjugatePrior =
  | DBeta _ -> true
  | DDirichlet _ -> true
  | DGamma _ -> true
  | DGaussian _ -> true
  | _ -> false

  sem posterior (ctx:{assumeMap:Map Name Expr, observeAssumeMap:Map Name Name, env:Env}) (value: Expr) =
  | DBernoulli l -> match l.p with TmVar v then
                      match mapLookup v.ident ctx.assumeMap with Some (TmAssume ({dist=TmDist ({dist=DBeta p} & t)} & a) ) then
                        let updatedPrior = DBeta {{p with a = (if_ value (addf_ p.a (float_ 1.0)) p.a)} with b = (if_ value p.b (addf_ p.b (float_ 1.0)))} in
                          Some (v.ident, TmAssume {a with dist = TmDist {t with dist = updatedPrior}})
                      else None ()
                    else None ()
  | DBinomial l -> match l.p with TmVar v then
                    match mapLookup v.ident ctx.assumeMap with Some (TmAssume ({dist=TmDist ({dist=DBeta p} & t)} & a)) then
                        let updatedPrior = DBeta {{p with a = (addf_ p.a (int2float_ value))} with b = (addf_ p.b (int2float_ (subi l.n value)))} in
                       Some (v.ident, TmAssume {a with dist = TmDist { t with dist = updatedPrior}})
                      else None ()
                    else None ()
  | DPoisson l -> match l.lambda with TmVar v then
                    match mapLookup v.ident ctx.assumeMap with Some (TmAssume ({dist=TmDist ({dist=DGamma p} & t)} & a)) then
                      let updatedPrior = DGamma {{p with k = addf_ p.k value} with theta = divf_ p.theta (addf_ p.theta (float_ 1.0))} in
                      Some (v.ident, TmAssume {a with dist = TmDist { t with dist = updatedPrior}})
                    else None ()
                  else None ()
  | DCategorical l -> match l.p with TmVar v then
                        match mapLookup v.ident ctx.assumeMap with Some (TmAssume ({dist=TmDist ({dist=DDirichlet p} & t)} & a)) then
                          let updatedPrior = DDirichlet {p with a = mapi_ (ulam_ "i" (ulam_ "e" (if_ (eqi_ (var_ "i") value) (addf_ (var_ "e") (float_ 1.0)) (var_ "e")))) p.a} in
                          Some (v.ident, TmAssume {a with dist = TmDist { t with dist = updatedPrior}})
                        else None ()
                      else None ()
  | DMultinomial l -> match l.p with TmVar v then
                        match mapLookup v.ident ctx.assumeMap with Some (TmAssume ({dist=TmDist ({dist=DDirichlet p} & t)} & a)) then
                          let updatedPrior = DDirichlet {p with a = map_ (ulam_ "v" (mapi_ (ulam_ "i" (ulam_ "e" (if_ (eqi_ (var_ "i") (var_ "v")) (addf_ (var_ "e") (float_ 1.0)) (var_ "e")))) p.a)) value} in
                          Some (v.ident, TmAssume {a with dist = TmDist { t with dist = updatedPrior}})
                        else None ()
                      else None ()
  | DGaussian l -> match l.mu with TmVar v then -- with known variance
                     (match mapLookup v.ident ctx.assumeMap with Some (TmAssume ({dist=TmDist ({dist=DGaussian p} & t)} & a)) then
                       let updatedPrior = DGaussian {{p with mu = (divf_ (float_ 1.0) (addf_ (divf_ (float_ 1.0) (mulf p.sigma p.sigma)) (divf_ (float_ 1.0) (mulf_ l.sigma l.sigma))) ) }
                                                              with sigma = (divf_ (mulf_ (mulf_ l.sigma l.sigma) (mulf_ p.sigma p.sigma)) (addf_ (mulf_ l.sigma l.sigma) (mulf_ p.sigma p.sigma)))} in
                       Some (v.ident, TmAssume {a with dist = TmDist { t with dist = updatedPrior}})
                     else None ())
                   else
                     match l.sigma with TmVar v then -- with known mean
                       match mapLookup v.ident ctx.assumeMap with Some (TmAssume ({dist=TmDist ({dist=DGamma p} & t)} & a)) then
                         let updatedPrior = DGamma {{p with k = addf_ p.k 0.5} with theta = mulf_ (divf_ (float_ 1.0) p.theta) (divf_ (subf_ value l.mean) (float_ 2.0))} in
                         Some (v.ident, TmAssume {a with dist = TmDist { t with dist = updatedPrior}})
                       else None ()
                     else None ()
  | DExponential l -> match l.rate with TmVar v then
                        match mapLookup v.ident ctx.assumeMap with Some (TmAssume ({dist=TmDist ({dist=DGamma p} & t)} & a)) then
                          let updatedPrior = DGamma {{p with k = addf p.k (float_ 1.0)} with theta = addf_ (divf_ (float_ 1.0) p.theta) value} in
                          Some (v.ident, TmAssume {a with dist = TmDist { t with dist = updatedPrior}})
                        else None ()
                      else None ()
  | DGamma l -> match l.theta with TmVar v then
                        match mapLookup v.ident ctx.assumeMap with Some (TmAssume ({dist=TmDist ({dist=DDirichlet p} & t)} & a)) then
                          let updatedPrior = DGamma {{p with k = addf_ p.k l.k} with theta = addf_ (divf_ (float_ 1.0) p.theta) value} in
                          Some (v.ident, TmAssume {a with dist = TmDist { t with dist = updatedPrior}})
                        else None ()
                      else None ()

  sem save (ctx:{skippedLets:Map Name Expr, savedLets:[Expr]}) =
  | TmLet ({body=TmAssume a}&t) -> save {ctx with skippedLets = (mapInsert t.ident a ctx.skippedLets)} t.inexpr
  | TmLet ({body=TmObserve o}&t) -> save {ctx with skippedLets = (mapInsert t.ident o ctx.skippedLets)} t.inexpr
  | TmLet ({body=TmPlate p}&t) -> save {ctx with skippedLets = (mapInsert t.ident p ctx.skippedLets)} t.inexpr
  | TmLet ({body=TmVar v}&t) ->
    match mapLookup v.ident ctx.skippedLets with Some s then
      save {ctx with skippedLets = (mapInsert t.ident s ctx.skippedLets)} t.inexpr
    else save {ctx with savedLets = (cons (TmLet t) ctx.savedLets)} t.inexpr
  | TmLet t -> save {ctx with savedLets = (cons (TmLet t) ctx.savedLets)} t.inexpr
  | t -> sfold_Expr_Expr save ctx t

  sem remove (savedLets:Map Name Expr) =
  | TmLet ({body=TmAssume _}&t) -> TmLet {t with inexpr = remove savedLets t.inexpr}
  | TmLet ({body=TmObserve _}&t) -> TmLet {t with inexpr = remove savedLets t.inexpr}
  | TmLet ({body=TmPlate _}&t) -> TmLet {t with inexpr = remove savedLets t.inexpr}
  | TmLet ({body=TmVar v}&t) ->
    match mapLookup v.ident savedLets with Some s then
      TmLet {t with inexpr = remove savedLets t.inexpr}
    else remove savedLets t.inexpr
  | TmLet t -> remove savedLets t.inexpr
  | t -> smap_Expr_Expr (remove savedLets) t

  sem place (model:Expr) =
  | [TmLet t] ++ as -> place (TmLet {t with inexpr=model}) as
  | [] -> model

  sem collect (ctx:{assumeMap:Map Name Expr, observeAssumeMap:Map Name Name, env:Env}) =
  | TmLet ({body = TmAssume a} & t) -> let assumeMap =
    match a.dist with TmDist d then
      if potentialConjugatePrior d.dist then
        mapInsert t.ident t.body ctx.assumeMap
      else ctx.assumeMap
    else never in
    collect {ctx with assumeMap=assumeMap} t.inexpr
  | TmLet ({body = TmObserve o} & t) ->
    let updatedCtx =
      match o.dist with TmDist d then
        match posterior ctx o.value d.dist with Some (ident, updatedPrior) then
        {{ctx with assumeMap= (mapInsert ident updatedPrior ctx.assumeMap)} with observeAssumeMap = mapInsert t.ident ident ctx.observeAssumeMap}
        else ctx
      else never
    in collect updatedCtx t.inexpr
  | TmLet ({body = TmPlate p} & t) ->
    match p.fun with TmLam l then
      match l.body with TmAssume a then
        let assumeMap =
          match a.dist with TmDist d then
            if potentialConjugatePrior d.dist then
              mapInsert t.ident l.body ctx.assumeMap
            else ctx.assumeMap
          else never
        in
        collect {ctx with assumeMap=assumeMap} t.inexpr
      else
        match l.body with TmObserve o then
          let updatedCtx =
            match o.dist with TmDist ({dist = (DBernoulli {p=TmVar v})&d}|{dist=DCategorical {p=TmVar v}&d}) then
              if nameEq v.ident l.ident then
                match p.lst with TmVar v then
                  match mapLookup v.ident ctx.assumeMap with Some (TmAssume a) then
                    {{ctx with assumeMap=(mapInsert v.ident (TmAssume {a with dist=(updateAssume o.value a.dist)}) ctx.assumeMap)} with observeAssumeMap = mapInsert t.ident v.ident ctx.observeAssumeMap}
                  else ctx
                else ctx--match p.lst with TmSeq s then
              else
                match o.value with TmVar v2 then
                  if nameEq v2.ident l.ident then
                    match mapLookup v.ident ctx.assumeMap with Some (TmAssume a) then
                      {{ctx with assumeMap=(mapInsert v.ident (TmAssume {a with dist=(updateFoldAssume p.lst a.dist)}) ctx.assumeMap)} with observeAssumeMap = mapInsert t.ident v.ident ctx.observeAssumeMap}
                    else ctx
                  else ctx
                else ctx
            else ctx
        in
        collect updatedCtx t.inexpr
      else never -- cannot be sth other than observe or assume
    else never -- plate should be consist of lambda term
  | TmLet t -> collect {ctx with env = (mapInsert t.ident t.body ctx.env)} t.inexpr
  | t -> sfold_Expr_Expr collect ctx t

  sem updateFoldAssume (lst:Expr) =
  | TmDist ({dist = DBeta t} & d)-> TmDist {d with dist = (DBeta
  {{t with a = foldl_ (ulam_ "acc" (ulam_ "x" (if_ (var_ "x") (addf_ (var_ "acc") (float_ 1.0)) (var_ "acc")))) t.a lst}
    with b = foldl_ (ulam_ "acc" (ulam_ "x" (if_ (var_ "x") (var_ "acc") (addf_ (var_ "acc") (float_ 1.0))))) t.b lst})}
 | TmDist ({dist = DDirichlet t} & d)-> TmDist {d with dist = (DDirichlet
  {t with a = (foldl_ (ulam_ "acc" (ulam_ "x"
  (mapi_ (ulam_ "i" (ulam_ "e" (if_ (eqi_ (var_ "i") (var_ "x")) (addf_ (var_ "e") (float_ 1.0)) (var_ "e")))) (var_ "acc")))) t.a lst)})}

  | t -> t

  sem updateAssume (val:Expr) =
  | TmDist ({dist = DBeta t} & d)-> TmDist {d with dist = (DBeta ({{t with a = (if_ val (addf_ t.a (float_ 1.0)) t.a)} with b=(if_ val t.b (addf_ t.b (float_ 1.0)))}))}
  | TmDist ({dist = DDirichlet t} & d)-> TmDist {d with dist = (DDirichlet ({t with a = mapi_ (ulam_ "i" (ulam_ "e" (if_ (eqi_ (var_ "i") val) (addf_ (var_ "e") (float_ 1.0)) (var_ "e")))) t.a }))}
  | t -> t

  sem reconstruct (ctx:{assumeMap:Map Name Expr, observeAssumeMap:Map Name Name, env:Env}) =
  | TmLet ({body=TmObserve o}&t) -> match mapLookup t.ident ctx.observeAssumeMap with Some _ then
                                       reconstruct ctx t.inexpr
                                     else TmLet {t with inexpr = reconstruct ctx t.inexpr}
  | TmLet ({body=TmAssume a}&t) -> match mapLookup t.ident ctx.assumeMap with Some a then
                                     TmLet {{t with body = a} with inexpr = reconstruct ctx t.inexpr}
                                   else TmLet {t with inexpr = reconstruct ctx t.inexpr}
  | TmLet ({body=TmPlate p}&t) -> match p.fun with TmLam l then
                                    match l.body with TmAssume a then
                                      match mapLookup t.ident ctx.assumeMap with Some a then
                                        TmLet {{t with body=(TmPlate {p with fun=(TmLam {l with body=a})})} with inexpr= reconstruct ctx t.inexpr}
                                      else TmLet {t with inexpr = reconstruct ctx t.inexpr}
                                    else match l.body with TmObserve o then
                                      match mapLookup t.ident ctx.observeAssumeMap with Some _ then
                                        reconstruct ctx t.inexpr
                                      else TmLet {t with inexpr = reconstruct ctx t.inexpr}
                                    else never
                                  else never
  | TmLet ({body=TmSeq s}&t) -> TmLet {t with inexpr = reconstruct ctx t.inexpr}
  | t -> smap_Expr_Expr (reconstruct ctx) t

end

/-
- Moves the let expressions that does not have assume or observe terms as body to the beginning of the program.
-/
let move = lam model.
  use Transformation in
  let savedCtx = save {skippedLets=_emptyEnv, savedLets= []} model in
  let removedModel = remove savedCtx.skippedLets model in
  place removedModel savedCtx.savedLets

/-
- Transforms the `moved` model based on the analytical relations between random variables
-/
let transform = lam model.
  use Transformation in
  let movedModel = move model in
  reconstruct (collect {assumeMap=_emptyEnv, observeAssumeMap=_emptyEnv, env=_emptyEnv} movedModel) movedModel


lang TestLang = Transformation + MExprPPL

mexpr

use TestLang in

let simple1example = use MExprPPL in
  bindall_
  [ ulet_ "x" (assume_ (beta_ (float_ 10.0) (float_ 5.0)))
  , ulet_ "obs" true_
  , ulet_ "obs2" (var_ "obs")
  , ulet_ "" (observe_ (var_ "obs2") (bern_ (var_ "x")))
  , var_ "x"
  ]
in

let tsimple1example = use MExprPPL in
  bindall_
  [ ulet_ "obs" true_
  , ulet_ "obs2" (var_ "obs")
  , ulet_ "x" (assume_ (beta_ (if_ (var_ "obs2") (addf_ (float_ 10.0) (float_ 1.0)) (float_ 10.0)) (if_ (var_ "obs2") (float_ 5.0) (addf_ (float_ 5.0) (float_ 1.0)))))
  , var_ "x"
  ]
  in

let simple2example = use MExprPPL in
  bindall_
  [ ulet_ "x" (assume_ (beta_ (float_ 10.0) (float_ 5.0)))
  , ulet_ "obs" (float_ 10.0)
  , ulet_ "" (observe_ (var_ "obs") (exp_ (var_ "x")))
  , var_ "x"
  ]
in
let tsimple2example = use MExprPPL in
  bindall_
  [ ulet_ "obs" (float_ 10.0)
  , ulet_ "x" (assume_ (beta_ (float_ 10.0) (float_ 5.0)))  , ulet_ "" (observe_ (var_ "obs") (exp_ (var_ "x")))
  , var_ "x"
  ]
in

let example1expanded = use MExprPPL in
  bindall_
  [ ulet_ "theta" (assume_ (beta_ (float_ 10.0) (float_ 10.0)))
  , ulet_ "" (observe_ true_ (bern_ (var_ "theta")))
  , var_ "theta"
  ]
in

let texample1expanded = use MExprPPL in
  bindall_
  [ ulet_ "theta" (assume_ (beta_ (if_ true_ (addf_ (float_ 10.0) (float_ 1.0)) (float_ 10.0)) (if_ true_ (float_ 10.0) (addf_ (float_ 10.0) (float_ 1.0)))))
  , var_ "theta"
  ]
in

let example1plate = use MExprPPL in
  bindall_
  [ ulet_ "theta" (assume_ (beta_ (float_ 10.0) (float_ 10.0)))
  , ulet_ "obs" (seq_ [true_, false_, true_])
  , ulet_ "" (plate_ (ulam_ "x" (observe_ (var_ "x") (bern_ (var_ "theta")))) (var_ "obs"))
  , (var_ "theta")
  ] in

let texample1plate = use MExprPPL in
  bindall_
  [ ulet_ "obs" (seq_ [true_, false_, true_])
  , ulet_ "theta" (assume_ (beta_ (foldl_ (ulam_ "acc" (ulam_ "x" (if_ (var_ "x") (addf_ (var_ "acc") (float_ 1.0)) (var_ "acc")))) (float_ 10.0) (var_ "obs")) (foldl_ (ulam_ "acc" (ulam_ "x" (if_ (var_ "x") (var_ "acc") (addf_ (var_ "acc") (float_ 1.0))))) (float_ 10.0) (var_ "obs"))))
  , var_ "theta"
  ] in

/-
let example2expanded = use MExprPPL in
  let r1 = assume (Beta 10.0 10.0) in
  let r2 = assume (Beta 15.0 1.0) in
  let r3 = assume (Beta 21.0 10.0) in
  observe true (Bernoulli r1);
  observe false (Bernoulli r2);
  observe true (Bernoulli r3);
  [r1,r2,r3]
in

let texample2expanded =
  let r1 = assume (Beta (if true then (addf 10.0 1.0) else 10.0) (if true then 10.0 else (addf 10.0 1.0))) in
  let r2 = assume (Beta (if false then (addf 10.0 1.0) else 10.0) (if false then 10.0 else (addf 10.0 1.0))) in
  let r3 = assume (Beta (if true then (addf 21.0 1.0) else 21.0) (if true then 10.0 else (addf 10.0 1.0))) in
  [r1,r2,r3] in
-/
let example2plate = use MExprPPL in
  bindall_
  [ ulet_ "params" (seq_ [(utuple_ [float_ 10.0,float_ 10.0]), (utuple_ [float_ 15.0,float_ 1.0]), (utuple_ [float_ 21.0,float_ 10.0])])
  , ulet_ "rvs" (plate_ (ulam_ "x" (assume_ (beta_ (tupleproj_ 0 (var_ "x")) (tupleproj_ 1 (var_ "x"))))) (var_ "params"))
 , ulet_ "obs" true_
  , ulet_ "" (plate_ (ulam_ "x" (observe_ (var_ "obs") (bern_ (var_ "x")))) (var_ "rvs"))
  , var_ "rvs"
  ] in

let texample2plate = use MExprPPL in
  bindall_
  [  ulet_ "params" (seq_ [(utuple_ [float_ 10.0,float_ 10.0]), (utuple_ [float_ 15.0,float_ 1.0]), (utuple_ [float_ 21.0,float_ 10.0])])
  , ulet_ "obs" true_
  , ulet_ "rvs" (plate_ (ulam_ "x" (assume_ (beta_ (if_ (var_ "obs") (addf_ (tupleproj_ 0 (var_ "x")) (float_ 1.0)) (tupleproj_ 0 (var_ "x")) ) (if_ (var_ "obs") (tupleproj_ 1 (var_ "x"))(addf_ (tupleproj_ 1 (var_ "x")) (float_ 1.0)))))) (var_ "params"))
  , var_ "rvs"
  ] in

let lda = use MExprPPL in
  bindall_
  [ ulet_ "numtopics" (int_ 2) -- the number of topics
  , ulet_ "numdocs" (int_ 3)
  , ulet_ "vocabsize" (int_ 4)
  , ulet_ "vocabulary" (seq_ [int_ 0, int_ 1, int_ 2, int_ 3]) -- word ids
  , ulet_ "docs" (seq_ [int_ 2, int_ 1, int_ 1, int_ 3, int_ 0, int_ 3, int_ 0, int_ 1, int_ 2, int_ 2]) -- word ids for the corpus
  , ulet_ "docids" (seq_ [int_ 0, int_ 0, int_ 0, int_ 1, int_ 1, int_ 1, int_ 1, int_ 2, int_ 2, int_ 2]) -- doc id for each word in the corpus
  , ulet_ "alpha" (appf2_ (var_ "make") (var_ "numtopics") (float_ 0.1)) --topic prior distributions hyperparameter
  , ulet_ "beta" (appf2_ (var_ "make") (var_ "vocabsize") (float_ 0.1)) --word prior distributions hyperparameter
  , ulet_ "phi" (plate_ (ulam_ "x" (assume_ (dirichlet_ (var_ "beta_")))) (range_ (int_ 1) (var_ "numtopics") (int_ 1)))
  , ulet_ "theta" (plate_ (ulam_ "x" (assume_ (dirichlet_ (var_ "alpha_")))) (range_ (int_ 1) (var_ "numdocs") (int_ 1)))
  , ulet_ "z" (plate_ (ulam_ "w" (assume_ (categorical_ (get_ (var_ "theta") (get_ (var_ "docids") (var_ "w")))))) (range_ (int_ 0) (length_ (var_ "docs")) (int_ 1)))
  , ulet_ "" (plate_ (ulam_ "w" (observe_ (get_ (var_ "docs") (var_ "w")) (categorical_ (get_ (var_ "phi") (get_ (var_ "z") (var_ "w")))))) (range_ (int_ 0) (length_ (var_ "docs")) (int_ 1)))
  --, ulet_ "" (plate_ (ulam_ "w" (observe_ (var_ "w") (categorical_ (var_ "phi") 
  , seq_ [var_ "phi", var_ "theta", var_ "z"]
  ]
in

let examplex = use MExprPPL in
  bindall_
  [ ulet_ "params" (seq_ [(utuple_ [float_ 10.0,float_ 10.0]), (utuple_ [float_ 15.0,float_ 1.0]), (utuple_ [float_ 21.0,float_ 10.0])])
  , ulet_ "rvs" (plate_ (ulam_ "x" (assume_ (beta_ (tupleproj_ 0 (var_ "x")) (tupleproj_ 1 (var_ "x"))))) (var_ "params"))
 , ulet_ "obs" true_
  , ulet_ "" (observe_ (var_ "obs") (var_ "rvs"))
  , var_ "rvs"
  ] in

let mexample1 = use MExprPPL in
  bindall_
  [ ulet_ "theta" (assume_ (beta_ (float_ 10.0) (float_ 10.0)))
  , ulet_ "obs" (seq_ [true_, false_, true_])
  , ulet_ "theta_1" (var_ "theta")
  , ulet_ "" (plate_ (ulam_ "x" (observe_ (var_ "x") (bern_ (var_ "theta")))) (var_ "obs"))
  , (var_ "theta")
  ] in

let tmexample1 = use MExprPPL in
  bindall_
  [ ulet_ "obs" (seq_ [true_, false_, true_])
  , ulet_ "theta" (assume_ (beta_ (float_ 10.0) (float_ 10.0)))
  , ulet_ "theta_1" (var_ "theta")
  , ulet_ "" (plate_ (ulam_ "x" (observe_ (var_ "x") (bern_ (var_ "theta")))) (var_ "obs"))
  , (var_ "theta")
  ] in

let dirichlet1example = use MExprPPL in
  bindall_
  [ ulet_ "x" (assume_ (dirichlet_ (seq_ [(float_ 5.0),(float_ 10.0),(float_ 3.0)])))
  , ulet_ "obs" (int_ 0)
  , ulet_ "" (observe_ (var_ "obs") (categorical_ (var_ "x")))
  , var_ "x"
  ]
in

let tdirichlet1example = use MExprPPL in
  bindall_
  [ ulet_ "obs" (int_ 0)
  , ulet_ "x" (assume_ (dirichlet_ (mapi_ (ulam_ "i" (ulam_ "e" (if_ (eqi_ (var_ "i") (var_ "obs")) (addf_ (var_ "e") (float_ 1.0)) (var_ "e")))) (seq_ [(float_ 5.0),(float_ 10.0),(float_ 3.0)]))))
   , var_ "x"
  ]
in

let dirichlet1plate = use MExprPPL in
  bindall_
  [ ulet_ "theta" (assume_ (dirichlet_ (seq_ [(float_ 10.0) ,(float_ 10.0)])))
  , ulet_ "obs" (seq_ [(int_ 0),(int_ 1)])
  , ulet_ "" (plate_ (ulam_ "x" (observe_ (var_ "x") (categorical_ (var_ "theta")))) (var_ "obs"))
  , (var_ "theta")
  ] in

let tdirichlet1plate = use MExprPPL in
  bindall_
  [ ulet_ "obs" (seq_ [(int_ 0),(int_ 1)])
  , ulet_ "theta" (assume_ (dirichlet_ (foldl_ (ulam_ "acc" (ulam_ "x"
  (mapi_ (ulam_ "i" (ulam_ "e" (if_ (eqi_ (var_ "i") (var_ "x")) (addf_ (var_ "e") (float_ 1.0)) (var_ "e")))) (var_ "acc")))) (seq_ [(float_ 10.0), (float_ 10.0)]) (var_ "obs"))))
  , (var_ "theta")
  ] in

let dirichlet2plate = use MExprPPL in
  bindall_
  [ ulet_ "obs" (seq_ [(int_ 0),(int_ 1)])
  , ulet_ "theta" (assume_ (dirichlet_ (foldl_ (ulam_ "acc" (ulam_ "x"
  (mapi_ (ulam_ "i" (ulam_ "e" (if_ (eqi_ (var_ "i") (var_ "x")) (addf_ (var_ "e") (float_ 1.0)) (var_ "e")))) (var_ "acc")))) (seq_ [(float_ 10.0), (float_ 10.0)]) (var_ "obs"))))
  , (var_ "theta")
  ] in

let tdirichlet2plate = use MExprPPL in
  bindall_
  [ ulet_ "obs" (seq_ [(int_ 0),(int_ 1)])
  , ulet_ "theta" (assume_ (dirichlet_ (foldl_ (ulam_ "acc" (ulam_ "x"
  (mapi_ (ulam_ "i" (ulam_ "e" (if_ (eqi_ (var_ "i") (var_ "x")) (addf_ (var_ "e") (float_ 1.0)) (var_ "e")))) (var_ "acc")))) (seq_ [(float_ 10.0), (float_ 10.0)]) (var_ "obs"))))
  , (var_ "theta")
  ] in
utest (transform simple1example) with tsimple1example using eqExpr in
utest (transform simple2example) with tsimple2example using eqExpr in
utest transform example1expanded with texample1expanded using eqExpr in
utest transform example2plate with texample2plate using eqExpr in
utest transform example1plate with texample1plate using eqExpr in
utest move mexample1 with tmexample1 using eqExpr in
utest transform dirichlet1example with tdirichlet1example using eqExpr in
utest transform dirichlet1plate with tdirichlet1plate using eqExpr in
--print (expr2str (transform lda ));
--print (expr2str ( transform tdirichlet1plate));

()
