import Colean.Gen.Iso

/-!
# Generators on `Expr`: the lifting to relations

*Spec.* Input: the context, `T.F` and (for `rel_ofC`) the isomorphism. Output, for `codatatype`:

* `T.F.Rel R : T.F params X idx → T.F params Y idx → Prop`, the inductive lifting of a relation:
  the same constructor, the same data, related recursive arguments (`R` at their index, pointwise
  under a telescope, `Occ.Rel` for a nested argument);
* `T.F.rel_fmap`: the images of one value under pointwise related functions are related;
* `T.Colean.rel_ofC`: the lifting through the isomorphism is the signature's (`Signature.Obj.Rel`);
* one step of the lifting, `simp` lemmas: `T.F.rel_cᵢ_cᵢ : T.F.Rel R (F.cᵢ ys) (F.cᵢ ys') ↔ …`,
  the data equal and the premises of `T.F.Rel.cᵢ`, and `T.F.rel_cᵢ_cⱼ : … ↔ False` where the
  results of two constructors meet (`genRelSteps`, also per type of a block, `Gen/Surface.lean`);
* `T.F.Rel.mono` (a larger relation relates more) and `T.F.rel_refl` (a layer is related to itself
  by a reflexive relation), for `T.coinduct` (`Gen/Surface.lean`).

`T.F.Rel` belongs to the surface (step 4), but the model's `rel_ofC` and the contract's `bisim`
are stated with it, so it is generated before them (a boundary violation recorded in
`architecture.md`), and its lemmas with it. The lemmas are proved by tactic scripts: `cases`,
then `constructor` and the hypothesis for `rel_fmap`; for `rel_ofC`, the layers written as
`toC a`, `toC a'` (`toC_ofC`), `cases` on the hypothesis, which is then at variables, the layers
of the nested arguments rewritten with the hypotheses on them, then the witnesses, and the
positions by cases in general position (`casesPos`); for the one-step lemmas, cases on the
hypothesis in general position (`casesRel`) and the hypotheses one way, the equations substituted
and the constructor the other; `Rel.mono` by cases and the constructor at the premises mapped;
`rel_refl` is `rel_fmap` at the identity rewritten by `fmap_id`. The names of `F` and `F.Rel`,
the one-step lemmas among them (`T.F.rel_a_b` for a constructor `rel_a_b`), are refused as
constructor names before anything is declared (`checkCtorNames`, `Gen/Front.lean`); a one-step
lemma whose name another one takes (`rel_a_b_c`, at `a` and `b_c` and at `a_b` and `c`) is not
generated.
-/

open Lean Meta Elab Term

namespace Codata.Gen

namespace Ctx

variable (ctx : Ctx)

/-- `X → Y → Prop`, or `∀ j₁ j₂, X j₁ j₂ → Y j₁ j₂ → Prop`. -/
def famRel (X Y : Expr) : TermElabM Expr :=
  ctx.withJs fun js => do
    mkForallFVars js (← mkArrow (mkAppN X js) (← mkArrow (mkAppN Y js) (mkSort .zero)))

/-- `@T.F.Rel params X Y R idx a b`, at the universes `wX`, `wY` of `X`, `Y`. -/
def relAt (wX wY : Level) (X Y R : Expr) (idx : Array Expr) (a b : Expr) : MetaM Expr := do
  ctx.genAt ctx.Rel [wX, wY] (#[X, Y, R] ++ idx ++ #[a, b])

/-- The premise of `T.F.Rel.c` at the recursive argument `a` of `c`, for its value `y` at `X` and
`y'` at `Y`: `R idx y y'`, pointwise under a telescope, `Occ.Rel` (`IOcc.Rel`, at the relation on
the packed index) for a nested argument; `σ` the substitution of `withArgsAt`. -/
def relPremise (a : ArgInfo) (wX wY : Level) (R : Expr) (σ : Expr → Expr) (y y' : Expr) :
    TermElabM Expr := do
  match a.kind with
  | .plain idx => pure (mkAppN R (idx.map σ ++ #[y, y']))
  | .fn n => openFn n (← inferType y) fun zs idx => do
    mkForallFVars zs (mkAppN R (idx ++ #[mkAppN y zs, mkAppN y' zs]))
  | .nest n =>
    let oX := ctx.nestAt n wX σ
    let oY := ctx.nestAt n wY σ
    if ctx.idxed then
      let RP ← if ctx.k ≤ 1 then pure R else
        withLocalDeclD `p ctx.J fun p => do mkLambdaFVars #[p] (mkAppN R (← ctx.projs p))
      mkAppM ``Codata.IOcc.Rel #[oX, oY, RP, y, y']
    else mkAppM ``Codata.Occ.Rel #[oX, oY, R, y, y']
  | .data => throwError "internal error: a premise at a data argument"

/-- The constructor of `T.F.Rel` for `c`, at the local variables `X`, `Y`, `R` and `Rv` for
`T.F.Rel` itself. -/
def relCtorType (c : Ctor) (wX wY : Level) (X Y R Rv : Expr) : TermElabM Expr := do
  ctx.withArgsAt c (mkAppN X) wX fun ys σ => do
  -- The primed copies of the recursive arguments, at `Y`.
  let recs := (c.args.zip ys).filter (!·.1.kind.isData)
  let rec primes (i : Nat) (acc : Array Expr) (k : Array Expr → TermElabM Expr) :
      TermElabM Expr := do
    if h : i < recs.size then
      let (a, _) := recs[i]
      withLocalDeclD (a.name.appendAfter "'") (ctx.replaceOcc (σ a.type) (mkAppN Y) wY)
        fun y' => primes (i + 1) (acc.push y') k
    else k acc
  primes 0 #[] fun ys' => do
  let hyps ← (recs.zip ys').mapM fun ((a, y), y') => ctx.relPremise a wX wY R σ y y'
  -- The fields: each argument, followed by its primed copy if recursive; then the hypotheses.
  let mut fields := #[]
  let mut ysY := #[]
  let mut j := 0
  for a in c.args, y in ys do
    fields := fields.push y
    if a.kind.isData then ysY := ysY.push y
    else
      fields := fields.push ys'[j]!
      ysY := ysY.push ys'[j]!
      j := j + 1
  let lhs := mkAppN (← ctx.constWith (ctx.fCtor c) [wX]) (ctx.params ++ #[X] ++ ys)
  let rhs := mkAppN (← ctx.constWith (ctx.fCtor c) [wY]) (ctx.params ++ #[Y] ++ ysY)
  let body := mkAppN Rv (ctx.params ++ #[X, Y, R] ++ c.idx.map σ ++ #[lhs, rhs])
  let rec withHyps (i : Nat) (acc : Array Expr) : TermElabM Expr := do
    if h : i < hyps.size then
      withLocalDeclD (← mkFreshUserName `h) hyps[i] fun hv => withHyps (i + 1) (acc.push hv)
    else
      withBinderInfo (ctx.params ++ #[X, Y, R]) .implicit do
        mkForallFVars (ctx.params ++ #[X, Y, R] ++ fields ++ acc) body
  withHyps 0 #[]

/-- `T.F.Rel`. -/
def genRelType : TermElabM Unit := do
  let fresh := ctx.freshLevels 2
  let (wX, wY) := (ctx.holeLevel (.param fresh[0]!), ctx.holeLevel (.param fresh[1]!))
  withLocalDecl `X .implicit (← ctx.famType wX) fun X => do
  withLocalDecl `Y .implicit (← ctx.famType wY) fun Y => do
  withLocalDeclD `R (← ctx.famRel X Y) fun R => do
  let ty ← withLocalDeclD `a (← ctx.fAt wX X ctx.idx) fun a => do
    withLocalDeclD `b (← ctx.fAt wY Y ctx.idx) fun b => do
    withBinderInfo (ctx.params ++ ctx.idx) .implicit do
      mkForallFVars (ctx.params ++ #[X, Y, R] ++ ctx.idx ++ #[a, b]) (mkSort .zero)
  withLocalDeclD `Rel ty fun Rv => do
  let ctorTys ← ctx.ctors.mapM (ctx.relCtorType · wX wY X Y R Rv)
  let us ← ctx.levelParamsOf fresh (ctorTys.push ty)
  let Rc := Lean.mkConst ctx.Rel (us.map mkLevelParam)
  addInductive us (ctx.params.size + 3) [{
    name := ctx.Rel, type := ty
    ctors := (ctx.ctors.zip ctorTys).toList.map fun (c, t) =>
      { name := ctx.relCtor c, type := t.replaceFVar Rv Rc } }] ctx.ref

/-- `T.F.rel_fmap`. -/
def genRelMap : TermElabM Unit := do
  let fresh := ctx.freshLevels 3
  let [wX, wY, wZ] := fresh.map fun u => ctx.holeLevel (.param u) | unreachable!
  withLocalDecl `X .implicit (← ctx.famType wX) fun X => do
  withLocalDecl `Y .implicit (← ctx.famType wY) fun Y => do
  withLocalDecl `Z .implicit (← ctx.famType wZ) fun Z => do
  withLocalDeclD `R (← ctx.famRel Y Z) fun R => do
  withLocalDeclD `f (← ctx.famFn X Y) fun f => do
  withLocalDeclD `g (← ctx.famFn X Z) fun g => do
  withLocalDeclD `a (← ctx.fAt wX X ctx.idx) fun a => do
  let hTy ← ctx.withJs fun js => withLocalDeclD `x (mkAppN X js) fun x => do
    mkForallFVars (js.push x) (mkAppN R (js ++ #[mkAppN f (js.push x), mkAppN g (js.push x)]))
  withLocalDeclD `h hTy fun h => do
  let xs := ctx.params ++ #[X, Y, Z, R, f, g] ++ ctx.idx ++ #[a, h]
  let type ← withBinderInfo (ctx.params ++ ctx.idx) .implicit do
    mkForallFVars xs (← ctx.relAt wY wZ Y Z R ctx.idx (← ctx.mapAt wX wY X Y f ctx.idx a)
      (← ctx.mapAt wX wZ X Z g ctx.idx a))
  let map := mkCIdent ctx.Fmap
  let value ← prove type fun goal => do
    let (_, goal) ← goal.introN (xs.size - 2)
    runTac goal (← `(tactic| (
      intro a h
      cases a
      all_goals simp only [$map:ident]
      all_goals constructor
      all_goals intros
      all_goals first
        | apply h
        | (apply Codata.Occ.rel_map; intro; apply h)
        | (apply Codata.IOcc.rel_map; intro; intro; apply h))))
  addThm ctx.Frel_map (← ctx.levelParamsOf fresh #[type]) type value ctx.ref

/-- `T.Colean.rel_ofC`. -/
def genRelOfC : TermElabM Unit := do
  let fresh := ctx.freshLevels 2
  let wX := ctx.holeLevel (.param fresh[0]!)
  let wY := ctx.holeLevel (.param fresh[1]!)
  ctx.withFamX `X wX fun X => do
  ctx.withFamX `Y wY fun Y => do
  let ixp ← ctx.ixp
  let RTy ← withLocalDeclD `q ixp fun q => do
    mkForallFVars #[q] (← mkArrow (mkApp X q) (← mkArrow (mkApp Y q) (mkSort .zero)))
  withLocalDeclD `R RTy fun R => do
  let pI ← ctx.packI
  withLocalDeclD `z (← ctx.objAt wX X pI) fun z => do
  withLocalDeclD `z' (← ctx.objAt wY Y pI) fun z' => do
  let (X', Y') := (← ctx.curryFam X, ← ctx.curryFam Y)
  let hTy ← ctx.relAt wX wY X' Y' (← ctx.curryN R 0) ctx.idx (← ctx.ofCAt wX X ctx.idx z)
    (← ctx.ofCAt wY Y ctx.idx z')
  withLocalDeclD `h hTy fun h => do
  let objRel := mkAppN (← ctx.sigConst ``Codata.Signature.Obj.Rel [wX, wY])
    #[← ctx.sigE, X, Y, R, pI, z, z']
  let xs := ctx.params ++ #[X, Y, R] ++ ctx.idx ++ #[z, z', h]
  let type ← withBinderInfo (ctx.params ++ ctx.idx) .implicit do mkForallFVars xs objRel
  -- The layers are written as `toC a`, `toC a'`, so that the hypothesis is on variables
  -- `a`, `a'` and at the index variables: `cases` on it needs no unification.
  let ofC := mkCIdent ctx.ofC
  let toC_ofC := mkCIdent ctx.toC_ofC
  let start ← `(tactic| (
    intro z z' h
    rw [← $toC_ofC:ident z, ← $toC_ofC:ident z']
    generalize $ofC:ident z = a at h ⊢
    generalize $ofC:ident z' = a' at h ⊢
    clear z z'))
  let value ← prove type fun g => do
    let (_, g) ← g.introN (xs.size - 3)
    let [g] ← Tactic.run g (Tactic.evalTactic start)
      | throwError "internal error: expected one goal"
    let h ← g.withContext do
      let some h ← (← getLCtx).findDeclRevM? fun d => do
          let ty ← instantiateMVars d.type
          return if ty.getAppFn.isConstOf ctx.Rel then some d.fvarId else none
        | throwError "internal error: no hypothesis of `{ctx.Rel}`"
      pure h
    for sg in ← g.cases h do
      let some c := ctx.ctors.find? (ctx.relCtor · == sg.ctorName)
        | throwError "internal error: unexpected case {sg.ctorName}"
      -- The premises of `T.F.Rel.c`, its last fields, named `h_x` by the fields of the case: the
      -- substitution of the index variables reorders the hypotheses that depend on them, so their
      -- positions in the context do not tell which is which.
      let recs := c.recArgs
      let hps := sg.fields.extract (sg.fields.size - recs.size) sg.fields.size
      let g ← (recs.zip hps).foldlM (init := sg.mvarId) fun g (a, hp) => do
        let .fvar hp := hp | throwError "internal error: a premise substituted"
        g.rename hp (Name.mkSimple s!"h_{a.name}")
      -- `toC (F.c …)` unfolded to its layer, where a nested argument's layer `toC o x` occurs.
      let g ← g.withContext do
        let tgt ← instantiateMVars (← g.getType)
        let args := tgt.getAppArgs
        g.replaceTargetDefEq (mkAppN tgt.getAppFn
          (args.extract 0 (args.size - 2) ++ #[← whnf args[args.size - 2]!, ← whnf args.back!]))
      -- The hypothesis on a nested pair gives its two layers, with one shape, and the relation
      -- on their contents.
      let mut steps : Array (TSyntax `tactic) := #[]
      for a in recs do
        if a.kind.isNest then
          let hId := mkIdent (Name.mkSimple s!"h_{a.name}")
          let e := mkIdent (Name.mkSimple s!"e_{a.name}")
          let e' := mkIdent (Name.mkSimple s!"e'_{a.name}")
          steps := steps.push
            (← `(tactic| obtain ⟨_, _, _, $e:ident, $e':ident, $hId:ident⟩ := $hId))
          steps := steps.push (← `(tactic| rw [$e:ident, $e':ident]))
      steps := steps.push (← `(tactic| refine ⟨_, _, _, rfl, rfl, fun b => ?_⟩))
      let [g] ← Tactic.run g (Tactic.evalTactic (← `(tactic| ($[$steps:tactic]*))))
        | throwError "internal error: expected one goal"
      -- The positions, by cases in general position.
      let b ← g.withContext do return (← getLCtx).lastDecl.get!.fvarId
      for sg in ← casesPos g b do runTac sg.mvarId (← `(tactic| solve_by_elim))
  addThm ctx.rel_ofC (← ctx.levelParamsOf fresh #[type]) type value ctx.ref

end Ctx

/-! ### One step of the lifting

For two constructors `c`, `c'` of one type, the lifting at their layers, as an equivalence that
`simp` uses: `T.F.rel_c_c : T.F.Rel R (F.c ys) (F.c ys') ↔ ys = ys' ∧ prems`, the data equal (one
equation per argument, `HEq` where the types of the two sides differ, as `T.cᵢ_inj`, the proofs
left out) and the premises of `T.F.Rel.c` at the recursive arguments (`True` without any), and
`T.F.rel_c_c' : … ↔ False` for two constructors, where their results meet (`withRelMeet`, either
way round, as `T.cᵢ_ne_cⱼ`). The two sides share the arguments that occur in the result index or
in the type of a recursive argument (and those in the type of one of these), so that both are at
one index and the premises are well typed: for an argument whose type mentions a data argument
(`k : X → T` with `X` an argument), the lemma applies where the two sides have the same data
there.

The same lemmas per type of a block, with a relation per type (`Gen/Surface.lean`): `RelStep`
describes the lifting. The proof is by cases on the hypothesis in general position (`casesRel`),
then the hypotheses, and the constructor of `T.F.Rel` after the equations are substituted. -/

/-- A lifting whose one-step lemmas are to be generated: that of a single type, `T.F.Rel R`, or
that of a type of a block, `Tₘ.F.Rel R₁ … Rₖ`. -/
structure RelStep where
  /-- The variables of the lemmas before the arguments: `X Y R`, or `X₁ … Xₖ Y₁ … Yₖ R₁ … Rₖ`. -/
  vars : Array Expr
  /-- The occurrences of the types in the arguments of the two sides (`withArgsAtU`). -/
  repX : Nat → Array Expr → Expr
  repY : Nat → Array Expr → Expr
  wX : Level
  wY : Level
  /-- The families of the two layers: `X`, `Y`, or `Blk.Colean.St X₁ … Xₖ`, `Blk.Colean.St Y₁ … Yₖ`.
  -/
  famX : Expr
  famY : Expr
  /-- The lifting at the index arguments of a constructor's result and at two layers. -/
  rel : Array Expr → Expr → Expr → TermElabM Expr
  /-- The premise at a recursive argument (`Ctx.relPremise`), under the left substitution. -/
  premise : ArgInfo → (Expr → Expr) → Expr → Expr → TermElabM Expr
  /-- The index arguments of `rel` at a constructor, under its substitution. -/
  idxOf : Ctor → (Expr → Expr) → Array Expr
  /-- The lemma for two constructors. -/
  name : Ctor → Ctor → Name
  /-- The constructors of the type. -/
  ctors : Array Ctor
  /-- The added universes, of the two families. -/
  fresh : List Name
  ref : Syntax
  /-- Applied to the types of the arguments (`withArgsAtU`). -/
  post : Expr → Expr := id

/-- Which arguments `ys` of a constructor the two sides of a step of the lifting share: those
that occur in the index arguments `idx` or in the types `recTys` of the recursive arguments, or
in the type of a local variable occurring there. -/
def relShared (ys idx recTys : Array Expr) : MetaM (Array Bool) := do
  let lctx ← getLCtx
  return ys.map fun y => (idx ++ recTys).any (occursOrInType lctx y)

/-- `MVarId.cases` on `h : T.F.Rel R a b` (or a lifting per type, unfolded first) whose layers `a`,
`b` are constructor applications, in general position, as `casesPos` does for a position: `h` is
eliminated at variables, and in each case the equation of the left layers is solved first, by the
heterogeneous `noConfusion` of the functor with the equations of the indices, which closes the
cases of other constructors and gives the equations of the arguments. Once these are substituted,
the equation of the right layers is one of a single type, solved as `cases` does, and those of the
indices hold by definition. So the result indices need not be patterns. The remaining goals. -/
def casesRel (g : MVarId) (h : FVarId) : MetaM (Array MVarId) := g.withContext do
  let hTy ← whnfR (← h.getType)
  let .const Rel _ := hTy.getAppFn | throwError "internal error: not a lifting{indentExpr hTy}"
  let g ← g.replaceLocalDeclDefEq h hTy
  let gi ← generalizeIndices g h
  let sgs ← gi.mvarId.induction gi.fvarId (mkCasesOnName Rel)
  sgs.filterMapM fun sg => sg.mvarId.withContext do
    -- The equations of the indices and of the left layers; those of the right layers and of
    -- `h` stay in the goal.
    let (hs, g) ← sg.mvarId.introNP (gi.numEqs - 2)
    g.withContext do
    let hs := hs.map mkFVar
    let P ← g.getType
    let hsTy ← inferType hs.back!
    let (s₀, s') ← match hsTy.heq?, hsTy.eq? with
      | some (_, s₀, _, s'), _ => pure (s₀, s')
      | _, some (_, s₀, s') => pure (s₀, s')
      | _, _ => throwError "internal error: expected an equation of layers, got{indentExpr hsTy}"
    let sTy ← whnf (← inferType s₀)
    let .const S us := sTy.getAppFn
      | throwError "internal error: expected a layer, got{indentExpr sTy}"
    let info ← getConstInfoInduct S
    let mut nc := mkAppN (.const (S ++ `noConfusion) ((← getLevel P) :: us))
      (#[P] ++ sTy.getAppArgs ++ #[s₀] ++ (← whnf (← inferType s')).getAppArgs ++ #[s'])
    for _ in [0:info.numParams + info.numIndices + 1] do
      nc := mkApp nc (← eqProof (← whnfForall (← inferType nc)).bindingDomain! hs)
    let some (c₀, _) ← constructorApp'? s₀ | throwError "internal error: expected a constructor"
    let some (c', _) ← constructorApp'? s' | throwError "internal error: expected a constructor"
    if c₀.name != c'.name then
      g.assign nc
      return none
    let .forallE _ K _ _ ← whnf (← inferType nc)
      | throwError "internal error: unexpected `noConfusion`{indentExpr nc}"
    let k ← mkFreshExprSyntheticOpaqueMVar K (← g.getTag)
    g.assign (mkApp nc k)
    let g ← k.mvarId!.tryClearMany (hs.map (·.fvarId!))
    -- The equations of the arguments, then those of the right layers and of `h`.
    let nEqs := K.getNumHeadForalls - P.getNumHeadForalls + 2
    let some (g, _) ← Cases.unifyEqs? nEqs g sg.subst | return none
    return some g

namespace Ctx

variable (ctx : Ctx)

/-- Run `k` on the arguments of `c` as those of the right side of a step of the lifting: the
arguments marked `shared` are the left side's `ys`, the others primed copies (an instance's
implicit), the occurrences replaced by `rep` at `lvl`. `k` receives them and the substitution of
the analysis' arguments. -/
def withRightArgs (c : Ctor) (ys : Array Expr) (shared : Array Bool)
    (rep : Nat → Array Expr → Expr) (lvl : Level) (post : Expr → Expr)
    (k : Array Expr → (Expr → Expr) → TermElabM α) : TermElabM α := do
  let rec go (i : Nat) (acc : Array Expr) : TermElabM α := do
    if h : i < c.args.size then
      if shared[i]! then go (i + 1) (acc.push ys[i]!) else
      let a := c.args[i]
      let ty := post (ctx.replaceOccU (a.type.replaceFVars (c.fvars.extract 0 i) acc) rep lvl)
      let bi := if a.bi.isInstImplicit then .implicit else a.bi
      withLocalDecl (a.name.appendAfter "'") bi ty fun y => go (i + 1) (acc.push y)
    else k acc fun e => e.replaceFVars c.fvars acc
  go 0 #[]

/-- Run `k` where the results of the constructors `c` and `c'` meet, as `withMeet` does for the
types' constructors: on the arguments of `c` at the left family as variables, and those of `c'` at
the right one at which their result indices unify by reducible unification, the arguments left
unassigned new local variables; with `swap`, the arguments of `c'` are the variables, and those of
`c` are where the indices unify. `k` receives the arguments of `c`, those of `c'`, the variables
of the lemma, in order, and the index arguments at which the two meet. Nothing is run when the
indices do not unify. -/
def withRelMeet (s : RelStep) (c c' : Ctor) (swap : Bool)
    (k : Array Expr → Array Expr → Array Expr → Array Expr → TermElabM α) :
    TermElabM (Option α) := do
  -- The side with variables, and the side with metavariables.
  let (cV, repV, wV, cM, repM, wM) :=
    if swap then (c', s.repY, s.wY, c, s.repX, s.wX) else (c, s.repX, s.wX, c', s.repY, s.wY)
  let rename (n : Name) : Name := if swap then n else n.appendAfter "'"
  let renameV (n : Name) : Name := if swap then n.appendAfter "'" else n
  let tel ← ctx.withArgsAtU cM repM wM (rename := rename) (post := s.post)
    fun zs σ => do mkForallFVars zs (mkAppN (Lean.mkConst ``Prod.mk) (s.idxOf cM σ))
  let names := tel.getForallBinderNames.toArray
  ctx.withArgsAtU cV repV wV (rename := renameV) (post := s.post) fun ys σ => do
  let (ms, bis, body) ← forallMetaTelescope tel
  let idxB := body.getAppArgs
  let idxA := s.idxOf cV σ
  unless idxA.size == idxB.size do return none
  let meet ← withReducible <| (idxA.zip idxB).allM fun (i, j) => isDefEq i j
  unless meet do return none
  let rec go (i : Nat) (sub : Array (Expr × Expr)) (args new : Array Expr) :
      TermElabM (Option α) := do
    let rep (e : Expr) : MetaM (Option Expr) := do
      let e := (← instantiateMVars e).replace fun x => (sub.find? (·.1 == x)).map (·.2)
      return if e.hasExprMVar then none else some e
    if h : i < ms.size then
      let m := ms[i]
      if ← m.mvarId!.isAssigned then
        let some v ← rep m | return none
        go (i + 1) sub (args.push v) new
      else
        let some ty ← rep (← inferType m) | return none
        withLocalDecl names[i]! bis[i]! ty fun x =>
          go (i + 1) (sub.push (m, x)) (args.push x) (new.push x)
    else if swap then some <$> k args ys (ys ++ new) idxA
    else some <$> k ys args (ys ++ new) idxA
  go 0 #[] #[] #[]

/-- The one-step lemmas of the lifting `s` (see the section header), `simp` lemmas. A lemma whose
name is taken (a constructor of that name) is not generated. -/
def genRelSteps (s : RelStep) : TermElabM Unit := do
  let free (n : Name) : MetaM Bool := return !(← getEnv).contains n
  let fApp (c : Ctor) (w : Level) (fam : Expr) (ys : Array Expr) : MetaM Expr :=
    ctx.genAt (ctx.fCtor c) [w] (#[fam] ++ ys)
  let thm (n : Name) (xs : Array Expr) (stmt : Expr) (tac : MVarId → TermElabM Unit) :
      TermElabM Unit := do
    let xs := ctx.params ++ s.vars ++ xs
    let type ← withBinderInfo (ctx.params ++ s.vars) .implicit do mkForallFVars xs stmt
    let value ← prove type fun g => do
      let (_, g) ← g.introN xs.size
      tac g
    addThm n (← ctx.levelParamsOf s.fresh #[type]) type value s.ref
    addSimp n
  -- `rel_c_c`
  for c in s.ctors do
    let n := s.name c c
    unless ← free n do continue
    ctx.withArgsAtU c s.repX s.wX (post := s.post) fun ys σ => do
    let recTys ← (c.args.zip ys).filterMapM fun (a, y) => do
      if a.kind.isData then return none else return some (← inferType y)
    let shared ← relShared ys (s.idxOf c σ) recTys
    ctx.withRightArgs c ys shared s.repY s.wY s.post fun ys' _ => do
    let new := (ys'.zip shared).filterMap fun (y, sh) => if sh then none else some y
    -- The equations of the data, then the premises; with the terms closing each in the proof.
    let mut conj : Array Expr := #[]
    let mut items : Array (TSyntax `term) := #[]
    for a in c.args, y in ys, y' in ys' do
      if !a.kind.isData then continue
      if y == y' || (← isProof y) then continue
      let e ← mkEqHEq y y'
      conj := conj.push e
      items := items.push (← if e.isHEq then `(HEq.rfl) else `(rfl))
    for a in c.args, y in ys, y' in ys' do
      if a.kind.isData then continue
      conj := conj.push (← s.premise a σ y y')
      items := items.push (← `(‹_›))
    let rhs := if conj.isEmpty then Lean.mkConst ``True
      else conj.pop.foldr (init := conj.back!) mkAnd
    let lhs ← s.rel (s.idxOf c σ) (← fApp c s.wX s.famX ys) (← fApp c s.wY s.famY ys')
    let close ← match items with
      | #[] => `(tactic| exact trivial)
      | #[i] => `(tactic| exact $i)
      | is => `(tactic| exact ⟨$is,*⟩)
    -- The patterns of the conjunction: `rfl` for an equation, `⟨⟩` for `HEq`, the premises.
    let pats ← conj.mapM fun e => do
      if e.isHEq then `(Lean.Parser.Tactic.rcasesPatLo| ⟨⟩)
      else if e.isEq then `(Lean.Parser.Tactic.rcasesPatLo| $(mkIdent `rfl):ident)
      else `(Lean.Parser.Tactic.rcasesPatLo| _)
    let relC := mkCIdent (ctx.relCtor c)
    let intro ← match pats with
      | #[] => `(tactic| intro _)
      | #[p] => `(tactic| (intro h; rcases h with $p:rcasesPatLo))
      | ps => `(tactic| (intro h; rcases h with ⟨$ps,*⟩))
    thm n (ys ++ new) (mkIff lhs rhs) fun g => do
      let [mp, mpr] ← g.apply (Lean.mkConst ``Iff.intro) | throwError "internal error: not an iff"
      let (h, mp) ← mp.intro1
      for g in ← casesRel mp h do runTac g close
      runTac mpr (← `(tactic| ($intro:tactic; apply $relC <;> assumption)))
  -- `rel_c_c'`
  for c in s.ctors do
    for c' in s.ctors do
      if c.name == c'.name then continue
      let n := s.name c c'
      unless ← free n do continue
      let disj (swap : Bool) := ctx.withRelMeet s c c' swap fun ys ys' xs idx => do
        let lhs ← s.rel idx (← fApp c s.wX s.famX ys) (← fApp c' s.wY s.famY ys')
        thm n xs (mkIff lhs (Lean.mkConst ``False)) fun g => do
          let [mp, mpr] ← g.apply (Lean.mkConst ``Iff.intro)
            | throwError "internal error: not an iff"
          let (h, mp) ← mp.intro1
          unless (← casesRel mp h).isEmpty do
            throwError "internal error: a step of the lifting at distinct constructors"
          let (h, mpr) ← mpr.intro1
          mpr.withContext do mpr.assign (← mkFalseElim (← mpr.getType) (mkFVar h))
      if (← disj false).isNone then discard <| disj true

/-- `T.F.Rel.mono`. -/
def relMonoN : Name := .str ctx.Rel "mono"

/-- `T.F.rel_refl`. -/
def relReflN : Name := ctx.nF "rel_refl"

/-- `T.F.Rel.mono`: a larger relation relates more, by cases on the lifting and its constructor,
the premises mapped by the hypothesis (pointwise under a telescope, by `Occ.Rel.mono` or
`IOcc.Rel.mono` for a nested argument). -/
def genRelMono : TermElabM Unit := do
  if (← getEnv).contains ctx.relMonoN then return
  let fresh := ctx.freshLevels 2
  let (wX, wY) := (ctx.holeLevel (.param fresh[0]!), ctx.holeLevel (.param fresh[1]!))
  withLocalDecl `X .implicit (← ctx.famType wX) fun X => do
  withLocalDecl `Y .implicit (← ctx.famType wY) fun Y => do
  withLocalDecl `R .implicit (← ctx.famRel X Y) fun R => do
  withLocalDecl `S .implicit (← ctx.famRel X Y) fun S => do
  let hTy ← ctx.withJs fun js => withLocalDeclD `x (mkAppN X js) fun x => do
    withLocalDeclD `y (mkAppN Y js) fun y => do
    mkForallFVars (js ++ #[x, y])
      (← mkArrow (mkAppN R (js ++ #[x, y])) (mkAppN S (js ++ #[x, y])))
  withLocalDeclD `h hTy fun h => do
  withLocalDecl `a .implicit (← ctx.fAt wX X ctx.idx) fun a => do
  withLocalDecl `b .implicit (← ctx.fAt wY Y ctx.idx) fun b => do
  withLocalDeclD `hab (← ctx.relAt wX wY X Y R ctx.idx a b) fun hab => do
  let xs := ctx.params ++ #[X, Y, R, S, h] ++ ctx.idx ++ #[a, b, hab]
  let type ← withBinderInfo (ctx.params ++ ctx.idx) .implicit do
    mkForallFVars xs (← ctx.relAt wX wY X Y S ctx.idx a b)
  let value ← prove type fun g => do
    let (fs, g) ← g.introN xs.size
    let h := mkFVar fs[ctx.params.size + 4]!
    -- On the packed index for a nested argument with several indices.
    let hP ← if ctx.k ≤ 1 then pure h else
      withLocalDeclD `p ctx.J fun p => do mkLambdaFVars #[p] (mkAppN h (← ctx.projs p))
    for sg in ← g.cases fs.back! do
      sg.mvarId.withContext do
      let some c := ctx.ctors.find? (ctx.relCtor · == sg.ctorName)
        | throwError "internal error: unexpected case {sg.ctorName}"
      let tgt ← instantiateMVars (← sg.mvarId.getType)
      let .const _ us := tgt.getAppFn | throwError "internal error: not a lifting"
      -- The arguments of the constructor from the two layers, the premises the last fields.
      let np := ctx.params.size + 1
      let (la, lb) := (tgt.appFn!.appArg!.getAppArgs, tgt.appArg!.getAppArgs)
      let args := (c.args.zip ((la.extract np la.size).zip (lb.extract np lb.size))).flatMap
        fun (a, x, y) => if a.kind.isData then #[x] else #[x, y]
      let nr := c.recArgs.size
      let hyps ← (c.recArgs.zip (sg.fields.extract (sg.fields.size - nr) sg.fields.size)).mapM
          fun (a, hp) => do
        let ty ← whnfR (← inferType hp)
        match a.kind with
        | .plain _ => return mkAppN h (ty.getAppArgs.push hp)
        | .fn n => forallBoundedTelescope ty n fun zs body => do
          mkLambdaFVars zs (mkAppN h (body.getAppArgs.push (mkAppN hp zs)))
        | .nest _ =>
          let args := ty.getAppArgs
          if ctx.idxed then mkAppM ``Codata.IOcc.Rel.mono #[args[5]!, args[7]!, hP, hp]
          else mkAppM ``Codata.Occ.Rel.mono #[args[3]!, args[5]!, h, hp]
        | .data => throwError "internal error: a premise at a data argument"
      sg.mvarId.assign (mkAppN (.const (ctx.relCtor c) us)
        (tgt.getAppArgs.extract 0 (ctx.params.size + 3) ++ args ++ hyps))
  addThm ctx.relMonoN (← ctx.levelParamsOf fresh #[type]) type value ctx.ref

/-- `T.F.rel_refl`: a layer is related to itself by a reflexive relation, `T.F.rel_fmap` at the
identity, rewritten by `T.F.fmap_id`. -/
def genRelRefl : TermElabM Unit := do
  if (← getEnv).contains ctx.relReflN then return
  let fresh := ctx.freshLevels 1
  let w := ctx.holeLevel (.param fresh[0]!)
  withLocalDecl `X .implicit (← ctx.famType w) fun X => do
  withLocalDecl `R .implicit (← ctx.famRel X X) fun R => do
  let hTy ← ctx.withJs fun js => withLocalDeclD `x (mkAppN X js) fun x => do
    mkForallFVars (js.push x) (mkAppN R (js ++ #[x, x]))
  withLocalDeclD `h hTy fun h => do
  withLocalDeclD `a (← ctx.fAt w X ctx.idx) fun a => do
  let idF ← if ctx.idxed then
      ctx.withJs fun js => withLocalDeclD `x (mkAppN X js) fun x => mkLambdaFVars (js.push x) x
    else mkAppOptM ``id #[X]
  let xs := ctx.params ++ #[X, R, h] ++ ctx.idx ++ #[a]
  let type ← withBinderInfo (ctx.params ++ ctx.idx) .implicit do
    mkForallFVars xs (← ctx.relAt w w X X R ctx.idx a a)
  let relMap ← ctx.genAt ctx.Frel_map [w, w, w] (#[X, X, X, R, idF, idF] ++ ctx.idx ++ #[a, h])
  let mapId ← ctx.genAt ctx.Fmap_id [w] (#[X] ++ ctx.idx ++ #[a])
  let relSelf ← withLocalDeclD `b (← ctx.fAt w X ctx.idx) fun b => do
    mkLambdaFVars #[b] (← ctx.relAt w w X X R ctx.idx b b)
  let value ← mkAppM ``Eq.mp #[← mkCongrArg relSelf mapId, relMap]
  addThm ctx.relReflN (← ctx.levelParamsOf fresh #[type]) type
    (← mkLambdaFVars xs value) ctx.ref

/-- The one-step lemmas of `T.F.Rel` (for a single type; per type in a block, `Gen/Surface.lean`),
`T.F.Rel.mono` and `T.F.rel_refl`. -/
def genRelLemmas : TermElabM Unit := do
  unless ctx.isBlock do
    let fresh := ctx.freshLevels 2
    let (wX, wY) := (ctx.holeLevel (.param fresh[0]!), ctx.holeLevel (.param fresh[1]!))
    withLocalDecl `X .implicit (← ctx.famType wX) fun X => do
    withLocalDecl `Y .implicit (← ctx.famType wY) fun Y => do
    withLocalDecl `R .implicit (← ctx.famRel X Y) fun R => do
    ctx.genRelSteps {
      vars := #[X, Y, R], repX := fun _ idx => mkAppN X idx, repY := fun _ idx => mkAppN Y idx
      wX, wY, famX := X, famY := Y
      rel := fun idx a b => ctx.relAt wX wY X Y R idx a b
      premise := fun a σ y y' => ctx.relPremise a wX wY R σ y y'
      idxOf := fun c σ => c.idx.map σ
      name := fun c c' => ctx.nF s!"rel_{c.fname}_{c'.fname}"
      ctors := ctx.ctors, fresh, ref := ctx.ref }
  ctx.genRelMono
  ctx.genRelRefl

end Ctx

end Codata.Gen
