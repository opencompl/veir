module

public meta import Lean
public import QPFTypes.Theory.QPF.Cofix.WithBot
public import QPFTypes.Meta.QPFAttr.Cofix

/-!
# Monotonicity of `codef` functions in their possibly-partial arguments

`codef f xs := body` defines `f.__partial` with `partial_fixpoint`, which only ensures that the
body is monotone in the recursive calls. For `f` to be usable on possibly-partial values in the
body of another `codef` (or `partial_fixpoint`) definition, as in
```
codef nats' : Stream Nat := cons 0 (map (· + 1) nats')
```
`f.__partial` also has to be monotone in its possibly-partial arguments: this file proves
```
f.__partial_mono {δ} [PartialOrder δ] ys (xs_fn : δ → PT) (hx : monotone xs_fn) :
  monotone (fun z => f.__partial ys (xs_fn z))
```
of the same form as the monotonicity lemmas of `@[qpf_ctor]` and `@[qpf_elim]`, and registers
it with `@[partial_fixpoint_monotone]`.

The proof is by fixpoint induction (`f.__partial.fixpoint_induct`), with the motive that `g`
is monotone in each possibly-partial argument `rᵢ`, for fixed earlier arguments:
`∀ r₀ .. rᵢ₋₁, monotone (fun rᵢ => g r₀ .. rᵢ)` (whose codomain is ordered pointwise). This is
admissible (`CofixWithBot.admissible_monotone`), and the induction step is proved like the
monotonicity side goals of `partial_fixpoint`, using the induction hypothesis for the
recursive calls (see `qpf_codef_mono`).

## Limitations

* The lemma is only proved if the possibly-partial arguments are not among the fixed
  parameters of `f.__partial`, i.e. those that `partial_fixpoint` does not abstract over, since
  the fixpoint induction principle then does not apply. Otherwise, no lemma is added.
-/

public meta section

namespace QPFTypes.Codef

open Lean Meta Elab

/-- The suffix for the monotonicity lemma of the partial version of a function. -/
def partialMonoSuffix : Name := `__partial_mono

/-- A universe level name which is not among `lvls`. -/
def freshLevelName (lvls : List Name) (base : String) : Name := Id.run do
  let mut i := 0
  let mut n := Name.mkSimple base
  while lvls.contains n do
    i := i + 1
    n := Name.mkSimple s!"{base}_{i}"
  return n

/-- The name of the induction hypothesis for the recursive calls, used by `qpf_codef_mono`. -/
def codefMonoIH : Name := `__codef_mono_ih

/--
`qpf_codef_mono` proves the induction step of the monotonicity proof of a `codef` function in
its possibly-partial arguments (see `QPFTypes.Meta.CodefMono`), i.e. the monotonicity of its
unfolding in one of these arguments, given the induction hypothesis `__codef_mono_ih` for the
recursive calls.
-/
syntax (name := qpfCodefMono) "qpf_codef_mono" : tactic

open Lean.Order in
@[tactic qpfCodefMono]
def evalQpfCodefMono : Tactic.Tactic := fun _ => do
  let ih := mkIdent codefMonoIH
  Tactic.evalTactic (← `(tactic| first
    | assumption
    | exact Lean.Order.monotone_const _
    | exact Lean.Order.monotone_id
    | (apply $ih:ident <;> qpf_codef_mono)
    -- E.g. for constructors and eliminators, with their `__partial_mono` lemmas.
    | (monotonicity <;> qpf_codef_mono)))

/-- `Mᵢ g := ∀ r₀ .. rⱼ₋₁, monotone (fun rⱼ => g r₀ .. rⱼ)`, the monotonicity of `g` in its
`j`-th argument. -/
def mkMonoIn (g : Expr) (j : Nat) : MetaM Expr := do
  forallBoundedTelescope (← inferType g) (some j) fun rs _ => do
    let gr := mkAppN g rs
    let .forallE n d _ bi ← whnf (← inferType gr)
      | throwError "codef: unexpected type of{indentExpr gr}"
    let fn ← withLocalDecl n bi d fun r => mkLambdaFVars #[r] (mkApp gr r)
    mkForallFVars rs (← mkAppM ``Lean.Order.monotone #[fn])

/-- For a function type `G = ∀ rs r, B`, with `rs` given, and `B` independent of `r`: the
predicate `fun g : G => monotone (fun r => g rs r)`, and a proof of its admissibility, with
`admissible_apply` and `admissible_monotone`. -/
partial def mkAdmMonoEval (G : Expr) : List Expr → MetaM (Expr × Expr)
  | [] => do
    let .forallE n D B _ ← whnf G | throwError "codef: unexpected type{indentExpr G}"
    if B.hasLooseBVars then
      throwError "codef: the type{indentExpr G}\nis dependent"
    let pred ← withLocalDeclD `g G fun g => do
      let fn ← withLocalDeclD n D fun r => mkLambdaFVars #[r] (mkApp g r)
      mkLambdaFVars #[g] (← mkAppM ``Lean.Order.monotone #[fn])
    let proof ← mkAppOptM ``QPF.CofixWithBot.admissible_monotone #[D, none, B, none]
    return (pred, proof)
  | r :: rs => do
    let C ← instantiateForall G #[r]
    let (pred', proof') ← mkAdmMonoEval C rs
    let proof ← mkAppM ``Lean.Order.admissible_apply #[← mkLambdaFVars #[r] pred', r, proof']
    let pred ← withLocalDeclD `g G fun g => mkLambdaFVars #[g] (mkApp pred' (mkApp g r)).headBeta
    return (pred, proof)

/-- A proof of `admissible (fun g : G => Mᵢ g)`, see `mkMonoIn`, with `admissible_pi`. -/
def mkAdmMonoIn (G : Expr) (j : Nat) : MetaM Expr := do
  forallBoundedTelescope G (some j) fun rs _ => do
    let (_, proof) ← mkAdmMonoEval G rs.toList
    -- Quantify over `rs`, innermost first.
    let mut proof := proof
    for t in (List.range rs.size).reverse do
      let P ← withLocalDeclD `g G fun g => do
        mkLambdaFVars #[g, rs[t]!] (← mkMonoIn' g rs t)
      proof ← mkAppM ``Lean.Order.admissible_pi #[P, ← mkLambdaFVars #[rs[t]!] proof]
    return proof
where
  /-- `∀ rₜ₊₁ .. rⱼ₋₁, monotone (fun rⱼ => g r₀ .. rⱼ)`, for given `r₀ .. rₜ`. -/
  mkMonoIn' (g : Expr) (rs : Array Expr) (t : Nat) : MetaM Expr := do
    let gr := mkAppN g rs
    let .forallE n d _ bi ← whnf (← inferType gr)
      | throwError "codef: unexpected type of{indentExpr gr}"
    let fn ← withLocalDecl n bi d fun r => mkLambdaFVars #[r] (mkApp gr r)
    mkForallFVars rs[t+1:] (← mkAppM ``Lean.Order.monotone #[fn])

/-- The conjunction `P₁ ∧ (P₂ ∧ .. Pₙ)` of a nonempty list. -/
def mkAndN' (ps : Array Expr) : Expr :=
  ps.pop.foldr mkAnd ps.back!

/-- The proofs of the conjuncts of `h : P₁ ∧ (P₂ ∧ .. Pₙ)`. -/
def splitAndN (h : Expr) (n : Nat) : MetaM (Array Expr) := do
  let mut h := h
  let mut hs := #[]
  for _ in [1:n] do
    hs := hs.push (← mkAppM ``And.left #[h])
    h ← mkAppM ``And.right #[h]
  return hs.push h

/-- Given proofs `ms` of `Mⱼ g` (see `mkMonoIn`), for the positions `j` of the possibly-partial
arguments of `g`, a proof of
```
∀ as (xs : δ → PT) (hx : monotone xs), monotone (fun z => g as[xs z])
```
where `as` are the other arguments of `g`, and the possibly-partial arguments are `xs z`. The
proof changes the possibly-partial arguments from `xs z₁` to `xs z₂` one at a time. -/
partial def mkJointMono (g : Expr) (ms : Array (Nat × Expr)) (δ : Expr) : MetaM Expr := do
  go (← inferType g) 0 #[] #[]
where
  go (G : Expr) (j : Nat) (binders : Array Expr) (xs : Array (Nat × Expr)) : MetaM Expr := do
    match ← whnf G with
    | .forallE n D B bi =>
      if ms.any (·.1 == j) then
        withLocalDeclD (n.appendAfter "_fn") (← mkArrow δ D) fun x =>
          go (B.instantiate1 x) (j + 1) (binders.push x) (xs.push (j, x))
      else
        withLocalDecl n bi D fun a => go (B.instantiate1 a) (j + 1) (binders.push a) xs
    | _ =>
      let hTys ← xs.mapM fun (_, x) => mkAppM ``Lean.Order.monotone #[x]
      -- `hxs : monotone xs_fn`, named after the argument `xs`.
      let hNames ← xs.mapM fun (_, x) => do
        let n := (← x.fvarId!.getUserName).eraseMacroScopes.toString
        return Name.mkSimple ("h" ++ (n.dropEnd 3).toString)
      withLocalDeclsDND (hNames.zip hTys) fun hxs => do
      withLocalDeclD `z₁ δ fun z₁ => withLocalDeclD `z₂ δ fun z₂ => do
      withLocalDeclD `hz (← mkAppM ``Lean.Order.PartialOrder.rel #[z₁, z₂]) fun hz => do
        let argsAt (t : Nat) : Array Expr := binders.mapIdx fun i a =>
          match xs.findIdx? (·.1 == i) with
          | some s => mkApp a (if s < t then z₂ else z₁)
          | none => a
        let mut chain : Option Expr := none
        for h : t in [:xs.size] do
          let (p, x) := xs[t]
          let some (_, m) := ms.find? (·.1 == p) | unreachable!
          let args := argsAt t
          let step := mkAppN m (args[:p].toArray ++
            #[mkApp x z₁, mkApp x z₂, mkApp3 hxs[t]! z₁ z₂ hz] ++ args[p+1:].toArray)
          let next ← match chain with
            | none => pure step
            | some c => mkAppM ``Lean.Order.PartialOrder.rel_trans #[c, step]
          chain := some next
        let some chain' := chain | throwError "codef: no possibly-partial arguments"
        let fn ← withLocalDeclD `z δ fun z => mkLambdaFVars #[z] (mkAppN g (argsAt 0 |>.map
          fun a => a.replaceFVar z₁ z))
        let proof ← mkLambdaFVars #[z₁, z₂, hz] chain'
        let type ← mkAppM ``Lean.Order.monotone #[fn]
        mkLambdaFVars (binders ++ hxs) (← mkExpectedTypeHint proof type)

/-- Prove and add `declName.__partial_mono`, for a function `declName` defined by `codef`, see
the module docstring. Returns whether the lemma was added. -/
def addCodefMono (declName : Name) : TermElabM Bool := do
  let pName := declName ++ QPFAttr.partialSuffix
  let pInfo ← getConstInfo pName
  let lvlNames := pInfo.levelParams
  let lvls := lvlNames.map mkLevelParam
  let p := Expr.const pName lvls
  let indName ← realizeGlobalConstNoOverloadCore (pName ++ `fixpoint_induct)
  let indTy ← instantiateTypeLevelParams (← getConstInfo indName).toConstantVal lvls
  -- The number of fixed parameters, which precede the motive in `fixpoint_induct`.
  let some k ← forallTelescope indTy fun ys _ =>
      ys.findIdxM? fun y => return (← y.fvarId!.getUserName) == `motive
    | throwError "codef: unexpected type of `{.ofConstName indName}`"
  forallTelescope pInfo.type fun ps _ => do
    let partialPos ← (Array.range ps.size).filterM fun i => do
      QPFAttr.isPartialType (← inferType ps[i]!)
    if partialPos.isEmpty then return false
    if partialPos.any (· < k) then
      trace[QPFTypes] "Not adding {declName ++ partialMonoSuffix}: a possibly-partial argument \
        is a fixed parameter of `{.ofConstName pName}`"
      return false
    let fixed := ps[:k].toArray
    let js := partialPos.map (· - k)
    let pf := mkAppN p fixed
    let G ← inferType pf
    -- The motive, and its admissibility.
    let motive ← withLocalDeclD `g G fun g => do
      mkLambdaFVars #[g] (mkAndN' (← js.mapM fun j => mkMonoIn g j))
    let adms ← js.mapM fun j => mkAdmMonoIn G j
    let preds ← js.mapM fun j => withLocalDeclD `g G fun g => do
      mkLambdaFVars #[g] (← mkMonoIn g j)
    let mut adm := adms.back!
    let mut pred := preds.back!
    for t in (List.range (js.size - 1)).reverse do
      adm ← mkAppM ``Lean.Order.admissible_and #[preds[t]!, pred, adms[t]!, adm]
      pred ← withLocalDeclD `g G fun g => do
        mkLambdaFVars #[g] (mkAnd (preds[t]!.beta #[g]) (pred.beta #[g]))
    -- The induction step.
    let .forallE _ stepTy _ _ ← whnf (← instantiateForall indTy (fixed ++ #[motive, adm]))
      | throwError "codef: unexpected type of `{.ofConstName indName}`"
    let stepTy ← Core.betaReduce stepTy
    let step ← forallBoundedTelescope stepTy (some 2) fun gh goal => do
      let #[g, hg] := gh | throwError "codef: unexpected type of `{.ofConstName indName}`"
      let ms := js.zip (← splitAndN hg js.size)
      let goals ← (← splitAndNTy goal js.size).mapIdxM fun t ty => do
        let mvar ← mkFreshExprSyntheticOpaqueMVar ty
        let (_, m) ← mvar.mvarId!.introN js[t]!
        m.withContext do
          let tgt ← instantiateMVars (← m.getType)
          unless tgt.isAppOfArity ``Lean.Order.monotone 5 do
            throwError "codef: unexpected monotonicity goal{indentExpr tgt}"
          let δ := tgt.getAppArgs[0]!
          let ih ← mkJointMono g ms δ
          let m ← m.assert codefMonoIH (← inferType ih) ih
          let (_, m) ← m.intro1P
          let gs ← Tactic.run m (Tactic.evalTactic (← `(tactic| qpf_codef_mono)))
          unless gs.isEmpty do
            throwError "codef: failed to prove the monotonicity of `{.ofConstName pName}`, \
              unsolved goals:{goalsToMessageData gs}"
        instantiateMVars mvar
      let mut proof := goals.back!
      for t in (List.range (goals.size - 1)).reverse do
        proof ← mkAppM ``And.intro #[goals[t]!, proof]
      mkLambdaFVars gh proof
    let key := mkAppN (.const indName lvls) (fixed ++ #[motive, adm, step])
    let ms := js.zip (← splitAndN key js.size)
    -- The lemma, with the same binders as those of `@[qpf_ctor]` and `@[qpf_elim]`.
    let w := freshLevelName lvlNames "w"
    withLocalDecl `δ .implicit (.sort (.param w)) fun δ => do
    withLocalDecl `inst .instImplicit (← mkAppM ``Lean.Order.PartialOrder #[δ]) fun instδ => do
      let joint ← mkJointMono pf ms δ
      forallTelescope (← inferType joint) fun bs goal => do
        let rest := ps[k:].toArray
        let otherParams := fixed ++ (rest.zip bs).filterMap fun (r, b) =>
          if partialPos.contains (rest.idxOf r + k) then none else some b
        let fns := (rest.zip bs).filterMap fun (r, b) =>
          if partialPos.contains (rest.idxOf r + k) then some b else none
        let hs := bs[rest.size:].toArray
        let binders := #[δ, instδ] ++ otherParams ++ fns ++ hs
        let type ← instantiateMVars (← mkForallFVars binders goal)
        let value ← instantiateMVars (← mkLambdaFVars binders (mkAppN joint bs))
        let name := declName ++ partialMonoSuffix
        withOptions (warn.sorry.set · false) <| addDecl <| .thmDecl {
          name, levelParams := lvlNames ++ [w], type, value
        }
        return true
where
  /-- The conjuncts of `P₁ ∧ (P₂ ∧ .. Pₙ)`. -/
  splitAndNTy (ty : Expr) (n : Nat) : MetaM (Array Expr) := do
    let mut ty := ty
    let mut ps := #[]
    for _ in [1:n] do
      let some (a, b) := ty.and? | throwError "codef: expected a conjunction{indentExpr ty}"
      ps := ps.push a
      ty := b
    return ps.push ty

end QPFTypes.Codef
