module

public meta import Lean
public import Veir.Interpreter.CTree
public import Veir.Interpreter.Refinement.Lemmas
public import CTree.Sim

import all Veir.Interpreter.CTree
import all CTree.Defs

public section

namespace Veir

open CTree

namespace Tree

/-- Normalize the explicit CTree bind exposed by interpreter simplification. -/
@[simp]
theorem bind_pure_left (value : α) (next : α → Tree β) :
    CTree.bind (pure value) next = next value := CTree.CTree.bind_ret value next

@[simp]
theorem fail_bind (next : α → Tree β) : CTree.bind fail next = fail := by
  simp only [fail, CTree.trigger, Bind.bind, CTree.CTree.bind_vis]
  congr 1
  funext impossible
  exact nomatch impossible

@[simp]
theorem ub_bind (next : α → Tree β) : CTree.bind ub next = ub := by
  simp only [ub, CTree.trigger, Bind.bind, CTree.CTree.bind_vis]
  congr 1
  funext impossible
  exact nomatch impossible

/-- Reify terminal interpreter events as outcomes, preserving all choice nodes.
Unlike an ordinary event handler, this stops at UB/failure without invoking the
event's `Empty` continuation. Execution is composed with CTree bind *before*
this adapter is applied. -/
def interp_ub_and_error (tree : Tree α) : Tree (Interp α) :=
  match tree.unfold with
  | .ret value => pure (.ok value)
  | .tau choice next => .tauG choice (fun value => interp_ub_and_error (next value))
  | .vis (.inl _) _ => pure (.fail none)
  | .vis (.inr _) _ => pure (.ub none)
partial_fixpoint

@[simp]
theorem interp_ub_and_error_pure (value : α) : interp_ub_and_error (pure value) = pure (.ok value) := by
  rw [interp_ub_and_error]
  simp

@[simp]
theorem interp_ub_and_error_tau (choice : C1In ⊕ FreezeCIn)
    (next : (C1 ⊕ₑ FreezeC) choice → Tree α) :
    interp_ub_and_error (.tauG choice next) = .tauG choice (fun value => interp_ub_and_error (next value)) := by
  rw [interp_ub_and_error]
  simp

@[simp]
theorem interp_ub_and_error_fail : interp_ub_and_error (fail : Tree α) = pure (.fail none) := by
  rw [interp_ub_and_error]
  simp [fail, CTree.trigger, Bind.bind]

@[simp]
theorem interp_ub_and_error_ub : interp_ub_and_error (ub : Tree α) = pure (.ub none) := by
  rw [interp_ub_and_error]
  simp [ub, CTree.trigger, Bind.bind]

/-- Interpreting a bind continues successful results and propagates terminal UB/errors. -/
theorem interp_ub_and_error_bind (tree : Tree α) (next : α → Tree β) :
    interp_ub_and_error (CTree.bind tree next) =
      CTree.bind (interp_ub_and_error tree) (fun result =>
        match result with
        | .ok value => interp_ub_and_error (next value)
        | .fail x => pure (.fail x)
        | .ub x => pure (.ub x)) := by
  ext n
  induction n generalizing tree with
  | zero => rfl
  | succ n ih =>
    cases tree using CTree.CTree.cases with
    | ret value => simp
    | tau choice cont =>
      simp only [CTree.CTree.bind_tau, interp_ub_and_error_tau, approx_tau_succ]
      congr 1
      funext value
      exact ih (cont value)
    | vis event cont =>
      simp only [CTree.CTree.bind_vis]
      cases event <;>
        rw [interp_ub_and_error, unfold_vis, interp_ub_and_error, unfold_vis] <;>
        simp

/-- Stateful refinement: every target choice is simulated by a source choice.
The argument order follows Veir's source-to-target refinement convention. -/
@[expose]
def Refines (relation : α → β → Prop) (source : Tree α) (target : Tree β) : Prop :=
  Sim (fun target source => Interp.isRefinedBy relation source target)
    (interp_ub_and_error target) (interp_ub_and_error source)

section

open Lean Meta Parser.Term PrettyPrinter.Delaborator SubExpr

/-- Display concrete CTree binds as a sequence without unfolding operation semantics. -/
meta partial def delabTreeDoElems : DelabM (List (TSyntax `doElem)) := do
  let e ← getExpr
  if e.isAppOfArity ``CTree.bind 8 || e.isAppOfArity ``Bind.bind 6 then
    let action ← withAppFn <| withAppArg delab
    withAppArg do
      let Expr.lam _ type body _ ← getExpr | do
        let name ← getUnusedName `value (← getExpr)
        let next ← delab
        let call ← `($next $(mkIdent name))
        return [← `(doElem|let $(mkIdent name) ← $action:term),
          ← `(doElem|$call:term)]
      withBindingBodyUnusedName fun name => do
        if body.hasLooseBVars then
          prependAndRec `(doElem|let $(⟨name⟩):term ← $action:term)
        else if type.isConstOf ``Unit || type.isConstOf ``PUnit then
          prependAndRec `(doElem|$action:term)
        else
          prependAndRec `(doElem|let _ ← $action:term)
  else if e.isLet then
    let Expr.letE name type value body nondep ← getExpr | failure
    let name ← getUnusedName name body
    let typeStx ← descend type 0 delab
    let valueStx ← descend value 1 delab
    withLetDecl name type value (nondep := nondep) fun fvar =>
      descend (body.instantiate1 fvar) 2 <|
        if nondep then
          prependAndRec `(doElem|have $(mkIdent name) : $typeStx := $valueStx)
        else
          prependAndRec `(doElem|let $(mkIdent name) : $typeStx := $valueStx)
  else if e.isAppOf ``Pure.pure || e.isAppOf ``CTree.CTree.ret then
    let value ← withAppArg delab
    return [← `(doElem|return $value)]
  else
    let action ← delab
    return [← `(doElem|$action:term)]
where
  prependAndRec elem : DelabM _ := List.cons <$> elem <*> delabTreeDoElems

meta def delabTreeDo : Delab := do
  let elems ← delabTreeDoElems
  let items ← elems.toArray.mapM (`(doSeqItem|$(·):doElem))
  `(do $items:doSeqItem*)

/-- Show both sides of refinement as programs, including a single-operation side. -/
@[app_delab Refines]
meta def delabRefines : Delab :=
  whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
    guard <| (← getExpr).isAppOfArity ``Refines 5
    let refines ← withAppFn <| withAppFn <| withAppFn delab
    let relation ← withAppFn <| withAppFn <| withAppArg delab
    let source ← withAppFn <| withAppArg delabTreeDo
    let target ← withAppArg delabTreeDo
    `($refines $relation $source $target)

end

theorem refines_pure (relation : α → β → Prop) (source : α) (target : β)
    : Refines relation (pure source) (pure target) ↔ relation source target := by
  unfold Refines
  simp

/-- Weakening the relation on successful return values preserves tree refinement. -/
theorem refines_mono {relation relation' : α → β → Prop}
    (hrelation : ∀ source target, relation source target → relation' source target)
    {source : Tree α} {target : Tree β} (h : Refines relation source target) :
    Refines relation' source target := by
  unfold Refines at *
  have hresult := Sim.bind _ _ (fun value => pure value) (fun value => pure value) h
    (RR' := fun target source => Interp.isRefinedBy relation' source target) (by
      intro target source h
      apply (Sim.pure _ _ _).mpr
      cases source <;> cases target <;> simp_all [Interp.isRefinedBy])
  change Sim _ (interp_ub_and_error target >>= pure)
    (interp_ub_and_error source >>= pure) at hresult
  simpa using hresult

/-- Source failure admits every target that source UB admits, using the existing
outcome convention. This does not assume that UB admits an arbitrary infinite tree. -/
theorem refines_fail_of_refines_ub (relation : α → β → Prop) (target : Tree β)
    (hub : Refines relation (ub : Tree α) target) :
    Refines relation (fail : Tree α) target := by
  unfold Refines at *
  rw [interp_ub_and_error_ub] at hub
  rw [interp_ub_and_error_fail]
  have hresult := Sim.bind _ _ (fun value => pure value)
    (fun (_ : Interp α) => pure (Interp.fail none)) hub
    (RR' := fun target source => Interp.isRefinedBy relation source target) (by
      intro target source _
      apply (Sim.pure _ _ _).mpr
      trivial)
  change Sim _ (interp_ub_and_error target >>= pure)
    ((pure (Interp.ub none) : Tree (Interp α)) >>= fun _ => pure (Interp.fail none)) at hresult
  simpa using hresult

/-- Undefined source behavior permits every target behavior, including divergence.
This is the explicit UB-top assumption for CTree refinement. -/
axiom refines_ub (relation : α → β → Prop) (target : Tree β) :
    Refines relation (ub : Tree α) target

/-- Interpreter failure follows the same unconstrained-source convention as UB. -/
theorem refines_fail (relation : α → β → Prop) (target : Tree β) :
    Refines relation (fail : Tree α) target :=
  refines_fail_of_refines_ub relation target (refines_ub relation target)

/-- Compose related tree computations with related continuations. Terminal source
errors use the UB-top convention, including when the target continuation diverges. -/
theorem refines_bind {relation : α → β → Prop} {relation' : γ → δ → Prop}
    {source : Tree α} {target : Tree β}
    {sourceNext : α → Tree γ} {targetNext : β → Tree δ}
    (hhead : Refines relation source target)
    (hnext : ∀ a b, relation a b → Refines relation' (sourceNext a) (targetNext b)) :
    Refines relation' (CTree.bind source sourceNext) (CTree.bind target targetNext) := by
  have hterminal (result : Interp γ)
      (htotal : ∀ value, Interp.isRefinedBy relation' result value) (tree : Tree δ) :
      Sim (fun target source => Interp.isRefinedBy relation' source target)
        (interp_ub_and_error tree) (pure result : Tree (Interp γ)) := by
    have hub := refines_ub relation' tree
    unfold Refines at hub
    rw [interp_ub_and_error_ub] at hub
    have hresult := Sim.bind _ _ (fun value => pure value)
      (fun (_ : Interp γ) => pure result) hub
      (RR' := fun target source => Interp.isRefinedBy relation' source target) (by
        intro target source _
        exact (Sim.pure _ _ _).mpr (htotal target))
    change Sim _ (interp_ub_and_error tree >>= pure)
      ((pure (Interp.ub none) : Tree (Interp γ)) >>= fun _ => pure result) at hresult
    simpa using hresult
  unfold Refines at hhead ⊢
  rw [interp_ub_and_error_bind, interp_ub_and_error_bind]
  apply Sim.bind _ _ _ _ hhead
  intro targetResult sourceResult hresult
  cases sourceResult with
  | fail error =>
    cases targetResult <;>
      simp only [Sim.pure, Interp.isRefinedBy] <;>
      try trivial
    exact hterminal (.fail error) (by intro; trivial) _
  | ub error =>
    cases targetResult <;>
      simp only [Sim.pure, Interp.isRefinedBy] <;>
      try trivial
    exact hterminal (.ub error) (by intro; trivial) _
  | ok sourceValue =>
    cases targetResult with
    | fail error => cases hresult
    | ub error => cases hresult
    | ok targetValue => exact hnext sourceValue targetValue hresult

/-- An action with a finite outcome can be discarded when its result is unused.
The UB hypothesis makes the required treatment of arbitrary target continuations
explicit, including continuations that diverge. -/
theorem refines_discard_of_canInterpretTo_of_refines_ub (relation : β → γ → Prop)
    {action : Tree α} {outcome : Interp α} {source : Tree β} {target : Tree γ}
    (hub : Refines relation (ub : Tree β) target)
    (haction : PureOrErr.CanInterpretTo action outcome)
    (hcontinuation : Refines relation source target) :
    Refines relation (CTree.bind action (fun _ => source)) target := by
  induction haction with
  | ret value => simpa using hcontinuation
  | tau choice next value result h ih =>
    unfold Refines at ih ⊢
    rw [CTree.CTree.bind_tau, interp_ub_and_error_tau]
    exact Sim.tau_r _ choice _ _ value ih
  | fail =>
    have hfail := refines_fail_of_refines_ub relation target hub
    unfold Refines at hfail ⊢
    rw [CTree.CTree.bind_vis]
    conv => rhs; rw [interp_ub_and_error, unfold_vis]
    change Sim (fun target source => Interp.isRefinedBy relation source target)
      (interp_ub_and_error target) (pure (Interp.fail (α := β) none))
    simpa only [interp_ub_and_error_fail] using hfail
  | ub =>
    unfold Refines at hub ⊢
    rw [CTree.CTree.bind_vis]
    conv => rhs; rw [interp_ub_and_error, unfold_vis]
    change Sim (fun target source => Interp.isRefinedBy relation source target)
      (interp_ub_and_error target) (pure (Interp.ub (α := β) none))
    simpa only [interp_ub_and_error_ub] using hub

/-- Every finite interpreter tree has an outcome: all silent and freeze choices
have at least one possible response. -/
theorem exists_canInterpretTo {action : Tree α} (haction : PureOrErr action) :
    ∃ outcome, PureOrErr.CanInterpretTo action outcome := by
  induction haction with
  | ret value => exact ⟨.ok value, .ret value⟩
  | tau choice next _ ih =>
    have hchoice : Nonempty ((C1 ⊕ₑ FreezeC) choice) := by
      cases choice with
      | inl choice => cases choice; exact ⟨.unit⟩
      | inr choice =>
        cases choice with
        | mk width => exact ⟨(0 : BitVec width)⟩
        | pointer => exact ⟨(default : Data.Pointer)⟩
    obtain ⟨value⟩ := hchoice
    obtain ⟨outcome, houtcome⟩ := ih value
    exact ⟨outcome, .tau choice next value outcome houtcome⟩
  | fail => exact ⟨_, .fail⟩
  | ub => exact ⟨_, .ub⟩

/-- Discard a finite action whose returned value is unused, preserving a refining
continuation. The UB hypothesis explicitly covers arbitrary target continuations. -/
theorem refines_discard_of_refines_ub (relation : β → γ → Prop)
    {action : Tree α} {source : Tree β} {target : Tree γ}
    (hub : Refines relation (ub : Tree β) target)
    (haction : PureOrErr action) (hcontinuation : Refines relation source target) :
    Refines relation (CTree.bind action (fun _ => source)) target := by
  obtain ⟨outcome, houtcome⟩ := exists_canInterpretTo haction
  exact refines_discard_of_canInterpretTo_of_refines_ub relation hub houtcome hcontinuation

/-- Discard an action with a finite outcome when its result is unused. -/
theorem refines_discard_of_canInterpretTo (relation : β → γ → Prop)
    {action : Tree α} {outcome : Interp α} {source : Tree β} {target : Tree γ}
    (haction : PureOrErr.CanInterpretTo action outcome)
    (hcontinuation : Refines relation source target) :
    Refines relation (CTree.bind action (fun _ => source)) target :=
  refines_discard_of_canInterpretTo_of_refines_ub relation
    (refines_ub relation target) haction hcontinuation

/-- Discard a finite action whose returned value is unused. -/
theorem refines_discard (relation : β → γ → Prop)
    {action : Tree α} {source : Tree β} {target : Tree γ}
    (haction : PureOrErr action) (hcontinuation : Refines relation source target) :
    Refines relation (CTree.bind action (fun _ => source)) target :=
  refines_discard_of_refines_ub relation (refines_ub relation target) haction hcontinuation

/-- Peel a lifted interpreter result in the target, preserving UB and failure. -/
theorem refines_monadLift_target (relation : α → β → Prop) (source : Tree α)
    (outcome : Interp β) :
    Refines relation source (monadLift outcome) ↔
    match outcome with
    | .ok value => Refines relation source (pure value)
    | .ub _ => Refines relation source ub
    | .fail _ => Refines relation source fail := by
  cases outcome <;> rfl

/-- Peel a lifted target step. Only a successful result runs its continuation. -/
theorem refines_monadLift_bind_target (relation : α → γ → Prop) (source : Tree α)
    (outcome : Interp β) (next : β → Tree γ) :
    Refines relation source (CTree.bind (monadLift outcome) next) ↔
    match outcome with
    | .ok value => Refines relation source (next value)
    | .ub _ => Refines relation source ub
    | .fail _ => Refines relation source fail := by
  cases outcome <;> simp [monadLift, MonadLift.monadLift]

/-- Reflexivity for arbitrary operation trees, including infinite computations,
terminal UB, and failure. -/
theorem refines_refl (relation : α → α → Prop) (hrefl : ∀ value, relation value value)
    (tree : Tree α) : Refines relation tree tree := by
  unfold Refines
  apply Sim.refl
  intro result
  cases result <;> simp [Interp.isRefinedBy, hrefl]

end Tree
end Veir
