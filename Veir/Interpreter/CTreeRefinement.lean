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
