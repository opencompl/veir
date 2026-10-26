module

public import Veir.Interpreter.CTreeRefinement

import all Veir.Interpreter.CTreeRefinement

public section

namespace Veir.Tree

open CTree

/-- Select one finite source execution before comparing its outcome to the target.
This uses the existential source-choice rule directly, without transitivity. -/
theorem refines_of_canInterpretTo (relation : α → β → Prop)
    {source : Tree α} {outcome : Interp α} {target : Tree β}
    (executes : PureOrErr.CanInterpretTo source outcome)
    (refines : Refines relation (monadLift outcome) target) :
    Refines relation source target := by
  induction executes with
  | ret value => exact refines
  | tau choice next value result step ih =>
    unfold Refines at ih ⊢
    rw [interp_ub_and_error_tau]
    exact Sim.tau_r _ choice _ _ value (ih refines)
  | fail =>
    change Refines relation fail target at refines
    unfold Refines at refines ⊢
    conv => rhs; rw [interp_ub_and_error, unfold_vis]
    simpa only [interp_ub_and_error_fail, Subeffect.mapEff_eq_inl,
      Subeffect.mapEff_eq_self] using refines
  | ub =>
    change Refines relation ub target at refines
    unfold Refines at refines ⊢
    conv => rhs; rw [interp_ub_and_error, unfold_vis]
    simpa only [interp_ub_and_error_ub, Subeffect.mapEff_eq_inr,
      Subeffect.mapEff_eq_self] using refines

/-- Compare a finite source tree with any target by checking its successful
outcomes. Source aborts also allow divergent target behavior. -/
theorem refines_of_finite (relation : α → β → Prop)
    {source : Tree α} (target : Tree β) (finite : PureOrErr source)
    (successful : ∀ value, PureOrErr.CanInterpretTo source (.ok value) →
      Refines relation (pure value) target) :
    Refines relation source target := by
  obtain ⟨outcome, executes⟩ := exists_canInterpretTo finite
  apply refines_of_canInterpretTo relation executes
  cases outcome with
  | ok value => exact successful value executes
  | fail error => exact refines_fail relation _
  | ub error => exact refines_ub relation _

/-- A finite source tree refines a pure target when every successful source
outcome is related to it. An aborting source execution permits that target too. -/
theorem refines_pure_of_finite (relation : α → β → Prop)
    {source : Tree α} (target : β) (finite : PureOrErr source)
    (successful : ∀ value, PureOrErr.CanInterpretTo source (.ok value) →
      relation value target) :
    Refines relation source (pure target) :=
  refines_of_finite relation (pure target) finite fun value executes =>
    (refines_pure relation value target).mpr (successful value executes)

end Veir.Tree
