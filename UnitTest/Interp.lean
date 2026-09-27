module

import Veir.Interpreter.Interp

/-!
  A `partial_fixpoint` in `Interp` gives a run that never returns the least
  element of the order, which is `ub`.
-/

open Veir

/-- A function that never returns. -/
private def diverge (n : Nat) : Interp Nat := diverge n
partial_fixpoint

/-- It is undefined behaviour rather than an arbitrary value. -/
example : diverge 0 = .ub none := by
  apply diverge.fixpoint_induct 0 (motive := fun f => f = .ub none)
  · exact Interp.admissible_of_ub _ rfl
  · intro f ih
    exact ih

/-- `ub` is below every outcome. -/
example (x : Interp Nat) : Lean.Order.PartialOrder.rel (.ub none) x :=
  Interp.rel_iff.mpr (.inl rfl)

/-- Nothing else is. -/
example : ¬ Lean.Order.PartialOrder.rel (.fail none : Interp Nat) (.ub none) := by
  intro h
  rcases Interp.rel_iff.mp h with h | h <;> cases h
