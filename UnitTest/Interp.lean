module

import Veir.Interpreter.Interp

/-!
  A `partial_fixpoint` in `Interp` gives a run that never returns the least
  element of the order, which is `spin`.
-/

open Veir

/-- A function that never returns. -/
private def diverge (n : Nat) : Interp Nat := diverge n
partial_fixpoint

/-- It is `spin` rather than an arbitrary value. -/
example : diverge 0 = .spin := by
  apply diverge.fixpoint_induct 0 (motive := fun f => f = .spin)
  · exact Interp.admissible_of_spin _ rfl
  · intro f ih
    exact ih

/-- `spin` is below every outcome. -/
example (x : Interp Nat) : Lean.Order.PartialOrder.rel .spin x :=
  Interp.rel_iff.mpr (.inl rfl)

/-- Nothing else is, not even `ub`. -/
example : ¬ Lean.Order.PartialOrder.rel (.ub none : Interp Nat) .spin := by
  intro h
  rcases Interp.rel_iff.mp h with h | h <;> cases h

/-- A function that never returns may recurse under `withBlame`. -/
private def divergeBlamed (op : OperationPtr) (n : Nat) : Interp Nat :=
  (divergeBlamed op n).withBlame op
partial_fixpoint
