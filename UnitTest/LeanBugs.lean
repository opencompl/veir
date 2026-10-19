import Lean

/-!
Known upstream Lean bugs. These tests deliberately expect the current failure, so
a Lean upgrade that fixes a bug makes the corresponding `#guard_msgs` fail.
-/

/-! The current Lean version generates an ill-typed proof when `cbv` reduces `if True`.
When this starts succeeding, revisit the `PuddleCbv.guard_eq_cond` workaround in
Veir/PatternRewriter/Puddle/Validity.lean and replace this with a success test. -/

/--
error: (kernel) application type mismatch
  ite_true
argument has type
  Nat
but function has type
  ∀ {x : Decidable True} (a b : Nat), (if True then a else b) = a
-/
#guard_msgs in
example : (if True then 0 else 1 : Nat) = 0 := by
  cbv
