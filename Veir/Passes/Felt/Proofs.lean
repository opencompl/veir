import Veir.Data.Felt.Basic

/-!
  Soundness proofs for `Veir/Passes/Felt/Combine.lean`.

  Each pattern in `Combine.lean` is paired with an algebraic identity
  here. The pattern matches the syntactic shape; this file proves the
  semantic equivalence. The pass-side `sorry`s on rewriter preconditions
  are consistent with current VEIR practice (see `harness/coverage.md`
  §Verification machinery); the bar this file clears is the semantic
  theorem, not the precondition discharge.

  Phase E.5 (2026-05-19) upgraded the proof model from `abbrev Felt
  := Int` to `abbrev Felt p := ZMod p`. Each theorem now universally
  quantifies over the modulus `p`, capturing the IR-level fact that
  LLZK doesn't pin a specific field at the dialect level. The proofs
  remain one-liners because Mathlib's commutative-ring instances on
  `ZMod p` discharge the identities exactly as `Int.*` did.
-/

namespace Veir.Data.Felt

/--
  `felt.add x (felt.const 0) = x`. Soundness of the
  `right_identity_zero_add` pattern in `Veir/Passes/Felt/Combine.lean`.
-/
theorem right_identity_zero_add (p : Nat) (lhs : Felt p) :
    add lhs (const p 0) = lhs := by
  show lhs + ((0 : Int) : ZMod p) = lhs
  simp

/--
  `felt.add (felt.const c1) (felt.const c2) = felt.const (c1 + c2)`.
  Soundness of `constant_fold_add` in `Veir/Passes/Felt/Combine.lean`.

  The Mathlib coercion `Int → ZMod p` is a ring homomorphism, so
  `↑c1 + ↑c2 = ↑(c1 + c2)` in `ZMod p`.
-/
theorem constant_fold_add (p : Nat) (c1 c2 : Int) :
    add (const p c1) (const p c2) = const p (c1 + c2) := by
  show ((c1 : ZMod p) + (c2 : ZMod p)) = ((c1 + c2 : Int) : ZMod p)
  push_cast
  ring

/--
  `felt.sub x x = felt.const 0`. Soundness of `self_subtraction_to_zero`
  in `Veir/Passes/Felt/Combine.lean`.
-/
theorem self_subtraction_to_zero (p : Nat) (x : Felt p) :
    sub x x = const p 0 := by
  show x - x = ((0 : Int) : ZMod p)
  simp

/--
  `felt.add (felt.add x c1) c2 = felt.add x (c1 + c2)`. Soundness of
  `assoc_const_fold_add` in `Veir/Passes/Felt/Combine.lean`.
-/
theorem assoc_const_fold_add (p : Nat) (x : Felt p) (c1 c2 : Int) :
    add (add x (const p c1)) (const p c2) = add x (const p (c1 + c2)) := by
  show (x + (c1 : ZMod p)) + (c2 : ZMod p) = x + ((c1 + c2 : Int) : ZMod p)
  push_cast
  ring

end Veir.Data.Felt
