import Veir.Data.Felt.Basic

/-!
  Soundness proofs for `Veir/Passes/Felt/Combine.lean`.

  Each pattern in `Combine.lean` is paired with an algebraic identity
  here, proven over `Felt p := ZMod p`. This file proves the *arithmetic
  identity only*; it does NOT prove that the IR rewrite preserves program
  semantics or well-formedness. The pass-side rewriter preconditions are
  discharged with `sorry` in `Combine.lean`, so the bar this file clears
  is the algebraic theorem, not the transformation. See `REVIEW.md`
  (finding VC2) for the full trust-boundary writeup.

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
  `↑c1 + ↑c2 = ↑(c1 + c2)` in `ZMod p`. The executable pass may print a
  registered field's canonical reduced representative; that is the same
  `ZMod p` value as `c1 + c2`.
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

/-! ## Tier 1 (E.5 follow-up, 2026-05-20)

  Multiplicative-identity, annihilation, and constant-fold rewrites for
  the remaining basic Felt arithmetic ops. Each identity holds in any
  commutative ring (`ZMod p` for arbitrary `p`).
-/

/-- `felt.mul x (felt.const 1) = x`. Soundness of `right_identity_one_mul`. -/
theorem right_identity_one_mul (p : Nat) (x : Felt p) :
    mul x (const p 1) = x := by
  show x * ((1 : Int) : ZMod p) = x
  simp

/-- `felt.mul x (felt.const 0) = felt.const 0`. Soundness of `right_zero_mul`
    (multiplicative annihilation). -/
theorem right_zero_mul (p : Nat) (x : Felt p) :
    mul x (const p 0) = const p 0 := by
  show x * ((0 : Int) : ZMod p) = ((0 : Int) : ZMod p)
  simp

/-- `felt.sub (felt.const c1) (felt.const c2) = felt.const (c1 - c2)`.
    Registered-field execution may print the canonical reduced representative. -/
theorem constant_fold_sub (p : Nat) (c1 c2 : Int) :
    sub (const p c1) (const p c2) = const p (c1 - c2) := by
  show ((c1 : ZMod p) - (c2 : ZMod p)) = ((c1 - c2 : Int) : ZMod p)
  push_cast
  ring

/-- `felt.mul (felt.const c1) (felt.const c2) = felt.const (c1 * c2)`.
    Registered-field execution may print the canonical reduced representative. -/
theorem constant_fold_mul (p : Nat) (c1 c2 : Int) :
    mul (const p c1) (const p c2) = const p (c1 * c2) := by
  show ((c1 : ZMod p) * (c2 : ZMod p)) = ((c1 * c2 : Int) : ZMod p)
  push_cast
  ring

/-- `felt.neg (felt.const c) = felt.const (-c)`.
    Registered-field execution may print the canonical reduced representative. -/
theorem constant_fold_neg (p : Nat) (c : Int) :
    neg (const p c) = const p (-c) := by
  show -((c : Int) : ZMod p) = ((-c : Int) : ZMod p)
  push_cast
  ring

/-- `felt.add x (felt.neg x) = felt.const 0`. -/
theorem add_neg_to_zero (p : Nat) (x : Felt p) :
    add x (neg x) = const p 0 := by
  show x + -x = ((0 : Int) : ZMod p)
  simp

/-- `felt.neg (felt.neg x) = x` (involution). -/
theorem neg_neg_to_self (p : Nat) (x : Felt p) :
    neg (neg x) = x := by
  show - -x = x
  simp

/-- Constant-canonicalization: `felt.add (felt.const c) x = felt.add x (felt.const c)`.
    Mirrors MLIR's convention of placing constants on the right of binary ops. -/
theorem add_const_swap (p : Nat) (x : Felt p) (c : Int) :
    add (const p c) x = add x (const p c) := by
  show ((c : Int) : ZMod p) + x = x + ((c : Int) : ZMod p)
  ring

/-! ## Tier 2 (E.5 follow-up, 2026-05-20)

  Telescoping cancellations and constant-multiplication associativity. Each
  holds in any commutative ring; no primality needed.
-/

/-- `felt.sub (felt.add x c) c = x`. -/
theorem add_sub_const_cancel (p : Nat) (x : Felt p) (c : Int) :
    sub (add x (const p c)) (const p c) = x := by
  show (x + (c : ZMod p)) - (c : ZMod p) = x
  ring

/-- `felt.add (felt.sub x c) c = x`. -/
theorem sub_add_const_cancel (p : Nat) (x : Felt p) (c : Int) :
    add (sub x (const p c)) (const p c) = x := by
  show (x - (c : ZMod p)) + (c : ZMod p) = x
  ring

/-- `felt.mul (felt.mul x c1) c2 = felt.mul x (c1 * c2)`. -/
theorem assoc_const_fold_mul (p : Nat) (x : Felt p) (c1 c2 : Int) :
    mul (mul x (const p c1)) (const p c2) = mul x (const p (c1 * c2)) := by
  show (x * (c1 : ZMod p)) * (c2 : ZMod p) = x * ((c1 * c2 : Int) : ZMod p)
  push_cast
  ring

end Veir.Data.Felt
