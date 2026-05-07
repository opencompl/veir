module

import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.Refinement
public import Veir.Data.LLVM.Int.Basic
public meta import Std.Tactic.BVDecide.Reflect
import Veir.ForLean
import Veir.Data.LLVM.Int.Simp

open Veir.Data.LLVM

namespace Veir.Data.LLVM.Int

/--
  We define a bitblastable structure `IntBv`, where the `toBitVec` fields contains a bitvector,
  the `poison` field indicates whether the value is poison,
  and `inv` preserves a proof that if the value is poison its corresponding bitvector
  value is `0#w`.
-/
@[ext]
structure IntBv (w : Nat) where
  toBitVec : BitVec w
  poison : Bool
deriving DecidableEq

def isPoison {w : Nat} (x : Int w) :=
  match _ : x with
  | .val _ => false
  | .poison => true

@[llvm_toBitVec, bv_normalize]
theorem poison_isPoison {w : Nat} : poison.isPoison (w := w) := by simp [isPoison]

@[llvm_toBitVec, bv_normalize]
theorem val_isPoison {w : Nat} {v : BitVec w} : (val v).isPoison (w := w) = false := by simp [isPoison]

@[bv_normalize, llvm_toBitVec]
theorem bool_poison (x : Int w) : (!x.isPoison = true) ↔ (¬ x.isPoison) := by simp [isPoison]

@[llvm_toBitVec, bv_normalize]
theorem val_of_not_isPoison {w : Nat} (x : Int w) (hx : x.isPoison = false) :
    ∃ v, x = val v := by
  cases x
  · case _ v => exists v
  · simp [isPoison] at hx

/-- We only allow extracting a `val v` constructor if given a non-poison hypothesis.
  This prevents coercing the poison value to a bitvector `0#w`, at the cost of
  always carrying around the hypothesis. -/
def getValue {w : Nat} (x : Int w) (h : ¬ x.isPoison) : BitVec w :=
  match x with
  | val v => v
  | poison => absurd rfl h

@[llvm_toBitVec]
theorem getValue_of_val {w : Nat} {v : BitVec w}:
    (val v).getValue (by simp [isPoison]) = v := by
  simp [getValue]

@[bv_normalize, llvm_toBitVec]
theorem isRefinedBy_toBitVec_eq (x y : Int w) :
    (x ⊑ y) ↔ (x.isPoison ∨ ((hx : ¬ x.isPoison) → (hy : ¬ y.isPoison) → x.getValue hx = y.getValue hy)) := by
  simp only [isRefinedBy, Bool.false_eq_true, Bool.not_eq_true]
  constructor
  · intros hc
    split at hc
    · grind
    · simp [llvm_toBitVec]
  · intros hc
    split
    · cases y
      · simp [llvm_toBitVec] at hc
        simp [hc]
      · /- not even sure this is correct -/
        sorry
    · simp



@[bv_normalize]
theorem toBitVec_bif {w : Nat} (b : Bool) (x y : IntBv w) :
    (bif b then x else y).toBitVec = bif b then x.toBitVec else y.toBitVec := by
  cases b <;> rfl

@[bv_normalize]
theorem poison_bif {w : Nat} (b : Bool) (x y : IntBv w) :
    (bif b then x else y).poison = bif b then x.poison else y.poison := by
  cases b <;> rfl

@[bv_normalize]
theorem eq_iff {w : Nat} {x y : IntBv w} :
    x = y ↔ x.toBitVec = y.toBitVec ∧ x.poison = y.poison :=
  IntBv.ext_iff

@[bv_normalize, llvm_toBitVec]
theorem toBitVec_ite_eq {w : Nat} (b : Prop) [Decidable b] (x y : IntBv w) :
    (if b then x else y).toBitVec = if b then x.toBitVec else y.toBitVec := by
  split <;> rfl

@[bv_normalize, llvm_toBitVec]
theorem poison_ite {w : Nat} (b : Prop) [Decidable b] (x y : IntBv w) :
    (if b then x else y).poison = if b then x.poison else y.poison := by
  split <;> rfl

attribute [llvm_toBitVec] IntPred.eval


/-! # LLVM IR operations unfolding to `toIntBv` -/

@[llvm_toBitVec]
theorem constant_isPoison {w : Nat} {v : _root_.Int} :
    (constant w v).isPoison = false := by
  simp [constant, llvm_toBitVec]

@[llvm_toBitVec]
theorem constant_getValue {w : Nat} {v : _root_.Int} :
    (constant w v).getValue  (by simp [constant_isPoison]) = BitVec.ofInt w v := by
  simp [constant, llvm_toBitVec, getValue]

@[llvm_toBitVec]
theorem add_isPoison {w : Nat} {nsw nuw : Bool} (x y : Int w) :
    (add x y nsw nuw).isPoison ↔
      (x.isPoison ∨ y.isPoison ∨
      ((hx : ¬x.isPoison) → (hy : ¬ y.isPoison) → nsw ∧ BitVec.saddOverflow (x.getValue hx) (y.getValue hy)) ∨
      ((hx : ¬x.isPoison) → (hy : ¬ y.isPoison) → nuw ∧ BitVec.uaddOverflow (x.getValue hx) (y.getValue hy))) := by
  simp only [add, pure_bind, Bool.not_eq_true]
  cases x <;> cases y <;> simp [Id.run, isPoison, llvm_toBitVec, pure]; grind

@[llvm_toBitVec]
theorem add_getValue {w : Nat} {nsw nuw : Bool} (x y : Int w) (h : ¬ (add x y nsw nuw).isPoison):
    (add x y nsw nuw).getValue h =
      x.getValue (by simp [llvm_toBitVec] at h; simp [h]) + y.getValue (by simp [llvm_toBitVec] at h; simp [h]) := by
  simp only [add, pure_bind]
  simp only [add_isPoison, Bool.not_eq_true, not_or, Classical.not_forall, not_and] at h
  cases x <;> cases y
  · simp [llvm_toBitVec, Id.run, pure, getValue]
    grind
  · simp [llvm_toBitVec, getValue] at h
  · simp [llvm_toBitVec, getValue] at h
  · simp [llvm_toBitVec, getValue] at h

@[llvm_toBitVec]
theorem sub_isPoison {w : Nat} {nsw nuw : Bool} (x y : Int w) :
    (sub x y nsw nuw).isPoison ↔
      (x.isPoison ∨ y.isPoison ∨
      ((hx : ¬x.isPoison) → (hy : ¬ y.isPoison) → nsw ∧ BitVec.ssubOverflow (x.getValue hx) (y.getValue hy)) ∨
      ((hx : ¬x.isPoison) → (hy : ¬ y.isPoison) → nuw ∧ BitVec.usubOverflow (x.getValue hx) (y.getValue hy))) := by
  simp only [sub, pure_bind, Bool.not_eq_true]
  cases x <;> cases y <;> simp [Id.run, isPoison, llvm_toBitVec, pure]; grind

/- We need the ITE to be able to prove the correctness. Unfortunately,
  it is also the reason why -/
@[llvm_toBitVec]
theorem sub_getValue {w : Nat} {nsw nuw : Bool} (x y : Int w) (h : ¬ (sub x y nsw nuw).isPoison) :
    (sub x y nsw nuw).getValue h =
      x.getValue (by simp [llvm_toBitVec] at h; simp [h]) - y.getValue (by simp [llvm_toBitVec] at h; simp [h]) := by
  simp only [sub, pure_bind]
  simp only [sub_isPoison, Bool.not_eq_true, not_or, Classical.not_forall, not_and] at h
  cases x <;> cases y
  · simp [llvm_toBitVec, Id.run, pure, getValue]
    grind
  · simp [llvm_toBitVec, getValue] at h
  · simp [llvm_toBitVec, getValue] at h
  · simp [llvm_toBitVec, getValue] at h

@[llvm_toBitVec]
theorem mul_isPoison {w : Nat} {nsw nuw : Bool} (x y : Int w) :
    (mul x y nsw nuw).isPoison ↔
      (x.isPoison ∨ y.isPoison ∨
      ((hx : ¬x.isPoison) → (hy : ¬ y.isPoison) → nsw ∧ BitVec.smulOverflow (x.getValue hx) (y.getValue hy)) ∨
      ((hx : ¬x.isPoison) → (hy : ¬ y.isPoison) → nuw ∧ BitVec.umulOverflow (x.getValue hx) (y.getValue hy))) := by
  simp only [mul, pure_bind, Bool.not_eq_true]
  cases x <;> cases y <;> simp [Id.run, isPoison, llvm_toBitVec, pure]; grind

@[llvm_toBitVec]
theorem mul_getValue {w : Nat} {nsw nuw : Bool} (x y : Int w) (h : ¬ (mul x y nsw nuw).isPoison) :
    (mul x y nsw nuw).getValue h =
      x.getValue (by simp [llvm_toBitVec] at h; simp [h]) * y.getValue (by simp [llvm_toBitVec] at h; simp [h]) := by
  simp only [mul, pure_bind]
  simp only [mul_isPoison, Bool.not_eq_true, not_or, Classical.not_forall, not_and] at h
  cases x <;> cases y
  · simp [llvm_toBitVec, Id.run, pure, getValue]
    grind
  · simp [llvm_toBitVec, getValue] at h
  · simp [llvm_toBitVec, getValue] at h
  · simp [llvm_toBitVec, getValue] at h

@[llvm_toBitVec]
theorem udiv_isPoison {w : Nat} {exact : Bool} (x y : Int w) :
    (udiv x y exact).isPoison ↔
      (x.isPoison ∨ y.isPoison ∨
      ((hx : ¬x.isPoison) → (hy : ¬ y.isPoison) → exact ∧ (x.getValue hx).umod (y.getValue hy) ≠ 0) ∨
      ((hy : ¬ y.isPoison) → (y.getValue hy) = 0)) := by
  simp only [udiv, pure_bind, Bool.not_eq_true]
  cases x <;> cases y <;> simp [Id.run, isPoison, llvm_toBitVec, pure]; grind

@[llvm_toBitVec]
theorem udiv_getValue {w : Nat} {exact : Bool}  (x y : Int w) (h : ¬ (udiv x y exact).isPoison) :
    (udiv x y exact).getValue h =
      (x.getValue (by simp [llvm_toBitVec] at h; simp [h])).udiv (y.getValue (by simp [llvm_toBitVec] at h; simp [h])) := by
  simp only [udiv, pure_bind]
  simp only [udiv_isPoison, Bool.not_eq_true, not_or, Classical.not_forall, not_and] at h
  cases x <;> cases y
  · simp [llvm_toBitVec, Id.run, pure, getValue]
    grind
  · simp [llvm_toBitVec, getValue] at h
  · simp [llvm_toBitVec, getValue] at h
  · simp [llvm_toBitVec, getValue] at h
    grind

@[llvm_toBitVec]
theorem sdiv_isPoison {w : Nat} {exact : Bool} (x y : Int w) :
    (sdiv x y exact).isPoison ↔
      (x.isPoison ∨ y.isPoison ∨
      ((hx : ¬x.isPoison) → (hy : ¬ y.isPoison) →
        ((y.getValue hy) = 0 ∨ (w ≠ 1 ∧ (x.getValue hx) = BitVec.intMin w ∧ (y.getValue hy) = -1))) ∨
      ((hx : ¬x.isPoison) → (hy : ¬ y.isPoison) → exact ∧ (x.getValue hx).smod (y.getValue hy) ≠ 0)) := by
  simp only [sdiv, BitVec.ofNat_eq_ofNat, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, bne_iff_ne,
    ne_eq, pure_bind, Bool.not_eq_true]
  cases x <;> cases y <;> simp [Id.run, isPoison, llvm_toBitVec, pure]; grind

@[llvm_toBitVec]
theorem sdiv_getValue {w : Nat} {exact : Bool}  (x y : Int w) (h : ¬ (sdiv x y exact).isPoison) :
    (sdiv x y exact).getValue h =
      (x.getValue (by simp [llvm_toBitVec] at h; simp [h])).sdiv (y.getValue (by simp [llvm_toBitVec] at h; simp [h])) := by
  simp only [sdiv, pure_bind, llvm_toBitVec]
  simp only [llvm_toBitVec] at h
  cases x <;> cases y
  · simp [llvm_toBitVec, getValue] at h
    simp [llvm_toBitVec, h, pure, Id.run]
    split
    · grind
    · split
      · grind
      · simp [llvm_toBitVec]
  · simp [llvm_toBitVec, getValue] at h
  · simp [llvm_toBitVec, getValue] at h
  · simp [llvm_toBitVec, getValue] at h

@[llvm_toBitVec]
theorem urem_isPoison {w : Nat} (x y : Int w) :
    (urem x y).isPoison ↔
      (x.isPoison ∨ y.isPoison ∨ ((hy : ¬ y.isPoison) → y.getValue hy = 0)) := by
  simp only [urem, BitVec.ofNat_eq_ofNat, beq_iff_eq, pure_bind, Bool.not_eq_true]
  cases x <;> cases y <;> simp [Id.run, isPoison, llvm_toBitVec, pure]; grind

@[llvm_toBitVec]
theorem urem_getValue {w : Nat} (x y : Int w) (h : ¬ (urem x y).isPoison) :
    (urem x y).getValue h =
      (x.getValue (by simp [llvm_toBitVec] at h; simp [h])).umod
          (y.getValue (by simp only [urem_isPoison, Bool.not_eq_true, not_or] at h; simp [h])) := by
  simp only [urem, pure_bind, llvm_toBitVec]
  simp only [llvm_toBitVec] at h
  cases x <;> cases y
  · simp [llvm_toBitVec, getValue] at h
    simp [llvm_toBitVec, h, Id.run]
  · simp [llvm_toBitVec, getValue] at h
  · simp [llvm_toBitVec, getValue] at h
  · simp [llvm_toBitVec, getValue] at h

@[llvm_toBitVec]
theorem srem_isPoison {w : Nat} (x y : Int w) :
    (srem x y).isPoison ↔
      (x.isPoison ∨ y.isPoison ∨
        ((hy : ¬ y.isPoison) → y.getValue hy = 0) ∨
        ((hx : ¬ x.isPoison) → (hy : ¬ y.isPoison) → (w ≠ 1 ∧ x.getValue hx = BitVec.intMin w ∧ y.getValue hy = -1))) := by
  simp [srem, BitVec.ofNat_eq_ofNat, beq_iff_eq, pure_bind, Bool.not_eq_true]
  cases x <;> cases y <;> simp [Id.run, isPoison, llvm_toBitVec, pure]; grind

@[llvm_toBitVec]
theorem srem_getValue {w : Nat} (x y : Int w) (h : ¬ (srem x y).isPoison) :
    (srem x y).getValue h =
      (x.getValue (by simp [llvm_toBitVec] at h; simp [h])).srem
          (y.getValue (by simp only [srem_isPoison, Bool.not_eq_true, not_or] at h; simp [h])) := by
  simp only [srem, pure_bind, llvm_toBitVec]
  simp only [llvm_toBitVec] at h
  cases x <;> cases y
  · simp [llvm_toBitVec, getValue] at h
    simp [llvm_toBitVec, h, Id.run]
    split
    · grind
    · simp [llvm_toBitVec]
  · simp [llvm_toBitVec, getValue] at h
  · simp [llvm_toBitVec, getValue] at h
  · simp [llvm_toBitVec, getValue] at h

@[llvm_toBitVec]
theorem shl_isPoison {w : Nat} {nsw nuw : Bool} (x y : Int w) :
    (shl x y nsw nuw).isPoison ↔
      (x.isPoison ∨ y.isPoison ∨
      ((hx : ¬x.isPoison) → (hy : ¬ y.isPoison) →
          nsw ∧ ((x.getValue hx) <<< (y.getValue hy)).sshiftRight' (y.getValue hy) ≠ (x.getValue hx)) ∨
      ((hx : ¬x.isPoison) → (hy : ¬ y.isPoison) →
          nuw ∧ (x.getValue hx) <<< (y.getValue hy) >>> (y.getValue hy) ≠ (x.getValue hx)) ∨
      ((hy : ¬ y.isPoison) → (y.getValue hy) ≥ w)) := by
  simp only [shl, pure_bind, Bool.not_eq_true]
  cases x <;> cases y <;> simp [Id.run, isPoison, llvm_toBitVec, pure]
  grind

@[llvm_toBitVec]
theorem shl_getValue {w : Nat} {nsw nuw : Bool} (x y : Int w) (h : ¬ (shl x y nsw nuw).isPoison) :
    (shl x y nsw nuw).getValue h =
      x.getValue (by simp [llvm_toBitVec] at h; simp [h]) <<< y.getValue (by simp [llvm_toBitVec] at h; simp [h]) := by
  simp only [shl, pure_bind]
  simp only [shl_isPoison, Bool.not_eq_true, not_or, Classical.not_forall, not_and] at h
  cases x <;> cases y
  · simp [llvm_toBitVec, getValue] at h
    simp [llvm_toBitVec, Id.run, pure, getValue]
    grind
  · simp [llvm_toBitVec, getValue] at h
  · simp [llvm_toBitVec, getValue] at h
  · simp [llvm_toBitVec, getValue] at h

@[llvm_toBitVec]
theorem lshr_isPoison {w : Nat} {exact: Bool} (x y : Int w) :
    (lshr x y exact).isPoison ↔
      (x.isPoison ∨ y.isPoison ∨
      ((hy : ¬ y.isPoison) → (y.getValue hy) ≥ w) ∨
      ((hx : ¬x.isPoison) → (hy : ¬ y.isPoison) →
          exact ∧ ((x.getValue hx) >>> (y.getValue hy)) <<< (y.getValue hy) ≠ (x.getValue hx))) := by
  simp only [lshr, pure_bind, Bool.not_eq_true]
  cases x <;> cases y <;> simp [Id.run, isPoison, llvm_toBitVec, pure]
  grind

@[llvm_toBitVec]
theorem lshr_getValue {w : Nat} {exact : Bool} (x y : Int w) (h : ¬ (lshr x y exact).isPoison) :
    (lshr x y exact).getValue h =
      x.getValue (by simp [llvm_toBitVec] at h; simp [h]) >>> y.getValue (by simp [llvm_toBitVec] at h; simp [h]) := by
  simp only [lshr, pure_bind]
  simp only [lshr_isPoison, Bool.not_eq_true, not_or, Classical.not_forall, not_and] at h
  cases x <;> cases y
  · simp [llvm_toBitVec, getValue] at h
    simp [llvm_toBitVec, Id.run, pure, getValue]
    split <;> grind
  · simp [llvm_toBitVec, getValue] at h
  · simp [llvm_toBitVec, getValue] at h
  · simp [llvm_toBitVec, getValue] at h

@[llvm_toBitVec]
theorem ashr_isPoison {w : Nat} {exact: Bool} (x y : Int w) :
    (ashr x y exact).isPoison ↔
      (x.isPoison ∨ y.isPoison ∨
      ((hy : ¬ y.isPoison) → (y.getValue hy) ≥ w) ∨
      ((hx : ¬x.isPoison) → (hy : ¬ y.isPoison) →
          exact ∧ ((x.getValue hx) >>> (y.getValue hy)) <<< (y.getValue hy) ≠ (x.getValue hx))) := by
  simp only [ashr, pure_bind, Bool.not_eq_true]
  cases x <;> cases y <;> simp [Id.run, isPoison, llvm_toBitVec, pure]
  grind

@[llvm_toBitVec]
theorem ashr_getValue {w : Nat} {exact : Bool} (x y : Int w) (h : ¬ (ashr x y exact).isPoison) :
    (ashr x y exact).getValue h =
      (x.getValue (by simp [llvm_toBitVec] at h; simp [h])).sshiftRight' (y.getValue (by simp [llvm_toBitVec] at h; simp [h])) := by
  simp only [ashr, pure_bind]
  simp only [ashr_isPoison, Bool.not_eq_true, not_or, Classical.not_forall, not_and] at h
  cases x <;> cases y
  · simp [llvm_toBitVec, getValue] at h
    simp [llvm_toBitVec, Id.run, pure, getValue]
    split <;> grind
  · simp [llvm_toBitVec, getValue] at h
  · simp [llvm_toBitVec, getValue] at h
  · simp [llvm_toBitVec, getValue] at h

@[llvm_toBitVec]
theorem and_isPoison {w : Nat} (x y : Int w) :
    (and x y ).isPoison ↔
      (x.isPoison ∨ y.isPoison ) := by
  simp only [and]
  cases x <;> cases y <;> simp [Id.run, isPoison, llvm_toBitVec]

@[llvm_toBitVec]
theorem and_getValue {w : Nat} (x y : Int w) (h : ¬ (and x y).isPoison) :
    (and x y).getValue h =
      (x.getValue (by simp [llvm_toBitVec] at h; simp [h])) &&& (y.getValue (by simp [llvm_toBitVec] at h; simp [h])) := by
  simp only [and]
  simp only [and_isPoison, Bool.not_eq_true, not_or] at h
  cases x <;> cases y
  · simp [llvm_toBitVec] at h
    simp [llvm_toBitVec, Id.run, getValue]
  · simp [llvm_toBitVec] at h
  · simp [llvm_toBitVec] at h
  · simp [llvm_toBitVec] at h

@[llvm_toBitVec]
theorem or_isPoison {w : Nat} {disjoint : Bool} (x y : Int w) :
    (or x y disjoint).isPoison ↔
      (x.isPoison ∨ y.isPoison ∨ ((hx : ¬x.isPoison) → (hy : ¬ y.isPoison) → (disjoint ∧ ((x.getValue hx) &&& (y.getValue hy) ≠ 0)))) := by
  simp only [or]
  cases x <;> cases y <;> simp [Id.run, isPoison, llvm_toBitVec, pure]
  split <;>
  simp_all
  grind

@[llvm_toBitVec]
theorem or_getValue {w : Nat} {disjoint : Bool} (x y : Int w) (h : ¬ (or x y disjoint).isPoison) :
    (or x y disjoint).getValue h =
      (x.getValue (by simp [llvm_toBitVec] at h; simp [h])) ||| (y.getValue (by simp [llvm_toBitVec] at h; simp [h])) := by
  simp only [or]
  simp only [or_isPoison, Bool.not_eq_true, not_or] at h
  cases x <;> cases y
  · simp [llvm_toBitVec] at h
    simp [llvm_toBitVec, Id.run, getValue]
    split
    simp_all
    grind
    grind
  · simp [llvm_toBitVec] at h
  · simp [llvm_toBitVec] at h
  · simp [llvm_toBitVec] at h

@[llvm_toBitVec]
theorem xor_isPoison {w : Nat} (x y : Int w) :
    (xor x y ).isPoison ↔
      (x.isPoison ∨ y.isPoison ) := by
  simp only [xor]
  cases x <;> cases y <;> simp [Id.run, isPoison, llvm_toBitVec]

@[llvm_toBitVec]
theorem xor_getValue {w : Nat} (x y : Int w) (h : ¬ (xor x y).isPoison) :
    (xor x y).getValue h =
      (x.getValue (by simp [llvm_toBitVec] at h; simp [h])) ^^^ (y.getValue (by simp [llvm_toBitVec] at h; simp [h])) := by
  simp only [xor]
  simp only [xor_isPoison, Bool.not_eq_true, not_or] at h
  cases x <;> cases y
  · simp [llvm_toBitVec] at h
    simp [llvm_toBitVec, Id.run, getValue]
  · simp [llvm_toBitVec] at h
  · simp [llvm_toBitVec] at h
  · simp [llvm_toBitVec] at h

/-! # Examples
  The following section includes examples we are using to compare across all the different implementations.
-/

/-- To make this go through, I had to make the hypothesis of non-poison `add` in `add_getValue`
    explicit, otherwise `simp` was not able to infer the hypotheses by itself.
    Overall, we have a problem with the hypotheses introduced by the rewriting of the refinement
    relation. -/
example (x y : Int 64) : (add x y) ⊑ (add y x) := by
  simp [llvm_toBitVec]
  /- `bv_decide` gets stuck with the quantifiers and does not work-/
  -- bv_decide
  sorry

example (x y : Int 64) :
    sub x (sub (constant 64 0) y) ⊑ add x y := by
  simp [llvm_toBitVec]
  /- In this case we don't even need `bv_normalize`. -/

end Int
