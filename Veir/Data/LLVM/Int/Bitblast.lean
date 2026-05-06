module

import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.Refinement
public import Veir.Data.LLVM.Int.Basic
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

@[llvm_toBitVec]
theorem poison_isPoison {w : Nat} : poison.isPoison (w := w) = true := by simp [isPoison]

@[llvm_toBitVec]
theorem val_isPoison {w : Nat} {v : BitVec w} : (val v).isPoison (w := w) = false := by simp [isPoison]

theorem val_of_not_isPoison {w : Nat} (x : Int w) (hx : x.isPoison = false) :
    ∃ v, x = val v := by
  cases x
  · case _ v => exists v
  · simp [isPoison] at hx

def getValue_old {w : Nat} (x : Int w) (hx : ¬ x.isPoison := by grind) : BitVec w :=
  match x with
  | Int.val v => v
  | Int.poison => absurd rfl hx

def getValue {w : Nat} (x : Int w)  : BitVec w :=
  match x with
  | val v => v
  | poison => 0#w

@[llvm_toBitVec]
theorem getValue_of_val {w : Nat} {v : BitVec w}:
    (val v).getValue = v := by
  simp [getValue]

@[bv_normalize, llvm_toBitVec]
theorem isRefinedBy_toBitVec_eq (x y : Int w) :
    (x ⊑ y) ↔ (x.isPoison ∨
      ((hx : ¬ x.isPoison) → (hy : ¬ y.isPoison) → (x.getValue = y.getValue))) := by
  sorry

/-! # LLVM IR operations unfolding to `toIntBv` -/

@[llvm_toBitVec]
theorem constant_isPoison {w : Nat} {v : _root_.Int} :
    (constant w v).isPoison = false := by
  simp [constant, llvm_toBitVec]

@[llvm_toBitVec]
theorem constant_getValue {w : Nat} {v : _root_.Int} :
    (constant w v).getValue = BitVec.ofInt w v := by
  simp [constant, llvm_toBitVec, getValue]

@[llvm_toBitVec]
theorem add_isPoison (x y : Int w) :
    (add x y nsw nuw).isPoison ↔
      x.isPoison ∨
      y.isPoison ∨
      ((hx : ¬ x.isPoison) → (hy : ¬ y.isPoison) → nsw ∧ BitVec.saddOverflow (x.getValue) (y.getValue)) ∨
      ((hx : ¬ x.isPoison) → (hy : ¬ y.isPoison) → nuw ∧ BitVec.uaddOverflow (x.getValue) (y.getValue)) := by
  simp [add]
  cases x <;> cases y
  · simp [llvm_toBitVec]

    sorry


  sorry

@[llvm_toBitVec]
theorem add_getValue (x y : Int w) (hadd : ¬ (add x y nsw nuw).isPoison):
    (add x y nsw nuw).getValue = x.getValue := by
  sorry

@[llvm_toBitVec]
theorem add_comm (x y : Int w) :
    (add x y nsw nuw) ⊑ (add y x nsw nuw) := by
  simp [llvm_toBitVec]
  bv_decide

@[llvm_toBitVec]
theorem sub_isPoison (x y : Int w) :
    (sub x y nsw nuw).isPoison ↔
      x.isPoison ∨
      y.isPoison ∨
      ((hx : ¬ x.isPoison) → (hy : ¬ y.isPoison) → nsw ∧ BitVec.ssubOverflow (x.getValue hx) (y.getValue hy)) ∨
      ((hx : ¬ x.isPoison) → (hy : ¬ y.isPoison) → nuw ∧ BitVec.usubOverflow (x.getValue hx) (y.getValue hy)) := by
  sorry

@[llvm_toBitVec]
theorem sub_getValue (x y : Int w) (hsub : ¬ (sub x y nsw nuw).isPoison):
    (sub x y nsw nuw).getValue hsub = x.getValue
      (by rw [sub_isPoison] at hsub; grind) + y.getValue (by rw [sub_isPoison] at hsub; grind):= by
  sorry

theorem bv_AddSub_1539 :
    ∀ (e e_1 : Int 64), sub e_1 (sub (constant 64 0) e) ⊑ add e_1 e := by
  intros x y
  simp [llvm_toBitVec]

end Int
