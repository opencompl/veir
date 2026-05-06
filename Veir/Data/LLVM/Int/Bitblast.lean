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

@[llvm_toBitVec]
theorem poison_isPoison {w : Nat} : poison.isPoison (w := w) := by simp [isPoison]

@[llvm_toBitVec]
theorem val_isPoison {w : Nat} {v : BitVec w} : (val v).isPoison (w := w) = false := by simp [isPoison]

@[bv_normalize, llvm_toBitVec]
theorem bool_poison (x : Int w) : (!x.isPoison = true) ↔ (¬ x.isPoison) := by simp [isPoison]

theorem val_of_not_isPoison {w : Nat} (x : Int w) (hx : x.isPoison = false) :
    ∃ v, x = val v := by
  cases x
  · case _ v => exists v
  · simp [isPoison] at hx

@[llvm_toBitVec]
theorem poison_ite_eq {w : Nat} (x y : Int w) (z : BitVec w) :
  (if x.isPoison = true ∨ y.isPoison = true then
      ({ toBitVec := 0#w, poison := true} : IntBv w) else
      ({ toBitVec := z, poison := false,} : IntBv w)).poison =
      (x.isPoison ∨ y.isPoison) := by
  split
  · case _ h =>  simp [h]
  · case _ h => simpa using h

def getValue {w : Nat} (x : Int w) : BitVec w :=
  match x with
  | val v => v
  | poison => 0#w

@[llvm_toBitVec]
theorem getValue_of_val {w : Nat} {v : BitVec w}:
    (val v).getValue = v := by
  simp [getValue]

@[bv_normalize, llvm_toBitVec]
theorem isRefinedBy_toBitVec_eq (x y : Int w) :
    (x ⊑ y) ↔ (x.isPoison ∨ (¬ y.isPoison ∧ x.getValue = y.getValue)) := by
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
      · simp [llvm_toBitVec] at hc
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
    (constant w v).getValue = BitVec.ofInt w v := by
  simp [constant, llvm_toBitVec, getValue]

@[llvm_toBitVec]
theorem add_isPoison (x y : Int w) :
    (add x y nsw nuw).isPoison ↔
      (x.isPoison ∨ y.isPoison ∨
      (nsw ∧ BitVec.saddOverflow x.getValue y.getValue) ∨
      (nuw ∧ BitVec.uaddOverflow x.getValue y.getValue)) := by
  simp [llvm_toBitVec, add]
  cases x <;> cases y <;> simp [Id.run, isPoison, llvm_toBitVec, pure]; grind

@[llvm_toBitVec]
theorem add_getValue (x y : Int w) :
    (add x y nsw nuw).getValue = if ¬ (add x y nsw nuw).isPoison then x.getValue + y.getValue else 0#w := by
  sorry

@[llvm_toBitVec]
theorem sub_isPoison (x y : Int w) :
    (sub x y nsw nuw).isPoison ↔
      (x.isPoison ∨ y.isPoison ∨
      (nsw ∧ BitVec.ssubOverflow x.getValue y.getValue) ∨
      (nuw ∧ BitVec.usubOverflow x.getValue y.getValue)) := by
  sorry

@[llvm_toBitVec]
theorem sub_getValue (x y : Int w) :
    (sub x y nsw nuw).getValue = x.getValue - y.getValue := by
  sorry

/-! # Examples
  The following section includes examples we are using to compare across all the different implementations.
-/

/-- to make this go through, I had to make the hypothesis of non-poison `add` in `add_getValue`
    explicit, otherwise `simp` was not able to infer the hypotheses by itself. -/
example (x y : Int 64) : (add x y) ⊑ (add y x) := by
  simp [llvm_toBitVec]
  bv_decide

example (x y : Int 64) :
    sub x (sub (constant 64 0) y) ⊑ add x y := by
  simp [llvm_toBitVec]
  bv_normalize

end Int
