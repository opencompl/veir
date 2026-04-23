module

public meta import Std.Tactic.BVDecide.Reflect
import all Veir.Data.LLVM.Int.Basic
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
  inv : poison → (toBitVec = 0#w) := by simp
deriving DecidableEq

/-- An `LLVM.Int w` is converted into a structure `IntBv`, where
  the `poison` field indicates whether the `Int` is poison. -/
def toIntBv (x : Int w) : IntBv w :=
  match h : x with
  | .val v => ⟨v, false, by simp⟩
  | .poison => ⟨0#w, true, by simp⟩

/--
  We prove the injectivity of `toIntBv`.
-/
theorem Int.toIntBv.inj {w : Nat} : ∀ {x y : Int w}, x.toIntBv = y.toIntBv → x = y
  | .val v,  .val v',  h => by
    simp only [toIntBv, IntBv.mk.injEq, and_true] at h
    simp [h]
  | .poison, .poison, _ => rfl
  | .val v,  .poison, h => by
    simp [toIntBv] at h
  | .poison, .val v,  h => by
    simp [toIntBv] at h

@[llvm_toBitVec]
theorem int_inj (i1 i2 : Int w) :
    i1 = i2 ↔ i1.toIntBv = i2.toIntBv := ⟨(· ▸ rfl), Int.toIntBv.inj⟩

@[llvm_toBitVec]
theorem toIntBv_poison :
    poison.toIntBv = ⟨0#w, true, by simp⟩ := by
  simp [toIntBv]

@[llvm_toBitVec]
theorem toIntBv_val :
    (val v).toIntBv = ⟨v, false, by simp⟩ := by
  simp [toIntBv]

theorem toBitVec_zero_of_poison (x : IntBv w) :
    x.poison = true → x.toBitVec = 0#w := by
  obtain ⟨bv, poison, h⟩ := x
  exact h

/- We enable `bv_decide` to normalize `toIntBv` for values and poison. -/
attribute [bv_normalize] IntBv.ext_iff
attribute [bv_normalize] toIntBv_poison
attribute [bv_normalize] toIntBv_val
attribute [bv_normalize] toBitVec_zero_of_poison

@[llvm_toBitVec]
theorem toIntBv_constant {w : Nat} (v : _root_.Int) :
    (constant w v).toIntBv = ⟨BitVec.ofInt w v, false, by simp⟩ := by
  simp [constant, toIntBv]

@[llvm_toBitVec]
theorem toIntBv_add {w : Nat} (x y : Int w) :
    (add x y).toIntBv =
      if (x.toIntBv.poison ∨ y.toIntBv.poison) = true then ⟨0#w, true, by simp⟩
        else ⟨x.toIntBv.toBitVec + y.toIntBv.toBitVec, false, by simp⟩ := by
  simp [add, llvm_toBitVec, Id.run]
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec]

example (x y : Int 64) :
    (x.add y) = (y.add x) := by
  simp [llvm_toBitVec]
  ext1 <;> bv_decide

example (x : Int 64) :
    x.add (val 0#64) = x := by
  simp [llvm_toBitVec]
  generalize x.toIntBv = x'
  ext1 <;> bv_decide

end Int
