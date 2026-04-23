module

import all Veir.Data.LLVM.Int.Basic
import Veir.ForLean
import Veir.Data.LLVM.Int.Simp

open Veir.Data.LLVM

namespace Veir.Data.LLVM.Int

@[ext]
structure IntBv (w : Nat) where
  toBitVec : BitVec w
  poison : Bool
deriving Inhabited, Repr, DecidableEq

/-- An `LLVM.Int w` is converted into a structure `IntBv`, where
  the `poison` field indicates whether the `Int` is poison. -/
def toIntBv (x : Int w) : IntBv w :=
  match x with
  | .val v => ⟨v, false⟩
  | .poison => ⟨0#w, true⟩

attribute [bv_normalize] IntBv.ext_iff

@[llvm_toBitVec]
theorem toIntBv_poison :
    poison.toIntBv = ⟨0#w, true⟩ := by
  simp [toIntBv]


@[llvm_toBitVec]
theorem toIntBv_val :
    (val v).toIntBv = ⟨v, false⟩ := by
  simp [toIntBv]

attribute [bv_normalize] toIntBv_poison
attribute [bv_normalize] toIntBv_val

theorem BitVec.ne_iff_exists {x y : BitVec w} :
    x ≠ y ↔ ∃ i, x.getLsbD i ≠ y.getLsbD i := by
  constructor
  · intro h
    refine Nat.exists_testBit_ne_of_ne ?_
    simp [← BitVec.toNat_inj] at h
    simp [h]
  · intro h
    obtain ⟨i, hi⟩ := h
    simp
    exact Ne.symm fun a => hi (congrFun (congrArg BitVec.getLsbD (id (Eq.symm a))) i)

theorem BitVec.append_eq_iff {x y : BitVec w} {z : BitVec v} :
    x ++ z = y ++ z ↔ x = y := by
  constructor
  · intro h
    exact (BitVec.append_left_inj z).mp h
  · intro h
    exact (BitVec.append_left_inj z).mpr h

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

/- # add -/

@[llvm_toBitVec]
theorem constant_val {w : Nat} (v : _root_.Int) :
    (constant w v).toIntBv = ⟨BitVec.ofInt w v, false⟩ := by
  simp [constant, toIntBv]

theorem poison_of_forall (h : ∀ (y' : BitVec w), y = val y' → False) :
    y = poison := by
  rcases y
  · case _ v =>
    specialize h v
    simp at h
  · rfl

@[grind =, llvm_toBitVec]
theorem poison_add {w : Nat} (x : Int w) : add poison x = poison := by
  simp only [add, Id.run]

@[grind =, llvm_toBitVec]
theorem add_poison {w : Nat} (x : Int w) : add x poison = poison := by
  simp only [add, Id.run]
  grind

@[llvm_toBitVec]
theorem add_val {w : Nat} {v v' : BitVec w} : add (val v) (val v') = val (v + v') := by
  simp only [add, Id.run]
  grind

@[llvm_toBitVec]
theorem add_int {w : Nat} (x y : Int w) :
    (add x y).toIntBv =
      if x.toIntBv.poison ∨ y.toIntBv.poison then ⟨0#w, true⟩
        else ⟨x.toIntBv.toBitVec + y.toIntBv.toBitVec, false⟩ := by
  simp [add, llvm_toBitVec, Id.run]
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec]

@[grind =]
theorem add_assoc {w : Nat} (x y z : Int w) :
    add (add x y) z = add x (add y z) := by
  simp only [add, Id.run]
  cases x <;> cases y <;> cases z <;> simp [BitVec.add_assoc]

@[grind =]
theorem add_comm {w : Nat} (x y : Int w) : add x y = add y x := by
  simp only [add]
  cases x <;> cases y <;> simp [BitVec.add_comm]

/- # mul -/

@[simp, grind =]
theorem poison_mul {w : Nat} (x : Int w) : mul poison x = poison := by
  simp only [mul, Id.run]

@[simp, grind =]
theorem mul_poison {w : Nat} (x : Int w) : mul x poison = poison := by
  simp only [mul, Id.run]
  grind

@[grind =]
theorem mul_assoc {w : Nat} (x y z : Int w) :
    mul x (mul y z) = mul (mul x y) z := by
  simp only [HMul.hMul, Mul.mul, mul, Id.run]
  cases x <;> cases y <;> cases z <;> simp [BitVec.mul_assoc]

@[grind =]
theorem mul_comm {w : Nat} {nsw nuw : Bool} (x y : Int w) :
    mul x y nsw nuw = mul y x nsw nuw := by
  simp only [Id.run, Veir.Data.LLVM.Int.mul]
  cases x <;> cases y <;>
  simp [BitVec.mul_comm, BitVec.smulOverflow_comm, BitVec.umulOverflow_comm]

example (x y : Int 64) :
    x.add y = y.add x := by
  simp [llvm_toBitVec]
  cases_bv_decide (Int _)


example (x : Int 64) :
    x.add (val 0#64) = x := by
  simp [llvm_toBitVec]
  cases_bv_decide (Int _)

end Int
