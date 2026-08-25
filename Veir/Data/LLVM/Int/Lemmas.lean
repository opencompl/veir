module

public import Veir.Data.LLVM.Int.Basic
public import Veir.Data.Refinement
import all Veir.Data.LLVM.Int.Basic
import Veir.ForLean

open Veir.Data.LLVM

public section

namespace Veir.Data.LLVM.Int

/- # add -/

@[simp, grind =]
theorem poison_add {w : Nat} (x : Int w) : add poison x = poison := by
  simp only [add, Id.run]

@[simp, grind =]
theorem add_poison {w : Nat} (x : Int w) : add x poison = poison := by
  simp only [add, Id.run]
  grind

@[grind =]
theorem add_assoc {w : Nat} (x y z : Int w) :
    add (add x y) z = add x (add y z) := by
  simp only [add, Id.run]
  cases x <;> cases y <;> cases z <;> simp [BitVec.add_assoc]

@[grind =]
theorem add_comm {w : Nat} (x y : Int w) : add x y = add y x := by
  simp only [add]
  cases x <;> cases y <;> simp [BitVec.add_comm]

/-- Adding zero never wraps, so the result is unchanged even when overflow flags are set. -/
theorem add_zero {w : Nat} (x : Int w) (nsw nuw : Bool) :
    add x (constant w 0) nsw nuw = x := by
  cases x with
  | poison => rfl
  | val x =>
    have hs : BitVec.saddOverflow x (BitVec.ofInt w 0) = false := by
      have hupper := @BitVec.toInt_lt w x
      have hlower := BitVec.le_toInt x
      simp [BitVec.saddOverflow]
      omega
    have hu : BitVec.uaddOverflow x (BitVec.ofInt w 0) = false := by
      simp [BitVec.uaddOverflow]
      exact x.isLt
    simp only [add, constant, Id.run]
    rw [hs, hu]
    simp

/- # sub -/

/-- Subtracting zero never wraps, so the result is unchanged even when overflow flags are set. -/
theorem sub_zero {w : Nat} (x : Int w) (nsw nuw : Bool) :
    sub x (constant w 0) nsw nuw = x := by
  cases x with
  | poison => rfl
  | val x =>
    have hs : BitVec.ssubOverflow x (BitVec.ofInt w 0) = false := by
      have hupper := @BitVec.toInt_lt w x
      have hlower := BitVec.le_toInt x
      simp [BitVec.ssubOverflow]
      omega
    have hu : BitVec.usubOverflow x (BitVec.ofInt w 0) = false := by
      simp [BitVec.usubOverflow]
    simp only [sub, constant, Id.run]
    rw [hs, hu]
    simp

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

/-- Multiplication by one refines to the operand for every width and overflow-flag setting.

For `i1` with `nsw`, multiplying the signed value `-1` by `-1` produces poison; that poison
still refines the unchanged operand, which is exactly the direction required by rewrites. -/
theorem mul_one_refines {w : Nat} (x : Int w) (nsw nuw : Bool) :
    mul x (constant w 1) nsw nuw ⊒ x := by
  cases x with
  | poison => exact isRefinedBy_refl _
  | val x =>
    simp only [mul, constant, Id.run]
    split
    · rw [isRefinedBy_eq]
      trivial
    · split
      · rw [isRefinedBy_eq]
        trivial
      · rw [isRefinedBy_eq]
        simp

end Int
