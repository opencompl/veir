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

/- # fold-table lemmas -/

@[simp, grind =]
theorem add_zero {w : Nat} (x : Int w) (nsw nuw : Bool) :
    add x (.val (0#w)) nsw nuw = x := by
  cases x <;> simp [add, Id.run, BitVec.saddOverflow_eq, BitVec.uaddOverflow, BitVec.isLt]

/-- Adding zero never overflows, so the carry may be refined to concrete false. -/
@[simp, grind .]
theorem uaddOverflowFlag_zero {w : Nat} (x : Int w) :
    uaddOverflowFlag x (.val (0#w)) ⊒ .val (0#1) := by
  cases x <;> simp [uaddOverflowFlag, Id.run, BitVec.uaddOverflow_eq, isRefinedBy_eq,
    BitVec.msb_eq_getLsbD_last]

end Int
