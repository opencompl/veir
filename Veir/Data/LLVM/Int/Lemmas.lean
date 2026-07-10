module

public import Veir.Data.LLVM.Int.Basic
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

/- # add / and / or / xor commutativity with flags -/

/-- Commutativity of `add`, including its overflow flags: `x + y` overflows (signed or unsigned)
    exactly when `y + x` does, so the poison behaviour is symmetric and `nsw`/`nuw` pass through
    unchanged. Used by the `commute_const_add` combine. -/
@[grind =]
theorem add_comm_flags {w : Nat} {nsw nuw : Bool} (x y : Int w) :
    add x y nsw nuw = add y x nsw nuw := by
  simp only [add, Id.run]
  cases x <;> cases y <;>
    simp [BitVec.add_comm, BitVec.saddOverflow_comm, BitVec.uaddOverflow_comm]

/-- Commutativity of `and`. Used by the `commute_const_and` combine. -/
@[grind =]
theorem and_comm {w : Nat} (x y : Int w) : and x y = and y x := by
  simp only [and, Id.run]
  cases x <;> cases y <;> simp [BitVec.and_comm]

/-- Commutativity of `or`, including its `disjoint` flag (the disjointness poison condition
    `x &&& y ≠ 0` is symmetric). Used by the `commute_const_or` combine. -/
@[grind =]
theorem or_comm {w : Nat} {disjoint : Bool} (x y : Int w) :
    or x y disjoint = or y x disjoint := by
  simp only [or, Id.run]
  cases x <;> cases y <;> simp [BitVec.or_comm, BitVec.and_comm]

/-- Commutativity of `xor`. Used by the `commute_const_xor` combine. -/
@[grind =]
theorem xor_comm {w : Nat} (x y : Int w) : xor x y = xor y x := by
  simp only [xor, Id.run]
  cases x <;> cases y <;> simp [BitVec.xor_comm]

end Int
