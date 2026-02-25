module

import all Veir.Data.LLVM.Int.Basic

open Veir.Data.LLVM

namespace Veir.Data.LLVM.Int

/- # add -/

theorem add_assoc {w : Nat} (x y z : Int w) : x + y + z = x + (y + z) := by
  simp only [HAdd.hAdd, Add.add, add, Id.run]
  cases x <;> cases y <;> cases z <;> grind

@[simp]
theorem poison_add {w : Nat} (x : Int w) : .poison + x = .poison := by
  simp only [HAdd.hAdd, Add.add, add, Id.run]

@[simp]
theorem add_poison {w : Nat} (x : Int w) : x + .poison = .poison := by
  simp only [HAdd.hAdd, Add.add, add, Id.run]
  grind

theorem add_comm {w : Nat} (x y : Int w) : x + y = y + x := by
  simp only [HAdd.hAdd, Add.add, add]
  grind

/- # mul -/

@[simp]
theorem poison_mul {w : Nat} (x : Int w) : .poison * x = .poison := by
  simp only [HMul.hMul, Mul.mul, mul, Id.run]

@[simp]
theorem mul_poison {w : Nat} (x : Int w) : x * .poison = .poison := by
  simp only [HMul.hMul, Mul.mul, mul, Id.run]
  grind

theorem mul_assoc {w : Nat} (x y z : Int w) : x * y * z = x * (y * z) := by
  simp only [HMul.hMul, Mul.mul, mul, Id.run]
  cases x <;> cases y <;> cases z <;> simp [BitVec.mul_assoc]

theorem mul_comm {w : Nat} (x y : Int w) : x * y = y * x := by
  simp only [HMul.hMul, Mul.mul, mul]
  cases x <;> cases y <;> simp [BitVec.mul_comm]

end Int
