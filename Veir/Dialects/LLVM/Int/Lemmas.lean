module

import all Veir.Dialects.LLVM.Int.Basic

open Veir.Dialects.LLVM

namespace Veir.Dialects.LLVM.Int

/- # add -/

theorem add_assoc {w : Nat} (x y z : Int w) : x + y + z = x + (y + z) := by
  simp only [HAdd.hAdd, Add.add, add]
  cases x <;> cases y <;> cases z <;> simp [BitVec.add_assoc]

@[simp]
theorem poison_add {w : Nat} (x : Int w) : .poison + x = .poison := by
  simp only [HAdd.hAdd, Add.add, add]

@[simp]
theorem add_poison {w : Nat} (x : Int w) : x + .poison = .poison := by
  simp only [HAdd.hAdd, Add.add, add]

theorem add_comm {w : Nat} (x y : Int w) : x + y = y + x := by
  simp only [HAdd.hAdd, Add.add, add]
  cases x <;> cases y <;> simp [BitVec.add_comm]

/- # mul -/

@[simp]
theorem poison_mul {w : Nat} (x : Int w) : .poison * x = .poison := by
  simp only [HMul.hMul, Mul.mul, mul]

@[simp]
theorem mul_poison {w : Nat} (x : Int w) : x * .poison = .poison := by
  simp only [HMul.hMul, Mul.mul, mul]

theorem mul_assoc {w : Nat} (x y z : Int w) : x * y * z = x * (y * z) := by
  simp only [HMul.hMul, Mul.mul, mul]
  cases x <;> cases y <;> cases z <;> simp [BitVec.mul_assoc]

theorem mul_comm {w : Nat} (x y : Int w) : x * y = y * x := by
  simp only [HMul.hMul, Mul.mul, mul]
  cases x <;> cases y <;> simp [BitVec.mul_comm]

end Int
