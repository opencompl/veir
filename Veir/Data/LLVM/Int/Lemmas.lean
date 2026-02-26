module

import all Veir.Data.LLVM.Int.Basic
import Veir.ForLean

open Veir.Data.LLVM

namespace Veir.Data.LLVM.Int

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
  simp only [HMul.hMul, Mul.mul, mul, Id.run]

@[simp]
theorem mul_poison {w : Nat} (x : Int w) : x * .poison = .poison := by
  simp only [HMul.hMul, Mul.mul, mul, Id.run]
  grind

theorem mul_assoc {w : Nat} (x y z : Int w) : x * y * z = x * (y * z) := by
  simp only [HMul.hMul, Mul.mul, mul, Id.run]
  cases x <;> cases y <;> cases z <;> simp [BitVec.mul_assoc]

@[grind =]
theorem mul_comm {w : Nat} (x y : Int w) : x.mul y nsw nuw = y.mul x nsw nuw := by
  simp only [Id.run, Veir.Data.LLVM.Int.mul]
  cases x <;> cases y <;> simp [BitVec.mul_comm, BitVec.smulOverflow_comm, BitVec.umulOverflow_comm]

end Int
