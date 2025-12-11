module

import Mlir.Dialects.LLVM.Basic

open Mlir.Dialects.LLVM


/-! ### add -/

theorem add_def {w : Nat} (a b : LLVMInt w) :
    a + b = match a, b with
  | .value a, .value b => .value (a + b)
  | _, _ => .poison := by sorry

theorem add_poison {w : Nat} (a : LLVMInt w) :
    a + .poison = .poison := by
  simp [add_def]

theorem poison_add {w : Nat} (a : LLVMInt w) :
    .poison + a = .poison := by
  simp [add_def]

theorem add_comm {w : Nat} (a b : LLVMInt w) :
    a + b = b + a := by
  simp [add_def]
  cases a <;> cases b <;> simp [BitVec.add_comm]

instance : Std.Commutative (α := LLVMInt w) (· + ·) := ⟨add_comm⟩

theorem add_assoc {w : Nat} (a b c : LLVMInt w) :
    a + b + c = a + (b + c) := by
  simp [add_def]
  cases a <;> cases b <;> cases c <;> simp [BitVec.add_assoc]

instance : Std.Associative (α := LLVMInt w) (· + ·) := ⟨add_assoc⟩

/-! ### mul -/

theorem mul_def {w : Nat} (a b : LLVMInt w) :
    a * b = match a, b with
  | .value a, .value b => .value (a * b)
  | _, _ => .poison := by sorry

theorem mul_poison {w : Nat} (a : LLVMInt w) :
    a * .poison = .poison := by
  simp [mul_def]

theorem poison_mul {w : Nat} (a : LLVMInt w) :
    .poison * a = .poison := by
  simp [mul_def]

theorem mul_comm {w : Nat} (a b : LLVMInt w) :
    a * b = b * a := by
  simp [mul_def]
  cases a <;> cases b <;> simp [BitVec.mul_comm]

instance : Std.Commutative (α := LLVMInt w) (· * ·) := ⟨mul_comm⟩

theorem mul_assoc {w : Nat} (a b c : LLVMInt w) :
    a * b * c = a * (b * c) := by
  simp [mul_def]
  cases a <;> cases b <;> cases c <;> simp [BitVec.mul_assoc]

instance : Std.Associative (α := LLVMInt w) (· * ·) := ⟨mul_assoc⟩
