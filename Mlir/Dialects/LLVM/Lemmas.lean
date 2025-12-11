module

import Mlir.Dialects.LLVM.Basic

open Mlir.Dialects.LLVM

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

theorem add_assoc {w : Nat} (a b c : LLVMInt w) :
    a + b + c = a + (b + c) := by
  simp [add_def]
  cases a <;> cases b <;> cases c <;> simp [BitVec.add_assoc]
