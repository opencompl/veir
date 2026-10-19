import Veir.Dialects.Arith.Puddle

namespace Veir.ArithCanonicalize.ExtendedSupport
open Veir Veir.Data Veir.Puddle

theorem addui_extended_iff {s t : IntegerType.Signedness} (w : Nat)
    (x y : LLVM.Int w) (v0 v1 : RuntimeValue) :
    InterpretsTo (.arith .addui_extended) ()
      #[IntegerType.mk w s, IntegerType.mk 1 t]
      #[.int w x, .int w y] #[v0, v1] ↔
      v0 = .int w (LLVM.Int.add x y) ∧
      v1 = .int 1 (LLVM.Int.uaddOverflowFlag x y) := by
  simp [InterpretsTo, interpretOp', Arith.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    have hh := h .empty
    grind
  · rintro ⟨rfl, rfl⟩
    constructor
    · grind
    · intro memory
      exact ⟨rfl, rfl⟩

theorem subui_extended_iff {s t : IntegerType.Signedness} (w : Nat)
    (x y : LLVM.Int w) (v0 v1 : RuntimeValue) :
    InterpretsTo (.arith .subui_extended) ()
      #[IntegerType.mk w s, IntegerType.mk 1 t]
      #[.int w x, .int w y] #[v0, v1] ↔
      v0 = .int w (LLVM.Int.sub x y) ∧
      v1 = .int 1 (LLVM.Int.usubOverflowFlag x y) := by
  simp [InterpretsTo, interpretOp', Arith.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    have hh := h .empty
    grind
  · rintro ⟨rfl, rfl⟩
    constructor
    · grind
    · intro memory
      exact ⟨rfl, rfl⟩

theorem mulsi_extended_iff {s t : IntegerType.Signedness} (w : Nat)
    (x y : LLVM.Int w) (v0 v1 : RuntimeValue) :
    InterpretsTo (.arith .mulsi_extended) ()
      #[IntegerType.mk w s, IntegerType.mk w t]
      #[.int w x, .int w y] #[v0, v1] ↔
      v0 = .int w (LLVM.Int.mul x y) ∧
      v1 = .int w (LLVM.Int.smulHigh x y) := by
  simp [InterpretsTo, interpretOp', Arith.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    have hh := h .empty
    grind
  · rintro ⟨rfl, rfl⟩
    constructor
    · grind
    · intro memory
      exact ⟨rfl, rfl⟩

theorem mului_extended_iff {s t : IntegerType.Signedness} (w : Nat)
    (x y : LLVM.Int w) (v0 v1 : RuntimeValue) :
    InterpretsTo (.arith .mului_extended) ()
      #[IntegerType.mk w s, IntegerType.mk w t]
      #[.int w x, .int w y] #[v0, v1] ↔
      v0 = .int w (LLVM.Int.mul x y) ∧
      v1 = .int w (LLVM.Int.umulHigh x y) := by
  simp [InterpretsTo, interpretOp', Arith.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    have hh := h .empty
    grind
  · rintro ⟨rfl, rfl⟩
    constructor
    · grind
    · intro memory
      exact ⟨rfl, rfl⟩

end Veir.ArithCanonicalize.ExtendedSupport
