module

import Veir.Interpreter.RuntimeValue.ArrayConformsSimp

open Veir Veir.RuntimeValue

/-! # Simplification of `ArrayConforms` with `simp`. -/

/-! Simple example of an `ArrayConforms` simplification. -/
example (operands : Array RuntimeValue) :
    ArrayConforms operands #[IntegerType.signless 32, IntegerType.signless 64] ↔
    ∃ x y, operands = #[.int (IntegerType.signless 32).bitwidth x,
      .int (IntegerType.signless 64).bitwidth y] := by
  simp

/-! Simplification of multiple type attributes in an array. -/
example (operands : Array RuntimeValue) (i : IntegerType) (b : LLVM.ByteType)
    (f : FloatType) (m : ModArithType) (r : RegisterType) (p : LLVM.PointerType)
    (felt : FeltType) :
    ArrayConforms operands #[.of IntegerType i, .of LLVM.ByteType b, .of FloatType f,
      .of ModArithType m, .of RegisterType r, .of LLVM.PointerType p, .of FeltType felt] ↔
    ∃ vi vb vf vm vr vp vfelt, Data.FeltSemantics.IsCanonical felt vfelt ∧
      operands = #[.int i.bitwidth vi, .byte b.bitwidth vb, .float f vf,
        .int m.modulus.type.bitwidth vm, .reg vr, .addr vp, .felt felt vfelt] := by
  simp

/-! Unknown type attributes remain unconstrained. -/
example (operands : Array RuntimeValue) (unknown : TypeAttr) (felt : FeltType)
    (i : IntegerType) :
    ArrayConforms operands #[.of FeltType felt, unknown, .of IntegerType i] ↔
    ∃ x, Data.FeltSemantics.IsCanonical felt x ∧
      ∃ v, Conforms v unknown ∧
        ∃ y, operands = #[.felt felt x, v, .int i.bitwidth y] := by
  simp

example (operands : Array RuntimeValue) : ArrayConforms operands #[] ↔ operands = #[] := by
  simp
