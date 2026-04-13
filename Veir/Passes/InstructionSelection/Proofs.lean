import Veir.Data.RISCV.Reg.Basic
import Veir.Data.LLVM.Int.Basic
import Veir.Data.Casting
import Veir.Data.Refinement
import Std.Tactic.BVDecide

/-!
  In this file we prove the correctness of the lowering patterns used in the
  instruction selection rewrites.
-/

open Veir
open Classical

/--
  Prove the correctness of the `constant` lowering pattern.

  We do not need to consider the poison case, as the semantics of `llvm_constant`
  are always concrete in the interpreter.
-/
theorem constant:
    IntIsRefinedByReg (Data.LLVM.Int.constant 64 v) (Data.RISCV.li (BitVec.ofInt 64 v)) := by
  simp [IntIsRefinedByReg, Data.LLVM.Int.constant, Data.RISCV.li]

/--
  Prove the correctness of the `add` lowering pattern.
-/
theorem add:
    IntIsRefinedByReg (Data.LLVM.Int.add x y) (Data.RISCV.add (LLVM.Int.toReg x) (LLVM.Int.toReg y)) := by
  simp only [IntIsRefinedByReg, Data.LLVM.Int.add, Bool.false_eq_true, false_and, reduceIte,
    pure_bind, Data.RISCV.add, LLVM.Int.toReg, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq]
  split
  · split
    · split
      <;> bv_decide
    · split
      · bv_decide
      · simp only [Id.run, Data.LLVM.Int.val.injEq] at *
        bv_decide
  · bv_decide
