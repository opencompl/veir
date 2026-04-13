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
