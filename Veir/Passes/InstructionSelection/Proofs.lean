import Veir.Data.RISCV.Reg.Basic
import Veir.Data.LLVM.Int.Basic
import Veir.Data.Casting
import Std.Tactic.BVDecide

/-!
  In this file we prove the correctness of the lowering patterns used in the
  instruction selection rewrites.
-/

open Veir

/--
  Prove the correctness of the `constant` lowering pattern.

  We do not need to consider the poison case, as the semantics of `llvm_constant`
  are always concrete in the interpreter.
-/
theorem constant_val (h : v = BitVec.ofInt 64 val) :
    (Data.LLVM.Int.val v) = RISCV.Reg.toInt (Data.RISCV.li v) 64 := by
  simp [h, Data.RISCV.li, RISCV.Reg.toInt]
