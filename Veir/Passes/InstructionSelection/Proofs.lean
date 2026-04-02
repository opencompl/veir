import Veir.Data.RISCV.Reg.Basic
import Veir.Data.LLVM.Int.Basic
import Veir.Data.Casting
/-! In this file we prove the correctness of the instruction selection lowering patterns. -/

open Veir

/-- constant in the non-poison case -/
theorem constant_val :
    (Data.LLVM.Int.val v) = RISCV.Reg.toInt (Data.RISCV.li v) 64 := by
  rfl
