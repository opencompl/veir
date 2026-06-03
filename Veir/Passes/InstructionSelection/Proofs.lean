import Veir.Data.RISCV.Reg.Basic
import Veir.Data.LLVM.Int.Basic
import Veir.Data.LLVM.Int.Simp
import Veir.Data.LLVM.Int.Bitblast
import Veir.Data.Casting
import Veir.Data.Refinement
import Std.Tactic.BVDecide

/-!
  In this file we prove the correctness of the lowering patterns used in the
  instruction selection rewrites.
-/

namespace Veir.Data.RISCV

/--
  Prove the correctness of the `constant` lowering pattern.

  We do not need to consider the poison case, as the semantics of `llvm_constant`
  are always concrete in the interpreter.
-/
theorem constant_refinement:
    isRefinedBy (LLVM.Int.constant 64 v) (RISCV.Reg.toInt (Data.RISCV.li (BitVec.ofInt 64 v)) 64) := by
  simp [isRefinedBy, Data.LLVM.Int.constant, Data.RISCV.li, RISCV.Reg.toInt]

/--
  Prove the correctness of the `add` lowering pattern.
-/
theorem add_refinement:
    isRefinedBy (Data.LLVM.Int.add x y) (RISCV.Reg.toInt (Data.RISCV.add (LLVM.Int.toReg x) (LLVM.Int.toReg y)) 64) := by
  simp only [isRefinedBy, Data.LLVM.Int.add, Bool.false_eq_true, false_and, ↓reduceIte,
    pure_bind, RISCV.Reg.toInt, Data.RISCV.add, LLVM.Int.toReg, BitVec.truncate_eq_setWidth,
    BitVec.setWidth_eq]
  split
  · split
    · split
      <;> bv_decide
    · split
      · bv_decide
      · simp only [Id.run, Data.LLVM.Int.val.injEq] at *
        bv_decide
  · bv_decide

theorem rewrite_paper_example {x y : Data.LLVM.Int 32} :
  isRefinedBy
    (let c64 := Data.LLVM.Int.constant 64 64
    let sextx := Data.LLVM.Int.sext x 64 (by omega)
    let sexty := Data.LLVM.Int.sext y 64 (by omega)
    let mul := Data.LLVM.Int.mul sextx sexty
    let ashr := Data.LLVM.Int.ashr mul c64
    Data.LLVM.Int.trunc ashr 32 (_h := by omega))
    (RISCV.Reg.toInt (Data.RISCV.mulh (LLVM.Int.toReg x) (LLVM.Int.toReg y)) 32) := by
  simp [llvm_toBitVec]
