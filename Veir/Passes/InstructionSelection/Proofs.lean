import Veir.Data.RISCV.Reg.Basic
import Veir.Data.RISCV.Reg.Lemmas
import Veir.Data.LLVM.Int.Basic
import Veir.Data.LLVM.Int.Simp
import Veir.Data.LLVM.Int.Lemmas
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
  A tactic to unfold the semantics of operations on `LLVM.Int` and on `RISCV.Reg` to
  bitvectors, such that `bv_decide` can prove the correctness of the refinement relation
  over instruction selection patterns.
-/
macro "refine_bv_decide" : tactic =>
  `(tactic| ((try simp only [llvm_toBitVec, reg_toBitVec]; try simp [LLVM.Int.getValue_eq_getValueD]; try bv_decide)))


/--
  Prove the correctness of the `constant` lowering pattern.

  We do not need to consider the poison case, as the semantics of `llvm_constant`
  are always concrete in the interpreter.
-/
theorem constant_refinement {v : Int}:
    (LLVM.Int.constant 64 v) ⊒ (RISCV.Reg.toInt (Data.RISCV.li (BitVec.ofInt 64 v)) 64) := by
  refine_bv_decide

/--
  Prove the correctness of the `add` lowering pattern.
-/
theorem add_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.add x y) ⊒
      (RISCV.Reg.toInt (Data.RISCV.add (LLVM.Int.toReg x) (LLVM.Int.toReg y)) 64) := by
  refine_bv_decide
