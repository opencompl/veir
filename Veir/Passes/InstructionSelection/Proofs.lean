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

/--
  Prove the correctness of the `and` lowering pattern.
-/
theorem and_refinement{lhs rhs : LLVM.Int 64} :
    (Data.LLVM.Int.and lhs rhs) ⊒ (RISCV.Reg.toInt (Data.RISCV.and (LLVM.Int.toReg rhs) (LLVM.Int.toReg lhs)) 64) := by
  refine_bv_decide

/--
  Prove the correctness of the `ashr` lowering pattern.
-/
theorem ashr_refinement {lhs rhs : LLVM.Int 64} :
    (Data.LLVM.Int.ashr lhs rhs) ⊒ (RISCV.Reg.toInt (Data.RISCV.sra (LLVM.Int.toReg rhs) (LLVM.Int.toReg lhs)) 64) := by
  simp only [llvm_toBitVec, reg_toBitVec]
  simp only [LLVM.Int.getValue_eq_getValueD]
  simp
  intros
  rw [Nat.mod_eq_of_lt (by simp [BitVec.lt_def] at *; grind)]

/--
  Prove the correctness of the `icmp` lowering pattern with `eq`.
-/
theorem icmp_refinement_eq {lhs rhs : LLVM.Int 64} :
    (Data.LLVM.Int.icmp lhs rhs LLVM.IntPred.eq) ⊒
      (RISCV.Reg.toInt (Data.RISCV.sltiu 1#12 (Data.RISCV.xor (LLVM.Int.toReg rhs) (LLVM.Int.toReg lhs))) 1) := by
  simp only [llvm_toBitVec, reg_toBitVec]
  simp only [LLVM.Int.getValue_eq_getValueD]
  bv_decide

/--
  Prove the correctness of the `icmp` lowering pattern with `ne`.
-/
theorem icmp_refinement_ne {lhs rhs : LLVM.Int 64} :
    (Data.LLVM.Int.icmp lhs rhs LLVM.IntPred.ne) ⊒
      (RISCV.Reg.toInt (Data.RISCV.sltu (Data.RISCV.xor (LLVM.Int.toReg rhs) (LLVM.Int.toReg lhs)) (Data.RISCV.li 0#64)) 1) := by
  simp only [llvm_toBitVec, reg_toBitVec]
  simp only [LLVM.Int.getValue_eq_getValueD]
  simp [BitVec.ult_zero_false]
  bv_decide

/--
  Prove the correctness of the `icmp` lowering pattern with `slt`.
-/
theorem icmp_refinement_slt {lhs rhs : LLVM.Int 64} :
    (Data.LLVM.Int.icmp lhs rhs LLVM.IntPred.slt) ⊒
      (RISCV.Reg.toInt (Data.RISCV.slt (LLVM.Int.toReg rhs) (LLVM.Int.toReg lhs)) 1) := by
  simp only [llvm_toBitVec, reg_toBitVec]
  simp only [LLVM.Int.getValue_eq_getValueD]
  bv_decide

/--
  Prove the correctness of the `icmp` lowering pattern with `sle`.
-/
theorem icmp_refinement_sle {lhs rhs : LLVM.Int 64} :
    (Data.LLVM.Int.icmp lhs rhs LLVM.IntPred.sle) ⊒
      (RISCV.Reg.toInt (Data.RISCV.xori 1#12 (Data.RISCV.slt (LLVM.Int.toReg lhs) (LLVM.Int.toReg rhs))) 1) := by
  simp [llvm_toBitVec, reg_toBitVec]
  simp only [LLVM.Int.getValue_eq_getValueD]
  bv_decide

/--
  Prove the correctness of the `icmp` lowering pattern with `sgt`.
-/
theorem icmp_refinement_sgt {lhs rhs : LLVM.Int 64} :
    (Data.LLVM.Int.icmp lhs rhs LLVM.IntPred.sgt) ⊒
      (RISCV.Reg.toInt (Data.RISCV.slt (LLVM.Int.toReg lhs) (LLVM.Int.toReg rhs)) 1) := by
  simp [llvm_toBitVec, reg_toBitVec]
  simp only [LLVM.Int.getValue_eq_getValueD]
  bv_decide

/--
  Prove the correctness of the `icmp` lowering pattern with `sge`.
-/
theorem icmp_refinement_sge {lhs rhs : LLVM.Int 64} :
    (Data.LLVM.Int.icmp lhs rhs LLVM.IntPred.sge) ⊒
      (RISCV.Reg.toInt (Data.RISCV.xori 1#12 (Data.RISCV.slt (LLVM.Int.toReg rhs) (LLVM.Int.toReg lhs))) 1) := by
  simp [llvm_toBitVec, reg_toBitVec]
  simp only [LLVM.Int.getValue_eq_getValueD]
  bv_decide

/--
  Prove the correctness of the `icmp` lowering pattern with `ult`.
-/
theorem icmp_refinement_ult {lhs rhs : LLVM.Int 64} :
    (Data.LLVM.Int.icmp lhs rhs LLVM.IntPred.ult) ⊒
      (RISCV.Reg.toInt (Data.RISCV.sltu (LLVM.Int.toReg rhs) (LLVM.Int.toReg lhs)) 1) := by
  simp [llvm_toBitVec, reg_toBitVec]
  simp only [LLVM.Int.getValue_eq_getValueD]
  bv_decide

/--
  Prove the correctness of the `icmp` lowering pattern with `ule`.
-/
theorem icmp_refinement_ule {lhs rhs : LLVM.Int 64} :
    (Data.LLVM.Int.icmp lhs rhs LLVM.IntPred.ule) ⊒
      (RISCV.Reg.toInt (Data.RISCV.xori 1#12 (Data.RISCV.sltu (LLVM.Int.toReg lhs) (LLVM.Int.toReg rhs))) 1) := by
  simp [llvm_toBitVec, reg_toBitVec]
  simp only [LLVM.Int.getValue_eq_getValueD]
  bv_decide

/--
  Prove the correctness of the `icmp` lowering pattern with `ugt`.
-/
theorem icmp_refinement_ugt {lhs rhs : LLVM.Int 64} :
    (Data.LLVM.Int.icmp lhs rhs LLVM.IntPred.ugt) ⊒
      (RISCV.Reg.toInt ((Data.RISCV.sltu (LLVM.Int.toReg lhs) (LLVM.Int.toReg rhs))) 1) := by
  simp [llvm_toBitVec, reg_toBitVec]
  simp only [LLVM.Int.getValue_eq_getValueD]
  bv_decide

/--
  Prove the correctness of the `icmp` lowering pattern with `uge`.
-/
theorem icmp_refinement_uge {lhs rhs : LLVM.Int 64} :
    (Data.LLVM.Int.icmp lhs rhs LLVM.IntPred.uge) ⊒
      (RISCV.Reg.toInt (Data.RISCV.xori 1#12 (Data.RISCV.sltu (LLVM.Int.toReg rhs) (LLVM.Int.toReg lhs))) 1) := by
  simp [llvm_toBitVec, reg_toBitVec]
  simp only [LLVM.Int.getValue_eq_getValueD]
  bv_decide

/--
  Prove the correctness of the `or` lowering pattern.
-/
theorem or_refinement{lhs rhs : LLVM.Int 64} :
    (Data.LLVM.Int.or lhs rhs) ⊒ (RISCV.Reg.toInt (Data.RISCV.or (LLVM.Int.toReg rhs) (LLVM.Int.toReg lhs)) 64) := by
  simp only [llvm_toBitVec, reg_toBitVec]
  simp only [LLVM.Int.getValue_eq_getValueD]
  bv_decide

/--
  Prove the correctness of the `xor` lowering pattern.
-/
theorem xor_refinement{lhs rhs : LLVM.Int 64} :
    (Data.LLVM.Int.xor lhs rhs) ⊒ (RISCV.Reg.toInt (Data.RISCV.xor (LLVM.Int.toReg rhs) (LLVM.Int.toReg lhs)) 64) := by
  simp only [llvm_toBitVec, reg_toBitVec]
  simp only [LLVM.Int.getValue_eq_getValueD]
  bv_decide

/--
  Prove the correctness of the `mul` lowering pattern.
-/
theorem mul_refinement{lhs rhs : LLVM.Int 64} :
    (Data.LLVM.Int.mul lhs rhs) ⊒ (RISCV.Reg.toInt (Data.RISCV.mul (LLVM.Int.toReg rhs) (LLVM.Int.toReg lhs)) 64) := by
  simp only [llvm_toBitVec, reg_toBitVec]
  simp only [LLVM.Int.getValue_eq_getValueD]
  bv_decide

/--
  Prove the correctness of the `sdiv` lowering pattern.
-/
theorem sdiv_refinement{lhs rhs : LLVM.Int 64} :
    (Data.LLVM.Int.sdiv lhs rhs) ⊒ (RISCV.Reg.toInt (Data.RISCV.div (LLVM.Int.toReg rhs) (LLVM.Int.toReg lhs)) 64) := by
  simp only [llvm_toBitVec, reg_toBitVec]
  simp only [LLVM.Int.getValue_eq_getValueD]
  simp
  bv_decide

/--
  Prove the correctness of the `udiv` lowering pattern.
-/
theorem udiv_refinement{lhs rhs : LLVM.Int 64} :
    (Data.LLVM.Int.udiv lhs rhs) ⊒ (RISCV.Reg.toInt (Data.RISCV.divu (LLVM.Int.toReg rhs) (LLVM.Int.toReg lhs)) 64) := by
  simp only [llvm_toBitVec, reg_toBitVec]
  simp only [LLVM.Int.getValue_eq_getValueD]
  simp
  bv_decide

/--
  Prove the correctness of the `udiv` lowering pattern.
-/
theorem srem_refinement{lhs rhs : LLVM.Int 64} :
    (Data.LLVM.Int.srem lhs rhs) ⊒ (RISCV.Reg.toInt (Data.RISCV.rem (LLVM.Int.toReg rhs) (LLVM.Int.toReg lhs)) 64) := by
  simp only [llvm_toBitVec, reg_toBitVec]
  simp only [LLVM.Int.getValue_eq_getValueD]
  bv_decide

/--
  Prove the correctness of the `udiv` lowering pattern.
-/
theorem urem_refinement{lhs rhs : LLVM.Int 64} :
    (Data.LLVM.Int.urem lhs rhs) ⊒ (RISCV.Reg.toInt (Data.RISCV.remu (LLVM.Int.toReg rhs) (LLVM.Int.toReg lhs)) 64) := by
  simp only [llvm_toBitVec, reg_toBitVec]
  simp only [LLVM.Int.getValue_eq_getValueD]
  bv_decide

/--
  Prove the correctness of the `udiv` lowering pattern.
-/
theorem sub_refinement{lhs rhs : LLVM.Int 64} :
    (Data.LLVM.Int.sub lhs rhs) ⊒ (RISCV.Reg.toInt (Data.RISCV.sub (LLVM.Int.toReg rhs) (LLVM.Int.toReg lhs)) 64) := by
  simp only [llvm_toBitVec, reg_toBitVec]
  simp only [LLVM.Int.getValue_eq_getValueD]
  bv_decide
