import Veir.Data.RISCV.Reg.Basic
import Veir.Data.RISCV.Reg.Lemmas
import Veir.Data.RISCV.Reg.Simp
import Veir.Data.LLVM.Int.Basic
import Veir.Data.LLVM.Int.Bitblast
import Veir.Data.LLVM.Int.Simp
import Veir.Data.LLVM.Int.Simp
import Veir.Data.Casting
import Veir.Data.Refinement
import Std.Tactic.BVDecide

/-!
  In this file we prove the correctness of the lowering patterns used in the
  instruction selection rewrites.
-/

namespace Veir.Data.RISCV

@[reg_toBitVec, grind =]
theorem helper1 {r : RISCV.Reg} :
    RISCV.Reg.toInt r 64 = (.val r.val) := by
  simp [RISCV.Reg.toInt]

@[reg_toBitVec, grind =]
theorem helper3 {r : RISCV.Reg} :
    (RISCV.Reg.toInt r w).isPoison = false := by
  simp [RISCV.Reg.toInt, LLVM.Int.isPoison]

@[reg_toBitVec, grind =]
theorem helper4 {r : RISCV.Reg} :
    (RISCV.Reg.toInt r w).getValue = r.val.zeroExtend w := by
  simp [llvm_toBitVec, reg_toBitVec, RISCV.Reg.toInt]

@[reg_toBitVec, grind =]
theorem helper2 {i : LLVM.Int w} :
    (LLVM.Int.toReg i).val = i.getValueD.zeroExtend 64 := by
  cases i <;> simp [llvm_toBitVec, reg_toBitVec, LLVM.Int.toReg, LLVM.Int.getValueD]

/--
  Prove the correctness of the `constant` lowering pattern.

  We do not need to consider the poison case, as the semantics of `llvm_constant`
  are always concrete in the interpreter.
-/
theorem constant_refinement:
    (LLVM.Int.constant 64 v) ⊒ (RISCV.Reg.toInt (Data.RISCV.li (BitVec.ofInt 64 v)) 64) := by
  simp [llvm_toBitVec, reg_toBitVec]

/--
  Prove the correctness of the `add` lowering pattern.
-/
theorem add_refinement:
    (Data.LLVM.Int.add x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.add (LLVM.Int.toReg x) (LLVM.Int.toReg y)) 64) := by
  simp [llvm_toBitVec, reg_toBitVec]
  simp only [LLVM.Int.getValue_eq_getValueD]
  intros

  bv_decide

/--
  Prove the correctness of the `and` lowering pattern.
-/
theorem and_refinement:
    (Data.LLVM.Int.and x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.and (LLVM.Int.toReg x) (LLVM.Int.toReg y)) 64) := by
  simp [llvm_toBitVec, reg_toBitVec]
  simp only [LLVM.Int.getValue_eq_getValueD]
  bv_decide

/--
  Prove the correctness of the `ashr` lowering pattern.
-/
theorem ashr_refinement:
    (Data.LLVM.Int.ashr x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.sra (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64) := by
  simp [llvm_toBitVec, reg_toBitVec]
  simp only [LLVM.Int.getValue_eq_getValueD]
  intros h1 h2
  rw [Nat.mod_eq_of_lt (by
      cases y <;> simp [h1, LLVM.Int.getValueD] at *;
      exact Nat.lt_of_succ_le h2)]

/--
  Prove the correctness of the `icmp` lowering pattern with `eq`.
-/
theorem icmp_refinement:
    (Data.LLVM.Int.icmp x y LLVM.IntPred.eq) ⊒
      (RISCV.Reg.toInt (Data.RISCV.sltiu 1#12 (Data.RISCV.xor (LLVM.Int.toReg y) (LLVM.Int.toReg x))) 1) := by
  simp [llvm_toBitVec, reg_toBitVec]

  sorry
