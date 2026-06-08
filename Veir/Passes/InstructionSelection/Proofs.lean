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

@[reg_toBitVec, grind =]
theorem helper5 {i : LLVM.Int w} (h : i.isPoison = false := by grind) :
    (LLVM.Int.toReg i).val = i.getValue.zeroExtend 64 := by
  cases i <;>
  simp [llvm_toBitVec, reg_toBitVec, LLVM.Int.toReg, LLVM.Int.getValue]
  split
  simp_all

theorem BitVec.ult_one_iff_of_lt {lhs : BitVec w} (h : 0 < w) :
    (lhs.ult 1#w) = decide (lhs = 0#w) := by
  simp only [BitVec.ult_eq_decide, BitVec.toNat_ofNat, decide_eq_decide]
  rw [Nat.mod_eq_of_lt (by grind)]
  simp [← BitVec.toNat_inj]

theorem BitVec.ult_zero_false {lhs : BitVec w} :
    (0#w).ult lhs = decide (¬ lhs = 0#w) := by
  by_cases hzero : lhs = 0#w
  · simp [hzero, BitVec.ult]
  · by_cases hlt : (0#w).ult lhs
    · simp [hlt, hzero]
    · simp [BitVec.ult_eq_decide] at hlt
      simp [BitVec.ult_eq_decide, hlt, ← BitVec.toNat_inj]

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
theorem add_refinement {lhs rhs : LLVM.Int 64} :
    (Data.LLVM.Int.add lhs rhs) ⊒ (RISCV.Reg.toInt (Data.RISCV.add (LLVM.Int.toReg rhs) (LLVM.Int.toReg lhs)) 64) := by
  simp only [llvm_toBitVec, reg_toBitVec]
  simp only [LLVM.Int.getValue_eq_getValueD]
  bv_decide

/--
  Prove the correctness of the `and` lowering pattern.
-/
theorem and_refinement{lhs rhs : LLVM.Int 64} :
    (Data.LLVM.Int.and lhs rhs) ⊒ (RISCV.Reg.toInt (Data.RISCV.and (LLVM.Int.toReg rhs) (LLVM.Int.toReg lhs)) 64) := by
  simp only [llvm_toBitVec, reg_toBitVec]
  simp only [LLVM.Int.getValue_eq_getValueD]
  bv_decide

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

/--
  Prove the correctness of the `sext` lowering pattern, with input width `i8`.
-/
theorem sext_refinement_8 {lhs : LLVM.Int 8} (h : 8 < w₂) (h' : w₂ ≤ 64) :
    (Data.LLVM.Int.sext lhs w₂ h) ⊒ (RISCV.Reg.toInt (Data.RISCV.sextb (LLVM.Int.toReg lhs)) w₂) := by
  simp only [llvm_toBitVec, reg_toBitVec]
  simp only [LLVM.Int.getValue_eq_getValueD]
  simp
  intro h2
  simp [LLVM.Int.getValueD]
  split
  · simp [LLVM.Int.isPoison] at h2
  · ext k hk
    simp [BitVec.getLsbD_signExtend, BitVec.getElem_signExtend]
    split
    · simp [show k < 64 by omega, show k ≤ 7 by omega, ← BitVec.getLsbD_eq_getElem]
    · simp [show k < 64 by omega]
      bv_decide

/--
  Prove the correctness of the `sext` lowering pattern, with input width `i16`.
-/
theorem sext_refinement_16 {lhs : LLVM.Int 16} (h : 16 < w₂) (h' : w₂ ≤ 64) :
    (Data.LLVM.Int.sext lhs w₂ h) ⊒ (RISCV.Reg.toInt (Data.RISCV.sexth (LLVM.Int.toReg lhs)) w₂) := by
  simp only [llvm_toBitVec, reg_toBitVec]
  simp only [LLVM.Int.getValue_eq_getValueD]
  simp
  intro h2
  simp [LLVM.Int.getValueD]
  split
  · simp [LLVM.Int.isPoison] at h2
  · ext k hk
    simp [BitVec.getLsbD_signExtend, BitVec.getElem_signExtend]
    split
    · simp [show k < 64 by omega, show k ≤ 15 by omega, ← BitVec.getLsbD_eq_getElem]
    · simp [show k < 64 by omega]
      bv_decide

/--
  Prove the correctness of the `sext` lowering pattern, with input width `i32`.
-/
theorem sext_refinement_32 {lhs : LLVM.Int 32} (h : 32 < w₂) (h' : w₂ ≤ 64) :
    (Data.LLVM.Int.sext lhs w₂ h) ⊒ (RISCV.Reg.toInt (Data.RISCV.sextw (LLVM.Int.toReg lhs)) w₂) := by
  simp only [llvm_toBitVec, reg_toBitVec]
  simp only [LLVM.Int.getValue_eq_getValueD]
  simp
  intro h2
  simp [LLVM.Int.getValueD]
  split
  · simp [LLVM.Int.isPoison] at h2
  · ext k hk
    simp [BitVec.getLsbD_signExtend, BitVec.getElem_signExtend]
    split
    · simp [show k < 64 by omega,  ← BitVec.getLsbD_eq_getElem]
    · simp [show k < 64 by omega]

/--
  Prove the correctness of the `sext` lowering pattern, with input width different than `i8/i16/i32`.
-/
theorem sext_refinement {lhs : LLVM.Int w₁} (h : w₁ < w₂) (h' : w₂ ≤ 64) (h'' : w₁ ≠ 8 ∧ w₁ ≠ 16 ∧ w₁ ≠ 32) :
    (Data.LLVM.Int.sext lhs w₂ h) ⊒
      (RISCV.Reg.toInt (Data.RISCV.srai (64 - w₁) (Data.RISCV.slli (64 - w₁) (LLVM.Int.toReg lhs))) w₂) := by
  simp only [llvm_toBitVec, reg_toBitVec]
  simp only [LLVM.Int.getValue_eq_getValueD]
  simp
  by_cases hw₁ : w₁ = 0
  · subst hw₁
    simp
    sorry
  intro h2
  simp [LLVM.Int.getValueD]
  split
  · simp [LLVM.Int.isPoison] at h2
  · ext k hk
    simp [← BitVec.getLsbD_eq_getElem, hk]
    rw [Nat.mod_eq_of_lt (by rw [Nat.mod_eq_of_lt (by grind)]; grind)]
    rw [Nat.mod_eq_of_lt (by grind)]

    sorry
