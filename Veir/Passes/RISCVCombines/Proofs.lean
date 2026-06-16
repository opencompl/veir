import Veir.Data.RISCV.Reg.Basic
import Veir.Data.RISCV.Reg.Lemmas

/-!
  In this file we prove the correctness of the RISCV combines.
-/

namespace Veir.Data.RISCV


/--
  Prove the correctness of the `right_identity_zero_add` combine.
-/
theorem right_identity_zero_add:
    (RISCV.add lhs (Data.RISCV.li (BitVec.ofInt 64 0))) = lhs := by
  simp [reg_toBitVec]

/--
  Soundness of:
  `riscv.slt rs1 (riscv.li imm)` -> `riscv.slti rs1 imm`

  This is stated directly over the RISCV register interpreter semantics. The
  rewrite is valid when the original `li` value is the 64-bit sign extension of
  the 12-bit immediate used by `slti`.
-/
theorem fold_slt_li_to_slti_sound (rs1 : Reg) (imm : BitVec 12) :
    slt (li (imm.signExtend 64)) rs1 = slti imm rs1 := by
  rw [val_inj]
  simp only [val_slt, val_slti, val_li]

/--
  Soundness of:
  `riscv.sltu rs1 (riscv.li imm)` -> `riscv.sltiu rs1 imm`

  As in the ISA semantics for `sltiu`, the immediate is sign-extended before the
  unsigned comparison.
-/
theorem fold_sltu_li_to_sltiu_sound (rs1 : Reg) (imm : BitVec 12) :
    sltu (li (imm.signExtend 64)) rs1 = sltiu imm rs1 := by
  rw [val_inj]
  simp only [val_sltu, val_sltiu, val_li]
