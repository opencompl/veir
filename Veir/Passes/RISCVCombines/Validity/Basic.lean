module

import all Veir.Passes.RISCVCombines.Validity.Common

/-! CTree validity proofs for the RISC-V combines: identities, shifts of booleans, redundant extensions, and immediates. -/

namespace Veir.RISCV.CTreeProofs

open Puddle
open _root_.CTree

set_option linter.unusedSimpArgs false

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Rv64.interpretOp'


theorem right_identity_zero_add_valid :
    Puddle.CTree.Pattern.Valid (right_identity_zero_add_pattern) := by
  proveCombineValid using Data.RISCV.right_identity_zero_add

theorem srl_sra_signbit_valid :
    Puddle.CTree.Pattern.Valid (srl_sra_signbitGen_pattern .srli rfl .srai 64) := by
  proveCombineValid using Data.RISCV.srl_sra_signbit

theorem srlw_sraw_signbit_valid :
    Puddle.CTree.Pattern.Valid (srl_sra_signbitGen_pattern .srliw rfl .sraiw 32) := by
  proveCombineValid using Data.RISCV.srlw_sraw_signbit

theorem drop_slli_srli_slt_valid :
    Puddle.CTree.Pattern.Valid (drop_slli_srli_boolGen_pattern .slt 2) := by
  proveCombineValid using Data.RISCV.drop_slli_srli_slt

theorem drop_slli_srli_sltu_valid :
    Puddle.CTree.Pattern.Valid (drop_slli_srli_boolGen_pattern .sltu 2) := by
  proveCombineValid using Data.RISCV.drop_slli_srli_sltu

theorem drop_slli_srli_slti_valid :
    Puddle.CTree.Pattern.Valid (drop_slli_srli_boolGen_pattern .slti 1) := by
  proveCombineValid using Data.RISCV.drop_slli_srli_slti

theorem drop_slli_srli_sltiu_valid :
    Puddle.CTree.Pattern.Valid (drop_slli_srli_boolGen_pattern .sltiu 1) := by
  proveCombineValid using Data.RISCV.drop_slli_srli_sltiu

theorem drop_slli_srli_seqz_valid :
    Puddle.CTree.Pattern.Valid (drop_slli_srli_boolGen_pattern .seqz 1) := by
  proveCombineValid using Data.RISCV.drop_slli_srli_seqz

theorem drop_slli_srli_snez_valid :
    Puddle.CTree.Pattern.Valid (drop_slli_srli_boolGen_pattern .snez 1) := by
  proveCombineValid using Data.RISCV.drop_slli_srli_snez

theorem drop_slli_srli_sltz_valid :
    Puddle.CTree.Pattern.Valid (drop_slli_srli_boolGen_pattern .sltz 1) := by
  proveCombineValid using Data.RISCV.drop_slli_srli_sltz

theorem drop_slli_srli_sgtz_valid :
    Puddle.CTree.Pattern.Valid (drop_slli_srli_boolGen_pattern .sgtz 1) := by
  proveCombineValid using Data.RISCV.drop_slli_srli_sgtz

theorem drop_andi_one_srli_valid :
    Puddle.CTree.Pattern.Valid (drop_andi_one_srli_pattern) := by
  proveCombineValid using Data.RISCV.drop_andi_one_srli

theorem zextw_zextw_valid :
    Puddle.CTree.Pattern.Valid (drop_redundant_ext_pattern .zextw) := by
  proveCombineValid using Data.RISCV.zextw_zextw

theorem sextw_sextw_valid :
    Puddle.CTree.Pattern.Valid (drop_redundant_ext_pattern .sextw) := by
  proveCombineValid using Data.RISCV.sextw_sextw

theorem zextb_zextb_valid :
    Puddle.CTree.Pattern.Valid (drop_redundant_ext_pattern .zextb) := by
  proveCombineValid using Data.RISCV.zextb_zextb

theorem zexth_zexth_valid :
    Puddle.CTree.Pattern.Valid (drop_redundant_ext_pattern .zexth) := by
  proveCombineValid using Data.RISCV.zexth_zexth

theorem sextb_sextb_valid :
    Puddle.CTree.Pattern.Valid (drop_redundant_ext_pattern .sextb) := by
  proveCombineValid using Data.RISCV.sextb_sextb

theorem sexth_sexth_valid :
    Puddle.CTree.Pattern.Valid (drop_redundant_ext_pattern .sexth) := by
  proveCombineValid using Data.RISCV.sexth_sexth

theorem zextw_zextb_valid :
    Puddle.CTree.Pattern.Valid (zextw_zextb_pattern) := by
  proveCombineValid using Data.RISCV.zextw_zextb

theorem add_li_to_addi_valid :
    Puddle.CTree.Pattern.Valid (add_li_to_addi_pattern false) := by
  proveCombineValid using Data.RISCV.add_li_to_addi

theorem add_li_to_addi_commuted_valid :
    Puddle.CTree.Pattern.Valid (add_li_to_addi_pattern true) := by
  proveCombineValid using Data.RISCV.add_li_to_addi_commuted

theorem zextw_li_low32_valid :
    Puddle.CTree.Pattern.Valid (zextw_li_low32_pattern) := by
  proveCombineValid using Data.RISCV.zextw_li_low32

theorem sextw_li_low32_valid :
    Puddle.CTree.Pattern.Valid (sextw_li_low32_pattern) := by
  proveCombineValid using Data.RISCV.sextw_li_low32

theorem zextb_li_low8_valid :
    Puddle.CTree.Pattern.Valid (ext_li_range_pattern .zextb 0 256) := by
  proveCombineValid using Data.RISCV.zextb_li_low8

theorem zexth_li_low16_valid :
    Puddle.CTree.Pattern.Valid (ext_li_range_pattern .zexth 0 65536) := by
  proveCombineValid using Data.RISCV.zexth_li_low16

theorem sextb_li_low8_valid :
    Puddle.CTree.Pattern.Valid (ext_li_range_pattern .sextb (-128) 128) := by
  proveCombineValid using Data.RISCV.sextb_li_low8

theorem sexth_li_low16_valid :
    Puddle.CTree.Pattern.Valid (ext_li_range_pattern .sexth (-32768) 32768) := by
  proveCombineValid using Data.RISCV.sexth_li_low16

/-- The created `rv64.get_register` reads `x0`, whose value is zero. -/
theorem li_zero_to_x0_valid :
    Puddle.CTree.Pattern.Valid li_zero_to_x0_pattern := by
  simp only [riscv_pattern]
  simpPuddleValid
  simpCombineSemantics
  normalizeCombineValid
  all_goals simp [TypeAttr.of, Attribute.of, liftM, monadLift, MonadLift.monadLift,
    RuntimeValue.isRefinedBy, ControlFlowAction.optionIsRefinedBy, Data.RISCV.li_zero_to_x0,
    -Attribute.registerType_eq_of]

/-- `riscv.<ext>` of `x0`, which reads as zero, is `x0`. -/
theorem zextw_x0_valid : Puddle.CTree.Pattern.Valid (ext_x0_pattern .zextw) := by
  proveCombineValid using Data.RISCV.zextw_x0

theorem sextw_x0_valid : Puddle.CTree.Pattern.Valid (ext_x0_pattern .sextw) := by
  proveCombineValid using Data.RISCV.sextw_x0

theorem zextb_x0_valid : Puddle.CTree.Pattern.Valid (ext_x0_pattern .zextb) := by
  proveCombineValid using Data.RISCV.zextb_x0

theorem zexth_x0_valid : Puddle.CTree.Pattern.Valid (ext_x0_pattern .zexth) := by
  proveCombineValid using Data.RISCV.zexth_x0

theorem sextb_x0_valid : Puddle.CTree.Pattern.Valid (ext_x0_pattern .sextb) := by
  proveCombineValid using Data.RISCV.sextb_x0

theorem sexth_x0_valid : Puddle.CTree.Pattern.Valid (ext_x0_pattern .sexth) := by
  proveCombineValid using Data.RISCV.sexth_x0

end Veir.RISCV.CTreeProofs
