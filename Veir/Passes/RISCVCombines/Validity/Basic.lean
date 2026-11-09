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

attribute [local implicit_reducible] TypeAttr Veir._propertiesOf Riscv.propertiesOf

theorem right_identity_zero_add_valid :
    Puddle.CTree.Pattern.Valid (right_identity_zero_add_pattern) := by
  unfold right_identity_zero_add_pattern
  proveCombineValid

theorem srl_sra_signbit_valid :
    Puddle.CTree.Pattern.Valid (srl_sra_signbitGen_pattern .srli rfl .srai 64) := by
  unfold srl_sra_signbitGen_pattern
  proveCombineValid

theorem srlw_sraw_signbit_valid :
    Puddle.CTree.Pattern.Valid (srl_sra_signbitGen_pattern .srliw rfl .sraiw 32) := by
  unfold srl_sra_signbitGen_pattern
  proveCombineValid

theorem drop_slli_srli_slt_valid :
    Puddle.CTree.Pattern.Valid (drop_slli_srli_boolGen_pattern .slt 2) := by
  unfold drop_slli_srli_boolGen_pattern
  proveCombineValid

theorem drop_slli_srli_sltu_valid :
    Puddle.CTree.Pattern.Valid (drop_slli_srli_boolGen_pattern .sltu 2) := by
  unfold drop_slli_srli_boolGen_pattern
  proveCombineValid

theorem drop_slli_srli_slti_valid :
    Puddle.CTree.Pattern.Valid (drop_slli_srli_boolGen_pattern .slti 1) := by
  unfold drop_slli_srli_boolGen_pattern
  proveCombineValid

theorem drop_slli_srli_sltiu_valid :
    Puddle.CTree.Pattern.Valid (drop_slli_srli_boolGen_pattern .sltiu 1) := by
  unfold drop_slli_srli_boolGen_pattern
  proveCombineValid

theorem drop_slli_srli_seqz_valid :
    Puddle.CTree.Pattern.Valid (drop_slli_srli_boolGen_pattern .seqz 1) := by
  unfold drop_slli_srli_boolGen_pattern
  proveCombineValid

theorem drop_slli_srli_snez_valid :
    Puddle.CTree.Pattern.Valid (drop_slli_srli_boolGen_pattern .snez 1) := by
  unfold drop_slli_srli_boolGen_pattern
  proveCombineValid

theorem drop_slli_srli_sltz_valid :
    Puddle.CTree.Pattern.Valid (drop_slli_srli_boolGen_pattern .sltz 1) := by
  unfold drop_slli_srli_boolGen_pattern
  proveCombineValid

theorem drop_slli_srli_sgtz_valid :
    Puddle.CTree.Pattern.Valid (drop_slli_srli_boolGen_pattern .sgtz 1) := by
  unfold drop_slli_srli_boolGen_pattern
  proveCombineValid

theorem drop_andi_one_srli_valid :
    Puddle.CTree.Pattern.Valid (drop_andi_one_srli_pattern) := by
  unfold drop_andi_one_srli_pattern
  proveCombineValid

theorem zextw_zextw_valid :
    Puddle.CTree.Pattern.Valid (drop_redundant_ext_pattern .zextw) := by
  unfold drop_redundant_ext_pattern
  proveCombineValid

theorem sextw_sextw_valid :
    Puddle.CTree.Pattern.Valid (drop_redundant_ext_pattern .sextw) := by
  unfold drop_redundant_ext_pattern
  proveCombineValid

theorem zextb_zextb_valid :
    Puddle.CTree.Pattern.Valid (drop_redundant_ext_pattern .zextb) := by
  unfold drop_redundant_ext_pattern
  proveCombineValid

theorem zexth_zexth_valid :
    Puddle.CTree.Pattern.Valid (drop_redundant_ext_pattern .zexth) := by
  unfold drop_redundant_ext_pattern
  proveCombineValid

theorem sextb_sextb_valid :
    Puddle.CTree.Pattern.Valid (drop_redundant_ext_pattern .sextb) := by
  unfold drop_redundant_ext_pattern
  proveCombineValid

theorem sexth_sexth_valid :
    Puddle.CTree.Pattern.Valid (drop_redundant_ext_pattern .sexth) := by
  unfold drop_redundant_ext_pattern
  proveCombineValid

theorem zextw_zextb_valid :
    Puddle.CTree.Pattern.Valid (zextw_zextb_pattern) := by
  unfold zextw_zextb_pattern
  proveCombineValid

theorem add_li_to_addi_valid :
    Puddle.CTree.Pattern.Valid (add_li_to_addi_pattern false) := by
  unfold add_li_to_addi_pattern
  proveCombineValid

theorem add_li_to_addi_commuted_valid :
    Puddle.CTree.Pattern.Valid (add_li_to_addi_pattern true) := by
  unfold add_li_to_addi_pattern
  proveCombineValid

theorem zextw_li_low32_valid :
    Puddle.CTree.Pattern.Valid (zextw_li_low32_pattern) := by
  unfold zextw_li_low32_pattern ext_of_li_pattern
  proveCombineValid

theorem sextw_li_low32_valid :
    Puddle.CTree.Pattern.Valid (sextw_li_low32_pattern) := by
  unfold sextw_li_low32_pattern ext_of_li_pattern
  proveCombineValid

theorem zextb_li_low8_valid :
    Puddle.CTree.Pattern.Valid (ext_li_range_pattern .zextb 0 256) := by
  unfold ext_li_range_pattern ext_of_li_pattern
  proveCombineValid

theorem zexth_li_low16_valid :
    Puddle.CTree.Pattern.Valid (ext_li_range_pattern .zexth 0 65536) := by
  unfold ext_li_range_pattern ext_of_li_pattern
  proveCombineValid

theorem sextb_li_low8_valid :
    Puddle.CTree.Pattern.Valid (ext_li_range_pattern .sextb (-128) 128) := by
  unfold ext_li_range_pattern ext_of_li_pattern
  proveCombineValid

theorem sexth_li_low16_valid :
    Puddle.CTree.Pattern.Valid (ext_li_range_pattern .sexth (-32768) 32768) := by
  unfold ext_li_range_pattern ext_of_li_pattern
  proveCombineValid

/-- The created `rv64.get_register` reads `x0`, whose value is zero. -/
theorem li_zero_to_x0_valid :
    Puddle.CTree.Pattern.Valid li_zero_to_x0_pattern := by
  unfold li_zero_to_x0_pattern
  simpPuddleValid
  simpCombineSemantics
  normalizeCombineValid
  all_goals simp [TypeAttr.of, Attribute.of, liftM, monadLift, MonadLift.monadLift,
    RuntimeValue.isRefinedBy, ControlFlowAction.optionIsRefinedBy, Data.RISCV.li,
    -Attribute.registerType_eq_of]

end Veir.RISCV.CTreeProofs
