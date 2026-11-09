module

import all Veir.Passes.RISCVCombines.Validity.Common

/-! CTree validity proofs for the RISC-V combines: dropping an operand producer whose changes the consumer ignores. -/

namespace Veir.RISCV.CTreeProofs

open Puddle
open _root_.CTree

set_option linter.unusedSimpArgs false

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Rv64.interpretOp'

attribute [local implicit_reducible] TypeAttr Veir._propertiesOf Riscv.propertiesOf

theorem drop_zextw_addw_0_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .addw 2 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_zextw_addw_1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .addw 2 1) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_zextw_addiw_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .addiw 1 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_zextw_roriw_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .roriw 1 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_zextw_srliw_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .srliw 1 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_zextw_subw_0_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .subw 2 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_zextw_subw_1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .subw 2 1) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_zextw_mulw_0_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .mulw 2 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_zextw_mulw_1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .mulw 2 1) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_zextw_divw_0_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .divw 2 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_zextw_divw_1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .divw 2 1) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_zextw_divuw_0_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .divuw 2 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_zextw_divuw_1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .divuw 2 1) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_zextw_remw_0_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .remw 2 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_zextw_remw_1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .remw 2 1) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_zextw_remuw_0_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .remuw 2 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_zextw_remuw_1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .remuw 2 1) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_zextw_sllw_0_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .sllw 2 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_zextw_sllw_1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .sllw 2 1) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_zextw_srlw_0_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .srlw 2 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_zextw_srlw_1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .srlw 2 1) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_zextw_sraw_0_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .sraw 2 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_zextw_sraw_1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .sraw 2 1) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_zextw_rolw_0_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .rolw 2 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_zextw_rolw_1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .rolw 2 1) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_zextw_rorw_0_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .rorw 2 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_zextw_rorw_1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .rorw 2 1) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_zextw_sraiw_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .sraiw 1 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_zextw_slliuw_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .slliuw 1 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_zextw_clzw_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .clzw 1 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_zextw_ctzw_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .ctzw 1 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_zextw_cpopw_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .cpopw 1 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_zextw_sextw_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .sextw 1 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_sextw_addw_0_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .addw 2 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_sextw_addw_1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .addw 2 1) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_sextw_addiw_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .addiw 1 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_sextw_roriw_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .roriw 1 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_sextw_srliw_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .srliw 1 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_sextw_subw_0_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .subw 2 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_sextw_subw_1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .subw 2 1) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_sextw_mulw_0_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .mulw 2 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_sextw_mulw_1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .mulw 2 1) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_sextw_divw_0_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .divw 2 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_sextw_divw_1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .divw 2 1) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_sextw_divuw_0_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .divuw 2 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_sextw_divuw_1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .divuw 2 1) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_sextw_remw_0_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .remw 2 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_sextw_remw_1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .remw 2 1) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_sextw_remuw_0_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .remuw 2 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_sextw_remuw_1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .remuw 2 1) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_sextw_sllw_0_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .sllw 2 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_sextw_sllw_1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .sllw 2 1) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_sextw_srlw_0_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .srlw 2 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_sextw_srlw_1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .srlw 2 1) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_sextw_sraw_0_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .sraw 2 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_sextw_sraw_1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .sraw 2 1) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_sextw_rolw_0_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .rolw 2 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_sextw_rolw_1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .rolw 2 1) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_sextw_rorw_0_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .rorw 2 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_sextw_rorw_1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .rorw 2 1) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_sextw_sraiw_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .sraiw 1 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_sextw_slliuw_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .slliuw 1 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_sextw_clzw_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .clzw 1 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_sextw_ctzw_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .ctzw 1 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_sextw_cpopw_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .cpopw 1 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_sextw_zextw_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .zextw 1 0) := by
  unfold drop_unary_operand_pattern
  proveCombineValid

theorem drop_sll_amount_mask_valid :
    Puddle.CTree.Pattern.Valid (drop_shift_amount_mask_pattern .sll 63) := by
  unfold drop_shift_amount_mask_pattern drop_unary_operand_pattern
  proveCombineValid

theorem drop_srl_amount_mask_valid :
    Puddle.CTree.Pattern.Valid (drop_shift_amount_mask_pattern .srl 63) := by
  unfold drop_shift_amount_mask_pattern drop_unary_operand_pattern
  proveCombineValid

theorem drop_sra_amount_mask_valid :
    Puddle.CTree.Pattern.Valid (drop_shift_amount_mask_pattern .sra 63) := by
  unfold drop_shift_amount_mask_pattern drop_unary_operand_pattern
  proveCombineValid

theorem drop_sllw_amount_mask_valid :
    Puddle.CTree.Pattern.Valid (drop_shift_amount_mask_pattern .sllw 31) := by
  unfold drop_shift_amount_mask_pattern drop_unary_operand_pattern
  proveCombineValid

theorem drop_srlw_amount_mask_valid :
    Puddle.CTree.Pattern.Valid (drop_shift_amount_mask_pattern .srlw 31) := by
  unfold drop_shift_amount_mask_pattern drop_unary_operand_pattern
  proveCombineValid

theorem drop_sraw_amount_mask_valid :
    Puddle.CTree.Pattern.Valid (drop_shift_amount_mask_pattern .sraw 31) := by
  unfold drop_shift_amount_mask_pattern drop_unary_operand_pattern
  proveCombineValid

theorem drop_sll_amount_zextw_valid :
    Puddle.CTree.Pattern.Valid (drop_zextw_shift_amount_pattern .sll) := by
  unfold drop_zextw_shift_amount_pattern drop_unary_operand_pattern
  proveCombineValid

theorem drop_srl_amount_zextw_valid :
    Puddle.CTree.Pattern.Valid (drop_zextw_shift_amount_pattern .srl) := by
  unfold drop_zextw_shift_amount_pattern drop_unary_operand_pattern
  proveCombineValid

theorem drop_sra_amount_zextw_valid :
    Puddle.CTree.Pattern.Valid (drop_zextw_shift_amount_pattern .sra) := by
  unfold drop_zextw_shift_amount_pattern drop_unary_operand_pattern
  proveCombineValid

end Veir.RISCV.CTreeProofs
