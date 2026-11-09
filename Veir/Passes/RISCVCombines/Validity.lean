module

public import Veir.PatternRewriter.Puddle.CTreeValidity
public import Veir.Passes.RISCVCombines.Combine
import all Veir.Passes.RISCVCombines.Validity.Basic
import all Veir.Passes.RISCVCombines.Validity.Bitwise
import all Veir.Passes.RISCVCombines.Validity.SignExtending
import all Veir.Passes.RISCVCombines.Validity.LowWord
import all Veir.Passes.RISCVCombines.Validity.Store

/-!
# CTree validity of the RISC-V combines

`certifiedCombines` lists the Puddle patterns of `Veir.Passes.RISCVCombines.Combine` that satisfy
`Puddle.CTree.Pattern.Valid`, each with its proof. The proofs follow the CTree strategy of
`math-fehr/puddle-ctree-wip`: `simpPuddleValid` discharges the structural obligations and erases
the handle bookkeeping, `simp [ctree_semantics]` unfolds the operation semantics, and the
remaining register equalities are decided by `veir_bv_decide`.

Patterns whose builder takes a correctness hypothesis are certified through the hypothesis-free
pattern they unfold to: `drop_ext_low_word_pattern` is `drop_unary_operand_pattern`, and
`sextw_signExtendingOpW_pattern` is `drop_sextw_of_producer_pattern`.

## Not certified

* The load-based combines `zextb_lbu`, `andi_255_lbu`, `zextw_slliw_lbu` (8, 16, 24),
  `packh_low_bytes{,_commuted}`, `packh_high_bytes{,_commuted}` and
  `sextw_{lw,lh,lb,lhu,lbu}`. They match a load as a non-root operation, and
  `Puddle.CTree.Pattern.Supported` requires non-root matched operations to be pure.
* The `ext_x0` combines (`zextw_x0`, `sextw_x0`, `zextb_x0`, `zexth_x0`, `sextb_x0`, `sexth_x0`).
  They rely on `x0` reading as zero, but `RuntimeValue.Conforms` lets a value of the `x0`
  register type be any register, so the statement does not hold in the semantic model.
* The LLVM funnel-shift combines, which are left for a follow-up.
-/

namespace Veir.RISCV.CTreeProofs

open Puddle

public section

/-- The certified RISC-V combine patterns (171 patterns). -/
def certifiedCombines : List { pattern : Pattern OpCode // Puddle.CTree.Pattern.Valid pattern } :=
  [
    ⟨right_identity_zero_add_pattern, right_identity_zero_add_valid⟩,
    ⟨srl_sra_signbitGen_pattern .srli rfl .srai 64, srl_sra_signbit_valid⟩,
    ⟨srl_sra_signbitGen_pattern .srliw rfl .sraiw 32, srlw_sraw_signbit_valid⟩,
    ⟨drop_slli_srli_boolGen_pattern .slt 2, drop_slli_srli_slt_valid⟩,
    ⟨drop_slli_srli_boolGen_pattern .sltu 2, drop_slli_srli_sltu_valid⟩,
    ⟨drop_slli_srli_boolGen_pattern .slti 1, drop_slli_srli_slti_valid⟩,
    ⟨drop_slli_srli_boolGen_pattern .sltiu 1, drop_slli_srli_sltiu_valid⟩,
    ⟨drop_slli_srli_boolGen_pattern .seqz 1, drop_slli_srli_seqz_valid⟩,
    ⟨drop_slli_srli_boolGen_pattern .snez 1, drop_slli_srli_snez_valid⟩,
    ⟨drop_slli_srli_boolGen_pattern .sltz 1, drop_slli_srli_sltz_valid⟩,
    ⟨drop_slli_srli_boolGen_pattern .sgtz 1, drop_slli_srli_sgtz_valid⟩,
    ⟨drop_andi_one_srli_pattern, drop_andi_one_srli_valid⟩,
    ⟨drop_redundant_ext_pattern .zextw, zextw_zextw_valid⟩,
    ⟨drop_redundant_ext_pattern .sextw, sextw_sextw_valid⟩,
    ⟨drop_redundant_ext_pattern .zextb, zextb_zextb_valid⟩,
    ⟨drop_redundant_ext_pattern .zexth, zexth_zexth_valid⟩,
    ⟨drop_redundant_ext_pattern .sextb, sextb_sextb_valid⟩,
    ⟨drop_redundant_ext_pattern .sexth, sexth_sexth_valid⟩,
    ⟨zextw_zextb_pattern, zextw_zextb_valid⟩,
    ⟨add_li_to_addi_pattern false, add_li_to_addi_valid⟩,
    ⟨add_li_to_addi_pattern true, add_li_to_addi_commuted_valid⟩,
    ⟨zextw_li_low32_pattern, zextw_li_low32_valid⟩,
    ⟨sextw_li_low32_pattern, sextw_li_low32_valid⟩,
    ⟨ext_li_range_pattern .zextb 0 256, zextb_li_low8_valid⟩,
    ⟨ext_li_range_pattern .zexth 0 65536, zexth_li_low16_valid⟩,
    ⟨ext_li_range_pattern .sextb (-128) 128, sextb_li_low8_valid⟩,
    ⟨ext_li_range_pattern .sexth (-32768) 32768, sexth_li_low16_valid⟩,
    ⟨li_zero_to_x0_pattern, li_zero_to_x0_valid⟩,
    ⟨drop_ext_of_bitwise_pattern .zextw .and true false, zextw_and_lhs_valid⟩,
    ⟨drop_ext_of_bitwise_pattern .zextw .and false true, zextw_and_rhs_valid⟩,
    ⟨drop_ext_of_bitwise_pattern .zextw .or true true, zextw_or_valid⟩,
    ⟨drop_ext_of_bitwise_pattern .zextw .xor true true, zextw_xor_valid⟩,
    ⟨drop_ext_of_bitwise_pattern .zextb .and true false, zextb_and_lhs_valid⟩,
    ⟨drop_ext_of_bitwise_pattern .zextb .and false true, zextb_and_rhs_valid⟩,
    ⟨drop_ext_of_bitwise_pattern .zextb .or true true, zextb_or_valid⟩,
    ⟨drop_ext_of_bitwise_pattern .zextb .xor true true, zextb_xor_valid⟩,
    ⟨drop_ext_of_bitwise_pattern .zexth .and true false, zexth_and_lhs_valid⟩,
    ⟨drop_ext_of_bitwise_pattern .zexth .and false true, zexth_and_rhs_valid⟩,
    ⟨drop_ext_of_bitwise_pattern .zexth .or true true, zexth_or_valid⟩,
    ⟨drop_ext_of_bitwise_pattern .zexth .xor true true, zexth_xor_valid⟩,
    ⟨drop_ext_of_bitwise_pattern .sextw .and true true, sextw_and_valid⟩,
    ⟨drop_ext_of_bitwise_pattern .sextw .or true true, sextw_or_valid⟩,
    ⟨drop_ext_of_bitwise_pattern .sextw .xor true true, sextw_xor_valid⟩,
    ⟨drop_ext_of_bitwise_pattern .sextb .and true true, sextb_and_valid⟩,
    ⟨drop_ext_of_bitwise_pattern .sextb .or true true, sextb_or_valid⟩,
    ⟨drop_ext_of_bitwise_pattern .sextb .xor true true, sextb_xor_valid⟩,
    ⟨drop_ext_of_bitwise_pattern .sexth .and true true, sexth_and_valid⟩,
    ⟨drop_ext_of_bitwise_pattern .sexth .or true true, sexth_or_valid⟩,
    ⟨drop_ext_of_bitwise_pattern .sexth .xor true true, sexth_xor_valid⟩,
    ⟨drop_sextw_of_producer_pattern .addw 2, sextw_addw_valid⟩,
    ⟨drop_sextw_of_producer_pattern .addiw 1, sextw_addiw_valid⟩,
    ⟨drop_sextw_of_producer_pattern .subw 2, sextw_subw_valid⟩,
    ⟨drop_sextw_of_producer_pattern .mulw 2, sextw_mulw_valid⟩,
    ⟨drop_sextw_of_producer_pattern .divw 2, sextw_divw_valid⟩,
    ⟨drop_sextw_of_producer_pattern .divuw 2, sextw_divuw_valid⟩,
    ⟨drop_sextw_of_producer_pattern .remw 2, sextw_remw_valid⟩,
    ⟨drop_sextw_of_producer_pattern .remuw 2, sextw_remuw_valid⟩,
    ⟨drop_sextw_of_producer_pattern .sllw 2, sextw_sllw_valid⟩,
    ⟨drop_sextw_of_producer_pattern .slliw 1, sextw_slliw_valid⟩,
    ⟨drop_sextw_of_producer_pattern .srlw 2, sextw_srlw_valid⟩,
    ⟨drop_sextw_of_producer_pattern .srliw 1, sextw_srliw_valid⟩,
    ⟨drop_sextw_of_producer_pattern .sraw 2, sextw_sraw_valid⟩,
    ⟨drop_sextw_of_producer_pattern .sraiw 1, sextw_sraiw_valid⟩,
    ⟨drop_sextw_of_producer_pattern .rolw 2, sextw_rolw_valid⟩,
    ⟨drop_sextw_of_producer_pattern .rorw 2, sextw_rorw_valid⟩,
    ⟨drop_sextw_of_producer_pattern .roriw 1, sextw_roriw_valid⟩,
    ⟨drop_sextw_of_producer_pattern .packw 2, sextw_packw_valid⟩,
    ⟨drop_sextw_of_producer_pattern .lui 0, sextw_lui_valid⟩,
    ⟨drop_sextw_of_producer_pattern .cpop 1, sextw_cpop_valid⟩,
    ⟨drop_sextw_of_producer_pattern .cpopw 1, sextw_cpopw_valid⟩,
    ⟨drop_sextw_of_producer_pattern .clz 1, sextw_clz_valid⟩,
    ⟨drop_sextw_of_producer_pattern .clzw 1, sextw_clzw_valid⟩,
    ⟨drop_sextw_of_producer_pattern .ctz 1, sextw_ctz_valid⟩,
    ⟨drop_sextw_of_producer_pattern .ctzw 1, sextw_ctzw_valid⟩,
    ⟨drop_sextw_of_producer_pattern .slt 2, sextw_slt_valid⟩,
    ⟨drop_sextw_of_producer_pattern .sltu 2, sextw_sltu_valid⟩,
    ⟨drop_sextw_of_producer_pattern .slti 1, sextw_slti_valid⟩,
    ⟨drop_sextw_of_producer_pattern .sltiu 1, sextw_sltiu_valid⟩,
    ⟨drop_sextw_of_producer_pattern .bext 2, sextw_bext_valid⟩,
    ⟨drop_sextw_of_producer_pattern .bexti 1, sextw_bexti_valid⟩,
    ⟨drop_sextw_of_producer_pattern .sextb 1, sextw_sextb_valid⟩,
    ⟨drop_sextw_of_producer_pattern .sexth 1, sextw_sexth_valid⟩,
    ⟨drop_sextw_of_producer_pattern .zexth 1, sextw_zexth_valid⟩,
    ⟨drop_sextw_of_producer_pattern .packh 2, sextw_packh_valid⟩,
    ⟨drop_sextw_of_producer_pattern .srai 1 (fun p => 32#6 ≤ p.immField 6), sextw_srai_valid⟩,
    ⟨drop_sextw_of_producer_pattern .srli 1 (fun p => 32#6 < p.immField 6), sextw_srli_valid⟩,
    ⟨drop_sextw_of_producer_pattern .andi 1 (fun p => !(p.immField 12).msb), sextw_andi_valid⟩,
    ⟨drop_sextw_of_producer_pattern .ori 1 (fun p => (p.immField 12).msb), sextw_ori_valid⟩,
    ⟨drop_unary_operand_pattern .zextw .addw 2 0, drop_zextw_addw_0_valid⟩,
    ⟨drop_unary_operand_pattern .zextw .addw 2 1, drop_zextw_addw_1_valid⟩,
    ⟨drop_unary_operand_pattern .zextw .addiw 1 0, drop_zextw_addiw_valid⟩,
    ⟨drop_unary_operand_pattern .zextw .roriw 1 0, drop_zextw_roriw_valid⟩,
    ⟨drop_unary_operand_pattern .zextw .srliw 1 0, drop_zextw_srliw_valid⟩,
    ⟨drop_unary_operand_pattern .zextw .subw 2 0, drop_zextw_subw_0_valid⟩,
    ⟨drop_unary_operand_pattern .zextw .subw 2 1, drop_zextw_subw_1_valid⟩,
    ⟨drop_unary_operand_pattern .zextw .mulw 2 0, drop_zextw_mulw_0_valid⟩,
    ⟨drop_unary_operand_pattern .zextw .mulw 2 1, drop_zextw_mulw_1_valid⟩,
    ⟨drop_unary_operand_pattern .zextw .divw 2 0, drop_zextw_divw_0_valid⟩,
    ⟨drop_unary_operand_pattern .zextw .divw 2 1, drop_zextw_divw_1_valid⟩,
    ⟨drop_unary_operand_pattern .zextw .divuw 2 0, drop_zextw_divuw_0_valid⟩,
    ⟨drop_unary_operand_pattern .zextw .divuw 2 1, drop_zextw_divuw_1_valid⟩,
    ⟨drop_unary_operand_pattern .zextw .remw 2 0, drop_zextw_remw_0_valid⟩,
    ⟨drop_unary_operand_pattern .zextw .remw 2 1, drop_zextw_remw_1_valid⟩,
    ⟨drop_unary_operand_pattern .zextw .remuw 2 0, drop_zextw_remuw_0_valid⟩,
    ⟨drop_unary_operand_pattern .zextw .remuw 2 1, drop_zextw_remuw_1_valid⟩,
    ⟨drop_unary_operand_pattern .zextw .sllw 2 0, drop_zextw_sllw_0_valid⟩,
    ⟨drop_unary_operand_pattern .zextw .sllw 2 1, drop_zextw_sllw_1_valid⟩,
    ⟨drop_unary_operand_pattern .zextw .srlw 2 0, drop_zextw_srlw_0_valid⟩,
    ⟨drop_unary_operand_pattern .zextw .srlw 2 1, drop_zextw_srlw_1_valid⟩,
    ⟨drop_unary_operand_pattern .zextw .sraw 2 0, drop_zextw_sraw_0_valid⟩,
    ⟨drop_unary_operand_pattern .zextw .sraw 2 1, drop_zextw_sraw_1_valid⟩,
    ⟨drop_unary_operand_pattern .zextw .rolw 2 0, drop_zextw_rolw_0_valid⟩,
    ⟨drop_unary_operand_pattern .zextw .rolw 2 1, drop_zextw_rolw_1_valid⟩,
    ⟨drop_unary_operand_pattern .zextw .rorw 2 0, drop_zextw_rorw_0_valid⟩,
    ⟨drop_unary_operand_pattern .zextw .rorw 2 1, drop_zextw_rorw_1_valid⟩,
    ⟨drop_unary_operand_pattern .zextw .sraiw 1 0, drop_zextw_sraiw_valid⟩,
    ⟨drop_unary_operand_pattern .zextw .slliuw 1 0, drop_zextw_slliuw_valid⟩,
    ⟨drop_unary_operand_pattern .zextw .clzw 1 0, drop_zextw_clzw_valid⟩,
    ⟨drop_unary_operand_pattern .zextw .ctzw 1 0, drop_zextw_ctzw_valid⟩,
    ⟨drop_unary_operand_pattern .zextw .cpopw 1 0, drop_zextw_cpopw_valid⟩,
    ⟨drop_unary_operand_pattern .zextw .sextw 1 0, drop_zextw_sextw_valid⟩,
    ⟨drop_unary_operand_pattern .sextw .addw 2 0, drop_sextw_addw_0_valid⟩,
    ⟨drop_unary_operand_pattern .sextw .addw 2 1, drop_sextw_addw_1_valid⟩,
    ⟨drop_unary_operand_pattern .sextw .addiw 1 0, drop_sextw_addiw_valid⟩,
    ⟨drop_unary_operand_pattern .sextw .roriw 1 0, drop_sextw_roriw_valid⟩,
    ⟨drop_unary_operand_pattern .sextw .srliw 1 0, drop_sextw_srliw_valid⟩,
    ⟨drop_unary_operand_pattern .sextw .subw 2 0, drop_sextw_subw_0_valid⟩,
    ⟨drop_unary_operand_pattern .sextw .subw 2 1, drop_sextw_subw_1_valid⟩,
    ⟨drop_unary_operand_pattern .sextw .mulw 2 0, drop_sextw_mulw_0_valid⟩,
    ⟨drop_unary_operand_pattern .sextw .mulw 2 1, drop_sextw_mulw_1_valid⟩,
    ⟨drop_unary_operand_pattern .sextw .divw 2 0, drop_sextw_divw_0_valid⟩,
    ⟨drop_unary_operand_pattern .sextw .divw 2 1, drop_sextw_divw_1_valid⟩,
    ⟨drop_unary_operand_pattern .sextw .divuw 2 0, drop_sextw_divuw_0_valid⟩,
    ⟨drop_unary_operand_pattern .sextw .divuw 2 1, drop_sextw_divuw_1_valid⟩,
    ⟨drop_unary_operand_pattern .sextw .remw 2 0, drop_sextw_remw_0_valid⟩,
    ⟨drop_unary_operand_pattern .sextw .remw 2 1, drop_sextw_remw_1_valid⟩,
    ⟨drop_unary_operand_pattern .sextw .remuw 2 0, drop_sextw_remuw_0_valid⟩,
    ⟨drop_unary_operand_pattern .sextw .remuw 2 1, drop_sextw_remuw_1_valid⟩,
    ⟨drop_unary_operand_pattern .sextw .sllw 2 0, drop_sextw_sllw_0_valid⟩,
    ⟨drop_unary_operand_pattern .sextw .sllw 2 1, drop_sextw_sllw_1_valid⟩,
    ⟨drop_unary_operand_pattern .sextw .srlw 2 0, drop_sextw_srlw_0_valid⟩,
    ⟨drop_unary_operand_pattern .sextw .srlw 2 1, drop_sextw_srlw_1_valid⟩,
    ⟨drop_unary_operand_pattern .sextw .sraw 2 0, drop_sextw_sraw_0_valid⟩,
    ⟨drop_unary_operand_pattern .sextw .sraw 2 1, drop_sextw_sraw_1_valid⟩,
    ⟨drop_unary_operand_pattern .sextw .rolw 2 0, drop_sextw_rolw_0_valid⟩,
    ⟨drop_unary_operand_pattern .sextw .rolw 2 1, drop_sextw_rolw_1_valid⟩,
    ⟨drop_unary_operand_pattern .sextw .rorw 2 0, drop_sextw_rorw_0_valid⟩,
    ⟨drop_unary_operand_pattern .sextw .rorw 2 1, drop_sextw_rorw_1_valid⟩,
    ⟨drop_unary_operand_pattern .sextw .sraiw 1 0, drop_sextw_sraiw_valid⟩,
    ⟨drop_unary_operand_pattern .sextw .slliuw 1 0, drop_sextw_slliuw_valid⟩,
    ⟨drop_unary_operand_pattern .sextw .clzw 1 0, drop_sextw_clzw_valid⟩,
    ⟨drop_unary_operand_pattern .sextw .ctzw 1 0, drop_sextw_ctzw_valid⟩,
    ⟨drop_unary_operand_pattern .sextw .cpopw 1 0, drop_sextw_cpopw_valid⟩,
    ⟨drop_unary_operand_pattern .sextw .zextw 1 0, drop_sextw_zextw_valid⟩,
    ⟨drop_shift_amount_mask_pattern .sll 63, drop_sll_amount_mask_valid⟩,
    ⟨drop_shift_amount_mask_pattern .srl 63, drop_srl_amount_mask_valid⟩,
    ⟨drop_shift_amount_mask_pattern .sra 63, drop_sra_amount_mask_valid⟩,
    ⟨drop_shift_amount_mask_pattern .sllw 31, drop_sllw_amount_mask_valid⟩,
    ⟨drop_shift_amount_mask_pattern .srlw 31, drop_srlw_amount_mask_valid⟩,
    ⟨drop_shift_amount_mask_pattern .sraw 31, drop_sraw_amount_mask_valid⟩,
    ⟨drop_zextw_shift_amount_pattern .sll, drop_sll_amount_zextw_valid⟩,
    ⟨drop_zextw_shift_amount_pattern .srl, drop_srl_amount_zextw_valid⟩,
    ⟨drop_zextw_shift_amount_pattern .sra, drop_sra_amount_zextw_valid⟩,
    ⟨drop_ext_store_pattern .zextw .sw, drop_zextw_sw_valid⟩,
    ⟨drop_ext_store_pattern .sextw .sw, drop_sextw_sw_valid⟩,
    ⟨drop_ext_store_pattern .zexth .sh, drop_zexth_sh_valid⟩,
    ⟨drop_ext_store_pattern .sexth .sh, drop_sexth_sh_valid⟩,
    ⟨drop_ext_store_pattern .zextb .sb, drop_zextb_sb_valid⟩,
    ⟨drop_ext_store_pattern .sextb .sb, drop_sextb_sb_valid⟩,
    ⟨drop_ext_store_pattern .zextw .sb, drop_zextw_sb_valid⟩,
    ⟨drop_ext_store_pattern .sextw .sb, drop_sextw_sb_valid⟩
  ]

/-- Every certified combine pattern satisfies the CTree validity predicate. -/
theorem certifiedCombines_valid (pattern : Pattern OpCode)
    (h : pattern ∈ certifiedCombines.map Subtype.val) :
    Puddle.CTree.Pattern.Valid pattern := by
  obtain ⟨certificate, _, rfl⟩ := List.mem_map.mp h
  exact certificate.property

end

end Veir.RISCV.CTreeProofs
