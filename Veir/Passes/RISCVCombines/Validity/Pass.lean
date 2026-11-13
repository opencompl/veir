module

public import Veir.Passes.RISCVCombines.Combine
public import Veir.Passes.Pipeline.Soundness
import all Veir.Passes.RISCVCombines.Combine
import all Veir.Passes.RISCVCombines.Validity.Basic
import all Veir.Passes.RISCVCombines.Validity.Bitwise
import all Veir.Passes.RISCVCombines.Validity.SignExtending
import all Veir.Passes.RISCVCombines.Validity.LowWord
import all Veir.Passes.RISCVCombines.Validity.Store
import all Veir.Passes.RISCVCombines.Validity.Load

/-!
# Soundness of the `riscv-combine` pass

Every entry of `combinePatterns` is pointwise valid, by the validity proof of its pattern or, for
the combines that try several patterns, of each of them. The pass is then sound.
-/

namespace Veir.RISCV.CTreeProofs

open Puddle.CTree RewritePattern

/-- A combine that drops an extension on any of the operands reading only the low word. -/
theorem drop_ext_low_word_pointwise {ext dst : Riscv} {arity : Nat}
    {readsLowWord : ReadsLowWord dst arity}
    (valid : ∀ index < arity, Pattern.Valid (drop_unary_operand_pattern ext dst arity index)) :
    PointwiseValid (drop_ext_low_word ext dst arity readsLowWord).run := by
  unfold drop_ext_low_word
  refine PointwiseValid.greedy fun pattern member => ?_
  obtain ⟨compiled, compiledMember, rfl⟩ := Array.mem_map.mp member
  obtain ⟨index, indexMember, rfl⟩ := Array.mem_map.mp compiledMember
  exact PointwiseValid.compile (valid index (Array.mem_range.mp indexMember))

/-- A combine that drops an extension on either operand of a bitwise operation. -/
theorem drop_ext_of_bitwise_true_pointwise {ext dst : Riscv}
    (lhs : Pattern.Valid (drop_ext_of_bitwise_pattern ext dst true false))
    (rhs : Pattern.Valid (drop_ext_of_bitwise_pattern ext dst false true)) :
    PointwiseValid (drop_ext_of_bitwise ext dst true).run := by
  unfold drop_ext_of_bitwise
  simp only [↓reduceIte]
  refine PointwiseValid.greedy fun pattern member => ?_
  obtain ⟨compiled, compiledMember, rfl⟩ := Array.mem_map.mp member
  simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at compiledMember
  rcases compiledMember with rfl | rfl
  · exact PointwiseValid.compile lhs
  · exact PointwiseValid.compile rhs

/-- A combine that drops an extension on both operands of a bitwise operation. -/
theorem drop_ext_of_bitwise_false_pointwise {ext dst : Riscv}
    (both : Pattern.Valid (drop_ext_of_bitwise_pattern ext dst true true)) :
    PointwiseValid (drop_ext_of_bitwise ext dst false).run :=
  PointwiseValid.compile both

public section

/-- Every combine of the pass is pointwise valid. -/
theorem combinePatterns_pointwise :
    ∀ pattern ∈ combinePatterns.map (·.run), PointwiseValid pattern := by
  intro pattern member
  obtain ⟨entry, entryMember, rfl⟩ := Array.mem_map.mp member
  simp only [combinePatterns, List.mem_toArray, List.mem_cons, List.not_mem_nil,
    or_false] at entryMember
  rcases entryMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact PointwiseValid.compile packh_low_bytes_valid
  · exact PointwiseValid.compile packh_low_bytes_commuted_valid
  · exact PointwiseValid.compile packh_high_bytes_valid
  · exact PointwiseValid.compile packh_high_bytes_commuted_valid
  · exact PointwiseValid.compile zextb_lbu_valid
  · exact PointwiseValid.compile andi_255_lbu_valid
  · exact PointwiseValid.compile add_li_to_addi_valid
  · exact PointwiseValid.compile add_li_to_addi_commuted_valid
  · exact PointwiseValid.compile zextw_slliw_lbu_8_valid
  · exact PointwiseValid.compile zextw_slliw_lbu_16_valid
  · exact PointwiseValid.compile zextw_slliw_lbu_24_valid
  · exact PointwiseValid.compile right_identity_zero_add_valid
  · exact PointwiseValid.compile srl_sra_signbit_valid
  · exact PointwiseValid.compile srlw_sraw_signbit_valid
  · exact PointwiseValid.compile drop_slli_srli_slt_valid
  · exact PointwiseValid.compile drop_slli_srli_sltu_valid
  · exact PointwiseValid.compile drop_slli_srli_slti_valid
  · exact PointwiseValid.compile drop_slli_srli_sltiu_valid
  · exact PointwiseValid.compile drop_slli_srli_seqz_valid
  · exact PointwiseValid.compile drop_slli_srli_snez_valid
  · exact PointwiseValid.compile drop_slli_srli_sltz_valid
  · exact PointwiseValid.compile drop_slli_srli_sgtz_valid
  · exact PointwiseValid.compile drop_andi_one_srli_valid
  · exact PointwiseValid.compile zextw_zextw_valid
  · exact PointwiseValid.compile zextw_zextb_valid
  · exact PointwiseValid.compile drop_sll_amount_mask_valid
  · exact PointwiseValid.compile drop_srl_amount_mask_valid
  · exact PointwiseValid.compile drop_sra_amount_mask_valid
  · exact PointwiseValid.compile drop_sllw_amount_mask_valid
  · exact PointwiseValid.compile drop_srlw_amount_mask_valid
  · exact PointwiseValid.compile drop_sraw_amount_mask_valid
  · exact PointwiseValid.compile drop_sll_amount_zextw_valid
  · exact PointwiseValid.compile drop_srl_amount_zextw_valid
  · exact PointwiseValid.compile drop_sra_amount_zextw_valid
  · exact drop_ext_low_word_pointwise (arity := 2) fun i hi => match i with
      | 0 => drop_zextw_addw_rs1_valid
      | 1 => drop_zextw_addw_rs2_valid
      | _ + 2 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 1) fun i hi => match i with
      | 0 => drop_zextw_addiw_valid
      | _ + 1 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 1) fun i hi => match i with
      | 0 => drop_zextw_roriw_valid
      | _ + 1 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 1) fun i hi => match i with
      | 0 => drop_zextw_srliw_valid
      | _ + 1 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 2) fun i hi => match i with
      | 0 => drop_zextw_subw_rs1_valid
      | 1 => drop_zextw_subw_rs2_valid
      | _ + 2 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 2) fun i hi => match i with
      | 0 => drop_zextw_mulw_rs1_valid
      | 1 => drop_zextw_mulw_rs2_valid
      | _ + 2 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 2) fun i hi => match i with
      | 0 => drop_zextw_divw_rs1_valid
      | 1 => drop_zextw_divw_rs2_valid
      | _ + 2 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 2) fun i hi => match i with
      | 0 => drop_zextw_divuw_rs1_valid
      | 1 => drop_zextw_divuw_rs2_valid
      | _ + 2 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 2) fun i hi => match i with
      | 0 => drop_zextw_remw_rs1_valid
      | 1 => drop_zextw_remw_rs2_valid
      | _ + 2 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 2) fun i hi => match i with
      | 0 => drop_zextw_remuw_rs1_valid
      | 1 => drop_zextw_remuw_rs2_valid
      | _ + 2 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 2) fun i hi => match i with
      | 0 => drop_zextw_sllw_rs1_valid
      | 1 => drop_zextw_sllw_rs2_valid
      | _ + 2 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 2) fun i hi => match i with
      | 0 => drop_zextw_srlw_rs1_valid
      | 1 => drop_zextw_srlw_rs2_valid
      | _ + 2 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 2) fun i hi => match i with
      | 0 => drop_zextw_sraw_rs1_valid
      | 1 => drop_zextw_sraw_rs2_valid
      | _ + 2 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 2) fun i hi => match i with
      | 0 => drop_zextw_rolw_rs1_valid
      | 1 => drop_zextw_rolw_rs2_valid
      | _ + 2 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 2) fun i hi => match i with
      | 0 => drop_zextw_rorw_rs1_valid
      | 1 => drop_zextw_rorw_rs2_valid
      | _ + 2 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 1) fun i hi => match i with
      | 0 => drop_zextw_sraiw_valid
      | _ + 1 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 1) fun i hi => match i with
      | 0 => drop_zextw_slliuw_valid
      | _ + 1 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 1) fun i hi => match i with
      | 0 => drop_zextw_clzw_valid
      | _ + 1 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 1) fun i hi => match i with
      | 0 => drop_zextw_ctzw_valid
      | _ + 1 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 1) fun i hi => match i with
      | 0 => drop_zextw_cpopw_valid
      | _ + 1 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 1) fun i hi => match i with
      | 0 => drop_zextw_sextw_valid
      | _ + 1 => absurd hi (by omega)
  · exact drop_ext_of_bitwise_true_pointwise zextw_and_lhs_valid zextw_and_rhs_valid
  · exact drop_ext_of_bitwise_false_pointwise zextw_or_valid
  · exact drop_ext_of_bitwise_false_pointwise zextw_xor_valid
  · exact PointwiseValid.compile drop_zextw_sw_valid
  · exact PointwiseValid.compile zextw_li_low32_valid
  · exact PointwiseValid.compile sextw_sextw_valid
  · exact drop_ext_low_word_pointwise (arity := 2) fun i hi => match i with
      | 0 => drop_sextw_addw_rs1_valid
      | 1 => drop_sextw_addw_rs2_valid
      | _ + 2 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 1) fun i hi => match i with
      | 0 => drop_sextw_addiw_valid
      | _ + 1 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 1) fun i hi => match i with
      | 0 => drop_sextw_roriw_valid
      | _ + 1 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 1) fun i hi => match i with
      | 0 => drop_sextw_srliw_valid
      | _ + 1 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 2) fun i hi => match i with
      | 0 => drop_sextw_subw_rs1_valid
      | 1 => drop_sextw_subw_rs2_valid
      | _ + 2 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 2) fun i hi => match i with
      | 0 => drop_sextw_mulw_rs1_valid
      | 1 => drop_sextw_mulw_rs2_valid
      | _ + 2 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 2) fun i hi => match i with
      | 0 => drop_sextw_divw_rs1_valid
      | 1 => drop_sextw_divw_rs2_valid
      | _ + 2 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 2) fun i hi => match i with
      | 0 => drop_sextw_divuw_rs1_valid
      | 1 => drop_sextw_divuw_rs2_valid
      | _ + 2 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 2) fun i hi => match i with
      | 0 => drop_sextw_remw_rs1_valid
      | 1 => drop_sextw_remw_rs2_valid
      | _ + 2 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 2) fun i hi => match i with
      | 0 => drop_sextw_remuw_rs1_valid
      | 1 => drop_sextw_remuw_rs2_valid
      | _ + 2 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 2) fun i hi => match i with
      | 0 => drop_sextw_sllw_rs1_valid
      | 1 => drop_sextw_sllw_rs2_valid
      | _ + 2 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 2) fun i hi => match i with
      | 0 => drop_sextw_srlw_rs1_valid
      | 1 => drop_sextw_srlw_rs2_valid
      | _ + 2 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 2) fun i hi => match i with
      | 0 => drop_sextw_sraw_rs1_valid
      | 1 => drop_sextw_sraw_rs2_valid
      | _ + 2 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 2) fun i hi => match i with
      | 0 => drop_sextw_rolw_rs1_valid
      | 1 => drop_sextw_rolw_rs2_valid
      | _ + 2 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 2) fun i hi => match i with
      | 0 => drop_sextw_rorw_rs1_valid
      | 1 => drop_sextw_rorw_rs2_valid
      | _ + 2 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 1) fun i hi => match i with
      | 0 => drop_sextw_sraiw_valid
      | _ + 1 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 1) fun i hi => match i with
      | 0 => drop_sextw_slliuw_valid
      | _ + 1 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 1) fun i hi => match i with
      | 0 => drop_sextw_clzw_valid
      | _ + 1 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 1) fun i hi => match i with
      | 0 => drop_sextw_ctzw_valid
      | _ + 1 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 1) fun i hi => match i with
      | 0 => drop_sextw_cpopw_valid
      | _ + 1 => absurd hi (by omega)
  · exact drop_ext_low_word_pointwise (arity := 1) fun i hi => match i with
      | 0 => drop_sextw_zextw_valid
      | _ + 1 => absurd hi (by omega)
  · exact drop_ext_of_bitwise_false_pointwise sextw_and_valid
  · exact drop_ext_of_bitwise_false_pointwise sextw_or_valid
  · exact drop_ext_of_bitwise_false_pointwise sextw_xor_valid
  · exact PointwiseValid.compile drop_sextw_sw_valid
  · exact PointwiseValid.compile sextw_li_low32_valid
  · exact PointwiseValid.compile (sextw_lw_valid _)
  · exact PointwiseValid.compile (sextw_lh_valid _)
  · exact PointwiseValid.compile (sextw_lb_valid _)
  · exact PointwiseValid.compile (sextw_lhu_valid _)
  · exact PointwiseValid.compile (sextw_lbu_valid _)
  · exact PointwiseValid.compile (sextw_addw_valid _)
  · exact PointwiseValid.compile (sextw_addiw_valid _)
  · exact PointwiseValid.compile (sextw_subw_valid _)
  · exact PointwiseValid.compile (sextw_mulw_valid _)
  · exact PointwiseValid.compile (sextw_divw_valid _)
  · exact PointwiseValid.compile (sextw_divuw_valid _)
  · exact PointwiseValid.compile (sextw_remw_valid _)
  · exact PointwiseValid.compile (sextw_remuw_valid _)
  · exact PointwiseValid.compile (sextw_sllw_valid _)
  · exact PointwiseValid.compile (sextw_slliw_valid _)
  · exact PointwiseValid.compile (sextw_srlw_valid _)
  · exact PointwiseValid.compile (sextw_srliw_valid _)
  · exact PointwiseValid.compile (sextw_sraw_valid _)
  · exact PointwiseValid.compile (sextw_sraiw_valid _)
  · exact PointwiseValid.compile (sextw_rolw_valid _)
  · exact PointwiseValid.compile (sextw_rorw_valid _)
  · exact PointwiseValid.compile (sextw_roriw_valid _)
  · exact PointwiseValid.compile (sextw_clzw_valid _)
  · exact PointwiseValid.compile (sextw_ctzw_valid _)
  · exact PointwiseValid.compile (sextw_cpopw_valid _)
  · exact PointwiseValid.compile (sextw_packw_valid _)
  · exact PointwiseValid.compile (sextw_slt_valid _)
  · exact PointwiseValid.compile (sextw_sltu_valid _)
  · exact PointwiseValid.compile (sextw_slti_valid _)
  · exact PointwiseValid.compile (sextw_sltiu_valid _)
  · exact PointwiseValid.compile (sextw_clz_valid _)
  · exact PointwiseValid.compile (sextw_ctz_valid _)
  · exact PointwiseValid.compile (sextw_cpop_valid _)
  · exact PointwiseValid.compile (sextw_bext_valid _)
  · exact PointwiseValid.compile (sextw_bexti_valid _)
  · exact PointwiseValid.compile (sextw_sextb_valid _)
  · exact PointwiseValid.compile (sextw_sexth_valid _)
  · exact PointwiseValid.compile (sextw_zexth_valid _)
  · exact PointwiseValid.compile (sextw_packh_valid _)
  · exact PointwiseValid.compile (sextw_lui_valid _)
  · exact PointwiseValid.compile (sextw_srai_valid _)
  · exact PointwiseValid.compile (sextw_srli_valid _)
  · exact PointwiseValid.compile (sextw_andi_valid _)
  · exact PointwiseValid.compile (sextw_ori_valid _)
  · exact PointwiseValid.compile zextb_zextb_valid
  · exact PointwiseValid.compile zexth_zexth_valid
  · exact PointwiseValid.compile sextb_sextb_valid
  · exact PointwiseValid.compile sexth_sexth_valid
  · exact drop_ext_of_bitwise_true_pointwise zextb_and_lhs_valid zextb_and_rhs_valid
  · exact drop_ext_of_bitwise_false_pointwise zextb_or_valid
  · exact drop_ext_of_bitwise_false_pointwise zextb_xor_valid
  · exact drop_ext_of_bitwise_true_pointwise zexth_and_lhs_valid zexth_and_rhs_valid
  · exact drop_ext_of_bitwise_false_pointwise zexth_or_valid
  · exact drop_ext_of_bitwise_false_pointwise zexth_xor_valid
  · exact drop_ext_of_bitwise_false_pointwise sextb_and_valid
  · exact drop_ext_of_bitwise_false_pointwise sextb_or_valid
  · exact drop_ext_of_bitwise_false_pointwise sextb_xor_valid
  · exact drop_ext_of_bitwise_false_pointwise sexth_and_valid
  · exact drop_ext_of_bitwise_false_pointwise sexth_or_valid
  · exact drop_ext_of_bitwise_false_pointwise sexth_xor_valid
  · exact PointwiseValid.compile drop_zexth_sh_valid
  · exact PointwiseValid.compile drop_sexth_sh_valid
  · exact PointwiseValid.compile drop_zextb_sb_valid
  · exact PointwiseValid.compile drop_sextb_sb_valid
  · exact PointwiseValid.compile drop_zextw_sb_valid
  · exact PointwiseValid.compile drop_sextw_sb_valid
  · exact PointwiseValid.compile zextb_li_low8_valid
  · exact PointwiseValid.compile zexth_li_low16_valid
  · exact PointwiseValid.compile sextb_li_low8_valid
  · exact PointwiseValid.compile sexth_li_low16_valid
  · exact PointwiseValid.compile li_zero_to_x0_valid

/-- The `riscv-combine` pass refines the module and leaves it verified. -/
theorem Combine.run_sound : Combine.run.Sound :=
  checkedContextPass_sound (PointwiseValid.greedy combinePatterns_pointwise)

/-- The pass with its IO returns what `Combine.run` does. -/
theorem Combine.impl_eq_run (ctx : WfIRContext OpCode) (op : OperationPtr)
    (opIn : op.InBounds ctx.raw) :
    Combine.impl ctx op opIn = ExceptT.mk (pure (Combine.run ctx op)) := by
  rw [Combine.impl]

end
end Veir.RISCV.CTreeProofs
