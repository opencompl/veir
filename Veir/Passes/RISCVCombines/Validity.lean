module

public import Veir.PatternRewriter.Puddle.CTreeValidity
public import Veir.Passes.RISCVCombines.Combine
import all Veir.Passes.RISCVCombines.Combine
import all Veir.Passes.RISCVCombines.Validity.Basic
import all Veir.Passes.RISCVCombines.Validity.Bitwise
import all Veir.Passes.RISCVCombines.Validity.SignExtending
import all Veir.Passes.RISCVCombines.Validity.LowWord
import all Veir.Passes.RISCVCombines.Validity.Store
import all Veir.Passes.RISCVCombines.Validity.Load

/-!
# CTree validity of the RISC-V combines

`combineCertificates` holds a certificate for every pattern in `combinePatternList`, the patterns
`riscv-combine` runs, in the same order: a proof of `Puddle.CTree.Pattern.Valid`, or the reason
why there is none. Its type is indexed by `combinePatternList`, so registering, removing or
reordering a combine without updating the certificates does not build.

The proofs follow the CTree strategy of `math-fehr/puddle-ctree-wip`: `simpPuddleValid`
discharges the structural obligations and erases the handle bookkeeping,
`simp [ctree_semantics]` unfolds the operation semantics, and each remaining register equality is
closed by the combine's local correctness lemma in `Veir.Passes.RISCVCombines.Proofs`, whose
statement must therefore match the pattern exactly.
-/

namespace Veir.RISCV.CTreeProofs

open Puddle

public section

/-- Why a registered combine pattern has no CTree validity proof. Every combine is currently
proven, so there is no reason yet; one is added here with a combine that cannot be proven. -/
inductive Unproven where
  deriving Repr, DecidableEq

/-- A certificate for each pattern of a list, in order: a CTree validity proof, or the reason why
there is none. -/
inductive Certificates : List (Pattern OpCode) → Type 1 where
  | nil : Certificates []
  | proven {pattern : Pattern OpCode} {patterns : List (Pattern OpCode)}
      (valid : Puddle.CTree.Pattern.Valid pattern) (rest : Certificates patterns) :
      Certificates (pattern :: patterns)
  | unproven {pattern : Pattern OpCode} {patterns : List (Pattern OpCode)}
      (reason : Unproven) (rest : Certificates patterns) : Certificates (pattern :: patterns)

namespace Certificates

/-- The patterns that have a validity proof. -/
def provenPatterns : {patterns : List (Pattern OpCode)} → Certificates patterns →
    List (Pattern OpCode)
  | _, .nil => []
  | _, .proven (pattern := pattern) _ rest => pattern :: rest.provenPatterns
  | _, .unproven _ rest => rest.provenPatterns

/-- The patterns that have no validity proof, with the reason. -/
def unprovenPatterns : {patterns : List (Pattern OpCode)} → Certificates patterns →
    List (Pattern OpCode × Unproven)
  | _, .nil => []
  | _, .proven _ rest => rest.unprovenPatterns
  | _, .unproven (pattern := pattern) reason rest => (pattern, reason) :: rest.unprovenPatterns

/-- Every pattern with a proof certificate satisfies the CTree validity predicate. -/
theorem valid : {patterns : List (Pattern OpCode)} → (certificates : Certificates patterns) →
    ∀ pattern ∈ certificates.provenPatterns, Puddle.CTree.Pattern.Valid pattern
  | _, .nil => by simp [provenPatterns]
  | _, .proven h rest => by
    simp only [provenPatterns, List.mem_cons, forall_eq_or_imp]
    exact ⟨h, valid rest⟩
  | _, .unproven _ rest => by simpa [provenPatterns] using valid rest

/-- Every pattern of the list is either proven or recorded as unproven. -/
theorem covers : {patterns : List (Pattern OpCode)} → (certificates : Certificates patterns) →
    ∀ pattern ∈ patterns, pattern ∈ certificates.provenPatterns ∨
      pattern ∈ certificates.unprovenPatterns.map Prod.fst
  | _, .nil => by simp
  | _, .proven _ rest => by
    simp only [List.mem_cons, forall_eq_or_imp, provenPatterns, true_or, true_and]
    intro pattern h
    rcases covers rest pattern h with h | h
    · exact .inl (.inr h)
    · exact .inr h
  | _, .unproven _ rest => by
    simp only [List.mem_cons, forall_eq_or_imp, unprovenPatterns, List.map_cons, true_or,
      or_true, true_and]
    intro pattern h
    rcases covers rest pattern h with h | h
    · exact .inl h
    · exact .inr (.inr h)

end Certificates

set_option maxRecDepth 100000 in
/-- A certificate for every pattern `riscv-combine` runs, in `combinePatternList` order. -/
def combineCertificates : Certificates combinePatternList :=
  .proven packh_low_bytes_valid <|
  .proven packh_low_bytes_commuted_valid <|
  .proven packh_high_bytes_valid <|
  .proven packh_high_bytes_commuted_valid <|
  .proven zextb_lbu_valid <|
  .proven andi_255_lbu_valid <|
  .proven add_li_to_addi_valid <|
  .proven add_li_to_addi_commuted_valid <|
  .proven zextw_slliw_lbu_8_valid <|
  .proven zextw_slliw_lbu_16_valid <|
  .proven zextw_slliw_lbu_24_valid <|
  .proven right_identity_zero_add_valid <|
  .proven srl_sra_signbit_valid <|
  .proven srlw_sraw_signbit_valid <|
  .proven drop_slli_srli_slt_valid <|
  .proven drop_slli_srli_sltu_valid <|
  .proven drop_slli_srli_slti_valid <|
  .proven drop_slli_srli_sltiu_valid <|
  .proven drop_slli_srli_seqz_valid <|
  .proven drop_slli_srli_snez_valid <|
  .proven drop_slli_srli_sltz_valid <|
  .proven drop_slli_srli_sgtz_valid <|
  .proven drop_andi_one_srli_valid <|
  .proven zextw_zextw_valid <|
  .proven zextw_zextb_valid <|
  .proven drop_sll_amount_mask_valid <|
  .proven drop_srl_amount_mask_valid <|
  .proven drop_sra_amount_mask_valid <|
  .proven drop_sllw_amount_mask_valid <|
  .proven drop_srlw_amount_mask_valid <|
  .proven drop_sraw_amount_mask_valid <|
  .proven drop_sll_amount_zextw_valid <|
  .proven drop_srl_amount_zextw_valid <|
  .proven drop_sra_amount_zextw_valid <|
  .proven drop_zextw_addw_rs1_valid <|
  .proven drop_zextw_addw_rs2_valid <|
  .proven drop_zextw_addiw_valid <|
  .proven drop_zextw_roriw_valid <|
  .proven drop_zextw_srliw_valid <|
  .proven drop_zextw_subw_rs1_valid <|
  .proven drop_zextw_subw_rs2_valid <|
  .proven drop_zextw_mulw_rs1_valid <|
  .proven drop_zextw_mulw_rs2_valid <|
  .proven drop_zextw_divw_rs1_valid <|
  .proven drop_zextw_divw_rs2_valid <|
  .proven drop_zextw_divuw_rs1_valid <|
  .proven drop_zextw_divuw_rs2_valid <|
  .proven drop_zextw_remw_rs1_valid <|
  .proven drop_zextw_remw_rs2_valid <|
  .proven drop_zextw_remuw_rs1_valid <|
  .proven drop_zextw_remuw_rs2_valid <|
  .proven drop_zextw_sllw_rs1_valid <|
  .proven drop_zextw_sllw_rs2_valid <|
  .proven drop_zextw_srlw_rs1_valid <|
  .proven drop_zextw_srlw_rs2_valid <|
  .proven drop_zextw_sraw_rs1_valid <|
  .proven drop_zextw_sraw_rs2_valid <|
  .proven drop_zextw_rolw_rs1_valid <|
  .proven drop_zextw_rolw_rs2_valid <|
  .proven drop_zextw_rorw_rs1_valid <|
  .proven drop_zextw_rorw_rs2_valid <|
  .proven drop_zextw_sraiw_valid <|
  .proven drop_zextw_slliuw_valid <|
  .proven drop_zextw_clzw_valid <|
  .proven drop_zextw_ctzw_valid <|
  .proven drop_zextw_cpopw_valid <|
  .proven drop_zextw_sextw_valid <|
  .proven zextw_and_lhs_valid <|
  .proven zextw_and_rhs_valid <|
  .proven zextw_or_valid <|
  .proven zextw_xor_valid <|
  .proven drop_zextw_sw_valid <|
  .proven zextw_x0_valid <|
  .proven zextw_li_low32_valid <|
  .proven sextw_sextw_valid <|
  .proven drop_sextw_addw_rs1_valid <|
  .proven drop_sextw_addw_rs2_valid <|
  .proven drop_sextw_addiw_valid <|
  .proven drop_sextw_roriw_valid <|
  .proven drop_sextw_srliw_valid <|
  .proven drop_sextw_subw_rs1_valid <|
  .proven drop_sextw_subw_rs2_valid <|
  .proven drop_sextw_mulw_rs1_valid <|
  .proven drop_sextw_mulw_rs2_valid <|
  .proven drop_sextw_divw_rs1_valid <|
  .proven drop_sextw_divw_rs2_valid <|
  .proven drop_sextw_divuw_rs1_valid <|
  .proven drop_sextw_divuw_rs2_valid <|
  .proven drop_sextw_remw_rs1_valid <|
  .proven drop_sextw_remw_rs2_valid <|
  .proven drop_sextw_remuw_rs1_valid <|
  .proven drop_sextw_remuw_rs2_valid <|
  .proven drop_sextw_sllw_rs1_valid <|
  .proven drop_sextw_sllw_rs2_valid <|
  .proven drop_sextw_srlw_rs1_valid <|
  .proven drop_sextw_srlw_rs2_valid <|
  .proven drop_sextw_sraw_rs1_valid <|
  .proven drop_sextw_sraw_rs2_valid <|
  .proven drop_sextw_rolw_rs1_valid <|
  .proven drop_sextw_rolw_rs2_valid <|
  .proven drop_sextw_rorw_rs1_valid <|
  .proven drop_sextw_rorw_rs2_valid <|
  .proven drop_sextw_sraiw_valid <|
  .proven drop_sextw_slliuw_valid <|
  .proven drop_sextw_clzw_valid <|
  .proven drop_sextw_ctzw_valid <|
  .proven drop_sextw_cpopw_valid <|
  .proven drop_sextw_zextw_valid <|
  .proven sextw_and_valid <|
  .proven sextw_or_valid <|
  .proven sextw_xor_valid <|
  .proven drop_sextw_sw_valid <|
  .proven sextw_x0_valid <|
  .proven sextw_li_low32_valid <|
  .proven sextw_lw_valid <|
  .proven sextw_lh_valid <|
  .proven sextw_lb_valid <|
  .proven sextw_lhu_valid <|
  .proven sextw_lbu_valid <|
  .proven sextw_addw_valid <|
  .proven sextw_addiw_valid <|
  .proven sextw_subw_valid <|
  .proven sextw_mulw_valid <|
  .proven sextw_divw_valid <|
  .proven sextw_divuw_valid <|
  .proven sextw_remw_valid <|
  .proven sextw_remuw_valid <|
  .proven sextw_sllw_valid <|
  .proven sextw_slliw_valid <|
  .proven sextw_srlw_valid <|
  .proven sextw_srliw_valid <|
  .proven sextw_sraw_valid <|
  .proven sextw_sraiw_valid <|
  .proven sextw_rolw_valid <|
  .proven sextw_rorw_valid <|
  .proven sextw_roriw_valid <|
  .proven sextw_clzw_valid <|
  .proven sextw_ctzw_valid <|
  .proven sextw_cpopw_valid <|
  .proven sextw_packw_valid <|
  .proven sextw_slt_valid <|
  .proven sextw_sltu_valid <|
  .proven sextw_slti_valid <|
  .proven sextw_sltiu_valid <|
  .proven sextw_clz_valid <|
  .proven sextw_ctz_valid <|
  .proven sextw_cpop_valid <|
  .proven sextw_bext_valid <|
  .proven sextw_bexti_valid <|
  .proven sextw_sextb_valid <|
  .proven sextw_sexth_valid <|
  .proven sextw_zexth_valid <|
  .proven sextw_packh_valid <|
  .proven sextw_lui_valid <|
  .proven sextw_srai_valid <|
  .proven sextw_srli_valid <|
  .proven sextw_andi_valid <|
  .proven sextw_ori_valid <|
  .proven zextb_zextb_valid <|
  .proven zexth_zexth_valid <|
  .proven sextb_sextb_valid <|
  .proven sexth_sexth_valid <|
  .proven zextb_and_lhs_valid <|
  .proven zextb_and_rhs_valid <|
  .proven zextb_or_valid <|
  .proven zextb_xor_valid <|
  .proven zexth_and_lhs_valid <|
  .proven zexth_and_rhs_valid <|
  .proven zexth_or_valid <|
  .proven zexth_xor_valid <|
  .proven sextb_and_valid <|
  .proven sextb_or_valid <|
  .proven sextb_xor_valid <|
  .proven sexth_and_valid <|
  .proven sexth_or_valid <|
  .proven sexth_xor_valid <|
  .proven drop_zexth_sh_valid <|
  .proven drop_sexth_sh_valid <|
  .proven drop_zextb_sb_valid <|
  .proven drop_sextb_sb_valid <|
  .proven drop_zextw_sb_valid <|
  .proven drop_sextw_sb_valid <|
  .proven zextb_x0_valid <|
  .proven zexth_x0_valid <|
  .proven sextb_x0_valid <|
  .proven sexth_x0_valid <|
  .proven zextb_li_low8_valid <|
  .proven zexth_li_low16_valid <|
  .proven sextb_li_low8_valid <|
  .proven sexth_li_low16_valid <|
  .proven li_zero_to_x0_valid <|
  .nil

/-- Every pattern `riscv-combine` runs is proven valid or recorded as unproven. -/
theorem combinePatternList_certified (pattern : Pattern OpCode) (h : pattern ∈ combinePatternList) :
    pattern ∈ combineCertificates.provenPatterns ∨
      pattern ∈ combineCertificates.unprovenPatterns.map Prod.fst :=
  combineCertificates.covers pattern h

/-- Every proven combine pattern satisfies the CTree validity predicate. -/
theorem combineCertificates_valid (pattern : Pattern OpCode)
    (h : pattern ∈ combineCertificates.provenPatterns) :
    Puddle.CTree.Pattern.Valid pattern :=
  combineCertificates.valid pattern h

/-- Every pattern `riscv-combine` runs satisfies the CTree validity predicate: no reason for a
pattern to be unproven exists. -/
theorem combinePatternList_valid (pattern : Pattern OpCode) (h : pattern ∈ combinePatternList) :
    Puddle.CTree.Pattern.Valid pattern := by
  rcases combinePatternList_certified pattern h with h | h
  · exact combineCertificates_valid pattern h
  · obtain ⟨⟨_, reason⟩, -, -⟩ := List.mem_map.mp h
    nomatch reason

end

end Veir.RISCV.CTreeProofs
