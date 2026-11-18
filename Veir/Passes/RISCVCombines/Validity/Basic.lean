module

import all Veir.Passes.RISCVCombines.Validity.Common
meta import Veir.Meta.ProofKind

/-! CTree validity proofs for the RISC-V combines: identities, shifts of booleans, redundant extensions, and immediates. -/

namespace Veir.RISCV.CTreeProofs

open Puddle
open _root_.CTree

set_option linter.unusedSimpArgs false

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Rv64.interpretOp'


@[proof_manual]
theorem right_identity_zero_add_valid :
    Puddle.CTree.Pattern.Valid (right_identity_zero_add_pattern) := by
  proveCombineValid using Data.RISCV.right_identity_zero_add

@[proof_bv]
theorem srl_sra_signbit_valid :
    Puddle.CTree.Pattern.Valid (srl_sra_signbitGen_pattern .srli rfl .srai 64) := by
  proveCombineValid using Data.RISCV.srl_sra_signbit

@[proof_bv]
theorem srlw_sraw_signbit_valid :
    Puddle.CTree.Pattern.Valid (srl_sra_signbitGen_pattern .srliw rfl .sraiw 32) := by
  proveCombineValid using Data.RISCV.srlw_sraw_signbit

@[proof_bv]
theorem drop_slli_srli_slt_valid :
    Puddle.CTree.Pattern.Valid (drop_slli_srli_boolGen_pattern .slt 2) := by
  proveCombineValid using Data.RISCV.drop_slli_srli_slt

@[proof_bv]
theorem drop_slli_srli_sltu_valid :
    Puddle.CTree.Pattern.Valid (drop_slli_srli_boolGen_pattern .sltu 2) := by
  proveCombineValid using Data.RISCV.drop_slli_srli_sltu

@[proof_bv]
theorem drop_slli_srli_slti_valid :
    Puddle.CTree.Pattern.Valid (drop_slli_srli_boolGen_pattern .slti 1) := by
  proveCombineValid using Data.RISCV.drop_slli_srli_slti

@[proof_bv]
theorem drop_slli_srli_sltiu_valid :
    Puddle.CTree.Pattern.Valid (drop_slli_srli_boolGen_pattern .sltiu 1) := by
  proveCombineValid using Data.RISCV.drop_slli_srli_sltiu

@[proof_bv]
theorem drop_slli_srli_seqz_valid :
    Puddle.CTree.Pattern.Valid (drop_slli_srli_boolGen_pattern .seqz 1) := by
  proveCombineValid using Data.RISCV.drop_slli_srli_seqz

@[proof_bv]
theorem drop_slli_srli_snez_valid :
    Puddle.CTree.Pattern.Valid (drop_slli_srli_boolGen_pattern .snez 1) := by
  proveCombineValid using Data.RISCV.drop_slli_srli_snez

@[proof_bv]
theorem drop_slli_srli_sltz_valid :
    Puddle.CTree.Pattern.Valid (drop_slli_srli_boolGen_pattern .sltz 1) := by
  proveCombineValid using Data.RISCV.drop_slli_srli_sltz

@[proof_bv]
theorem drop_slli_srli_sgtz_valid :
    Puddle.CTree.Pattern.Valid (drop_slli_srli_boolGen_pattern .sgtz 1) := by
  proveCombineValid using Data.RISCV.drop_slli_srli_sgtz

@[proof_bv]
theorem drop_andi_one_srli_valid :
    Puddle.CTree.Pattern.Valid (drop_andi_one_srli_pattern) := by
  proveCombineValid using Data.RISCV.drop_andi_one_srli

@[proof_bv]
theorem zextw_zextw_valid :
    Puddle.CTree.Pattern.Valid (drop_redundant_ext_pattern .zextw) := by
  proveCombineValid using Data.RISCV.zextw_zextw

@[proof_bv]
theorem sextw_sextw_valid :
    Puddle.CTree.Pattern.Valid (drop_redundant_ext_pattern .sextw) := by
  proveCombineValid using Data.RISCV.sextw_sextw

@[proof_bv]
theorem zextb_zextb_valid :
    Puddle.CTree.Pattern.Valid (drop_redundant_ext_pattern .zextb) := by
  proveCombineValid using Data.RISCV.zextb_zextb

@[proof_bv]
theorem zexth_zexth_valid :
    Puddle.CTree.Pattern.Valid (drop_redundant_ext_pattern .zexth) := by
  proveCombineValid using Data.RISCV.zexth_zexth

@[proof_bv]
theorem sextb_sextb_valid :
    Puddle.CTree.Pattern.Valid (drop_redundant_ext_pattern .sextb) := by
  proveCombineValid using Data.RISCV.sextb_sextb

@[proof_bv]
theorem sexth_sexth_valid :
    Puddle.CTree.Pattern.Valid (drop_redundant_ext_pattern .sexth) := by
  proveCombineValid using Data.RISCV.sexth_sexth

@[proof_bv]
theorem zextw_zextb_valid :
    Puddle.CTree.Pattern.Valid (zextw_zextb_pattern) := by
  proveCombineValid using Data.RISCV.zextw_zextb

@[proof_bv]
theorem add_li_to_addi_valid :
    Puddle.CTree.Pattern.Valid (add_li_to_addi_pattern false) := by
  proveCombineValid using Data.RISCV.add_li_to_addi

@[proof_bv]
theorem add_li_to_addi_commuted_valid :
    Puddle.CTree.Pattern.Valid (add_li_to_addi_pattern true) := by
  proveCombineValid using Data.RISCV.add_li_to_addi_commuted

@[proof_bv]
theorem and_li_to_zextw_valid :
    Puddle.CTree.Pattern.Valid (and_li_to_zextw_pattern false) := by
  proveCombineValid using Data.RISCV.and_li_to_zextw

@[proof_bv]
theorem and_li_to_zextw_commuted_valid :
    Puddle.CTree.Pattern.Valid (and_li_to_zextw_pattern true) := by
  proveCombineValid using Data.RISCV.and_li_to_zextw_commuted

@[proof_bv]
theorem zextw_li_low32_valid :
    Puddle.CTree.Pattern.Valid
      (ext_of_li_pattern .zextw fun cst => !decide (cst.value ≥ 4294967296#64)) := by
  proveCombineValid using Data.RISCV.zextw_li_low32

@[proof_bv]
theorem sextw_li_low32_valid :
    Puddle.CTree.Pattern.Valid (ext_of_li_pattern .sextw fun cst =>
      !decide (cst.value.toInt < -2147483648 ∨ cst.value.toInt ≥ 2147483648)) := by
  proveCombineValid using Data.RISCV.sextw_li_low32

@[proof_bv]
theorem zextb_li_low8_valid :
    Puddle.CTree.Pattern.Valid (ext_of_li_pattern .zextb fun cst =>
      !decide (cst.value.toInt < 0 ∨ cst.value.toInt ≥ 256)) := by
  proveCombineValid using Data.RISCV.zextb_li_low8

@[proof_bv]
theorem zexth_li_low16_valid :
    Puddle.CTree.Pattern.Valid (ext_of_li_pattern .zexth fun cst =>
      !decide (cst.value.toInt < 0 ∨ cst.value.toInt ≥ 65536)) := by
  proveCombineValid using Data.RISCV.zexth_li_low16

@[proof_bv]
theorem sextb_li_low8_valid :
    Puddle.CTree.Pattern.Valid (ext_of_li_pattern .sextb fun cst =>
      !decide (cst.value.toInt < (-128) ∨ cst.value.toInt ≥ 128)) := by
  proveCombineValid using Data.RISCV.sextb_li_low8

@[proof_bv]
theorem sexth_li_low16_valid :
    Puddle.CTree.Pattern.Valid (ext_of_li_pattern .sexth fun cst =>
      !decide (cst.value.toInt < (-32768) ∨ cst.value.toInt ≥ 32768)) := by
  proveCombineValid using Data.RISCV.sexth_li_low16

/-- The created `rv64.get_register` reads `x0`, whose value is zero. -/
@[proof_manual]
theorem li_zero_to_x0_valid :
    Puddle.CTree.Pattern.Valid li_zero_to_x0_pattern := by
  simp only [riscv_pattern]
  simpPuddleValid
  simpCombineSemantics
  normalizeCombineValid
  all_goals simp [TypeAttr.of, Attribute.of, liftM, monadLift, MonadLift.monadLift,
    RuntimeValue.isRefinedBy, ControlFlowAction.optionIsRefinedBy, Data.RISCV.li_zero_to_x0,
    -Attribute.registerType_eq_of]

/- The `riscv.<ext> x0 -> x0` combines (`ext_x0_pattern`) are valid only if every value of the
`x0` register type is zero. `RuntimeValue.Conforms` no longer states that invariant, because the
verifier does not stop other operations from producing `x0`-typed results, so these proofs are
disabled until the invariant is established elsewhere.

`riscv.<ext>` of `x0`, which reads as zero, is `x0`:

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
-/

end Veir.RISCV.CTreeProofs
