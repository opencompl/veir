module

import all Veir.Passes.RISCVCombines.Combine
import all Veir.Dialects.RISCV.Properties
import all Veir.GlobalOpInfo
import all Veir.Interpreter.CTreeInterpreter
import all Veir.Dialects.RISCV.Interpreter
import all Veir.Dialects.RISCV.InterpreterLemmas
import all Veir.Dialects.RV64.InterpreterLemmas
import Veir.PatternRewriter.Puddle.CTreeValidityTactics
import Veir.Passes.RISCVCombines.Simp

/-! # Correctness of the RISC-V combines -/

namespace Veir.RISCV.CTreeProofs

open Puddle
open _root_.CTree

attribute [local puddle]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Riscv.interpretOpCTree

attribute [local riscv_combine]
  RuntimeValue.isRefinedBy
  forall_riscvLoadCTree_canInterpretTo_ok
  _root_.Veir.RISCV.liFitsSImm12 RISCVImmediateProperties.immField
  rv64_interpretOp'_get_register


/-- Prove the validity of a combine pattern: unfold it, discharge the structural obligations,
normalize the semantics to register equalities under the matcher's guards, and bit-blast them.
The simp call is contextual, so that each guard rewrites the conclusion it guards. -/
macro "proveCombineValid" : tactic => `(tactic| (
  simp only [riscv_pattern]
  simpPuddleValid
  simp [puddle, riscv_combine]
  all_goals veir_bv_decide))

/-! ## Identities, booleans and immediates -/

/-- `riscv.add x (riscv.li 0) -> x` (`right_identity_zero_add`). The matcher fixes the
    materialized constant to `0#64`. -/
theorem right_identity_zero_add_valid :
    Puddle.CTree.Pattern.Valid (right_identity_zero_add_pattern) := by
  proveCombineValid

/-- `riscv.add x (riscv.li c) -> riscv.addi x c` (`add_li_to_addi`): the signed bounds from
    `liFitsSImm12` ensure that truncating `c` to 12 bits and sign-extending recovers `c`. -/
theorem add_li_to_addi_valid :
    Puddle.CTree.Pattern.Valid (add_li_to_addi_pattern false) := by
  proveCombineValid

/-- `riscv.add (riscv.li c) x -> riscv.addi x c` (`add_li_to_addi_commuted`). -/
theorem add_li_to_addi_commuted_valid :
    Puddle.CTree.Pattern.Valid (add_li_to_addi_pattern true) := by
  proveCombineValid

/-- `riscv.and (riscv.li 0xffffffff) x -> riscv.zextw x` (`and_li_to_zextw`): both sides retain
    bits 31:0 and clear bits 63:32. -/
theorem and_li_to_zextw_valid :
    Puddle.CTree.Pattern.Valid (and_li_to_zextw_pattern false) := by
  proveCombineValid

/-- The other operand order matched by `and_li_to_zextw_commuted`. -/
theorem and_li_to_zextw_commuted_valid :
    Puddle.CTree.Pattern.Valid (and_li_to_zextw_pattern true) := by
  proveCombineValid

/-- The created `rv64.get_register` reads `x0`, whose value is zero. -/
theorem li_zero_to_x0_valid :
    Puddle.CTree.Pattern.Valid li_zero_to_x0_pattern := by
  proveCombineValid

/-! ## Shift amounts

A shift reads only the low bits of its amount (SSA operand 1): six for the 64-bit shifts, five
for the word shifts. Masking the amount with `andi` (under the guard of
`drop_shift_amount_mask_pattern`) or zero-extending it with `zextw` leaves those bits unchanged. -/

theorem drop_sll_amount_mask_valid :
    Puddle.CTree.Pattern.Valid (drop_shift_amount_mask_pattern .sll 63) := by
  proveCombineValid

theorem drop_srl_amount_mask_valid :
    Puddle.CTree.Pattern.Valid (drop_shift_amount_mask_pattern .srl 63) := by
  proveCombineValid

theorem drop_sra_amount_mask_valid :
    Puddle.CTree.Pattern.Valid (drop_shift_amount_mask_pattern .sra 63) := by
  proveCombineValid

theorem drop_sllw_amount_mask_valid :
    Puddle.CTree.Pattern.Valid (drop_shift_amount_mask_pattern .sllw 31) := by
  proveCombineValid

theorem drop_srlw_amount_mask_valid :
    Puddle.CTree.Pattern.Valid (drop_shift_amount_mask_pattern .srlw 31) := by
  proveCombineValid

theorem drop_sraw_amount_mask_valid :
    Puddle.CTree.Pattern.Valid (drop_shift_amount_mask_pattern .sraw 31) := by
  proveCombineValid

theorem drop_sll_amount_zextw_valid :
    Puddle.CTree.Pattern.Valid (drop_zextw_shift_amount_pattern .sll) := by
  proveCombineValid

theorem drop_srl_amount_zextw_valid :
    Puddle.CTree.Pattern.Valid (drop_zextw_shift_amount_pattern .srl) := by
  proveCombineValid

theorem drop_sra_amount_zextw_valid :
    Puddle.CTree.Pattern.Valid (drop_zextw_shift_amount_pattern .sra) := by
  proveCombineValid

theorem drop_zextw_sllw_rs2_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .sllw 2 1) := by
  proveCombineValid

theorem drop_zextw_srlw_rs2_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .srlw 2 1) := by
  proveCombineValid

theorem drop_zextw_sraw_rs2_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .sraw 2 1) := by
  proveCombineValid

/--
  `riscv.srli 63 (riscv.srai _ x) -> riscv.srli 63 x` (`srl_sra_signbit`): an arithmetic right
  shift by any amount never changes the top bit, so a subsequent logical shift by 63 (which keeps
  only that bit) gives the same result as skipping the `srai` entirely. Mirrors LLVM's generic
  `DAGCombiner::visitSRL` rule `fold (srl (sra X, Y), 31) -> (srl X, 31)`.
  https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/CodeGen/SelectionDAG/DAGCombiner.cpp#L11628-L11633
-/
theorem srl_sra_signbit_valid :
    Puddle.CTree.Pattern.Valid (srl_sra_signbitGen_pattern .srli rfl .srai 64) := by
  proveCombineValid

/-- The `i32` analogue of `srl_sra_signbit`, at bit 31 (`srlw_sraw_signbit`). -/
theorem srlw_sraw_signbit_valid :
    Puddle.CTree.Pattern.Valid (srl_sra_signbitGen_pattern .srliw rfl .sraiw 32) := by
  proveCombineValid

/-!
  The `drop_slli_srli_boolGen` family: for a comparison op producing exactly 0 or 1,
  `riscv.slli 63` isolates its bit 0 into bit 63 and `riscv.srli 63` moves it straight back, so
  the round trip is the identity and both shifts can be dropped entirely.
-/

theorem drop_slli_srli_slt_valid :
    Puddle.CTree.Pattern.Valid (drop_slli_srli_boolGen_pattern .slt 2) := by
  proveCombineValid

theorem drop_slli_srli_sltu_valid :
    Puddle.CTree.Pattern.Valid (drop_slli_srli_boolGen_pattern .sltu 2) := by
  proveCombineValid

theorem drop_slli_srli_slti_valid :
    Puddle.CTree.Pattern.Valid (drop_slli_srli_boolGen_pattern .slti 1) := by
  proveCombineValid

theorem drop_slli_srli_sltiu_valid :
    Puddle.CTree.Pattern.Valid (drop_slli_srli_boolGen_pattern .sltiu 1) := by
  proveCombineValid

theorem drop_slli_srli_seqz_valid :
    Puddle.CTree.Pattern.Valid (drop_slli_srli_boolGen_pattern .seqz 1) := by
  proveCombineValid

theorem drop_slli_srli_snez_valid :
    Puddle.CTree.Pattern.Valid (drop_slli_srli_boolGen_pattern .snez 1) := by
  proveCombineValid

theorem drop_slli_srli_sltz_valid :
    Puddle.CTree.Pattern.Valid (drop_slli_srli_boolGen_pattern .sltz 1) := by
  proveCombineValid

theorem drop_slli_srli_sgtz_valid :
    Puddle.CTree.Pattern.Valid (drop_slli_srli_boolGen_pattern .sgtz 1) := by
  proveCombineValid

/-- `riscv.andi 1 (riscv.srli 63 x) -> riscv.srli 63 x` (`drop_andi_one_srli`): `srli 63` leaves
    only bit 0, so masking it with 1 changes nothing. -/
theorem drop_andi_one_srli_valid :
    Puddle.CTree.Pattern.Valid (drop_andi_one_srli_pattern) := by
  proveCombineValid

/-! ## Redundant extensions -/

/-- Each extension is idempotent (`drop_redundant_ext`): the inner extension already establishes
    the high-bit pattern the outer one would. -/
theorem zextw_zextw_valid :
    Puddle.CTree.Pattern.Valid (drop_redundant_ext_pattern .zextw) := by
  proveCombineValid

theorem sextw_sextw_valid :
    Puddle.CTree.Pattern.Valid (drop_redundant_ext_pattern .sextw) := by
  proveCombineValid

theorem zextb_zextb_valid :
    Puddle.CTree.Pattern.Valid (drop_redundant_ext_pattern .zextb) := by
  proveCombineValid

theorem zexth_zexth_valid :
    Puddle.CTree.Pattern.Valid (drop_redundant_ext_pattern .zexth) := by
  proveCombineValid

theorem sextb_sextb_valid :
    Puddle.CTree.Pattern.Valid (drop_redundant_ext_pattern .sextb) := by
  proveCombineValid

theorem sexth_sexth_valid :
    Puddle.CTree.Pattern.Valid (drop_redundant_ext_pattern .sexth) := by
  proveCombineValid

/-- A byte zero-extension is already a word zero-extension (`zextw_zextb`). -/
theorem zextw_zextb_valid :
    Puddle.CTree.Pattern.Valid (zextw_zextb_pattern) := by
  proveCombineValid

/-! ## Extensions of materialized constants

`riscv.<ext> (riscv.li c) -> riscv.li c` when the matcher's range guard on `c` holds: for a
zero-extension the unsigned range below `2^width`, for a sign-extension the signed range
`[-2^(width-1), 2^(width-1))`. -/

theorem zextw_li_low32_valid :
    Puddle.CTree.Pattern.Valid
      (ext_of_li_pattern .zextw fun cst => !decide (cst.value ≥ 4294967296#64)) := by
  proveCombineValid

theorem sextw_li_low32_valid :
    Puddle.CTree.Pattern.Valid (ext_of_li_pattern .sextw fun cst =>
      !decide (cst.value.toInt < -2147483648 ∨ cst.value.toInt ≥ 2147483648)) := by
  proveCombineValid

theorem zextb_li_low8_valid :
    Puddle.CTree.Pattern.Valid (ext_of_li_pattern .zextb fun cst =>
      !decide (cst.value.toInt < 0 ∨ cst.value.toInt ≥ 256)) := by
  proveCombineValid

theorem zexth_li_low16_valid :
    Puddle.CTree.Pattern.Valid (ext_of_li_pattern .zexth fun cst =>
      !decide (cst.value.toInt < 0 ∨ cst.value.toInt ≥ 65536)) := by
  proveCombineValid

theorem sextb_li_low8_valid :
    Puddle.CTree.Pattern.Valid (ext_of_li_pattern .sextb fun cst =>
      !decide (cst.value.toInt < (-128) ∨ cst.value.toInt ≥ 128)) := by
  proveCombineValid

theorem sexth_li_low16_valid :
    Puddle.CTree.Pattern.Valid (ext_of_li_pattern .sexth fun cst =>
      !decide (cst.value.toInt < (-32768) ∨ cst.value.toInt ≥ 32768)) := by
  proveCombineValid

section


/-! ## Byte-load and byte-packing combines.

    A load returns the bytes it read, extended to a register: `lbu` the byte `x`
    zero-extended, `⟨x.setWidth 64⟩`. These combines reuse the load results without
    moving or recreating memory accesses. -/

/-- `zextb (lbu x) = lbu x`: an unsigned byte load is already zero-extended. -/
theorem zextb_lbu_valid : Puddle.CTree.Pattern.Valid (zextb_lbu_pattern) := by
  proveCombineValid

/-- `andi 255 (lbu x) = lbu x`: an unsigned byte load is already masked. -/
theorem andi_255_lbu_valid : Puddle.CTree.Pattern.Valid (andi_255_lbu_pattern) := by
  proveCombineValid

/-- The byte-packing pre-canonicalization is valid for each selected shift:
    a word shift of a zero-extended byte, followed by `zextw`, is the same as
    the corresponding full-width shift. -/
theorem zextw_slliw_lbu_8_valid : Puddle.CTree.Pattern.Valid (zextw_slliw_lbu_pattern 8) := by
  proveCombineValid

theorem zextw_slliw_lbu_16_valid : Puddle.CTree.Pattern.Valid (zextw_slliw_lbu_pattern 16) := by
  proveCombineValid

theorem zextw_slliw_lbu_24_valid : Puddle.CTree.Pattern.Valid (zextw_slliw_lbu_pattern 24) := by
  proveCombineValid

/-- `or (lbu lo) (slli (lbu hi), 8) -> packh lo hi`. -/

theorem packh_low_bytes_valid : Puddle.CTree.Pattern.Valid (packh_low_bytes_pattern false) := by
  proveCombineValid

/-- `or (slli (lbu hi), 8) (lbu lo) -> packh lo hi`. -/
theorem packh_low_bytes_commuted_valid : Puddle.CTree.Pattern.Valid (packh_low_bytes_pattern true) := by
  proveCombineValid

/-- `or (slli (lbu b2), 16) (slli (lbu b3), 24) -> slli (packh b2 b3), 16`. -/

theorem packh_high_bytes_valid : Puddle.CTree.Pattern.Valid (packh_high_bytes_pattern false) := by
  proveCombineValid

/-- `or (slli (lbu b3), 24) (slli (lbu b2), 16) -> slli (packh b2 b3), 16`. -/
theorem packh_high_bytes_commuted_valid : Puddle.CTree.Pattern.Valid (packh_high_bytes_pattern true) := by
  proveCombineValid

/-! ## `sextw` of a load

    A signed load sign-extends its value to the register and an unsigned one zero-extends it, so
    the value is already a sign-extended word. -/

theorem sextw_lw_valid (h : IsSignExtendingOpW .lw 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .lw 1 _ h) := by
  proveCombineValid

theorem sextw_lh_valid (h : IsSignExtendingOpW .lh 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .lh 1 _ h) := by
  proveCombineValid

theorem sextw_lb_valid (h : IsSignExtendingOpW .lb 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .lb 1 _ h) := by
  proveCombineValid

theorem sextw_lhu_valid (h : IsSignExtendingOpW .lhu 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .lhu 1 _ h) := by
  proveCombineValid

theorem sextw_lbu_valid (h : IsSignExtendingOpW .lbu 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .lbu 1 _ h) := by
  proveCombineValid

end

/-! ## Extensions of bitwise operations

`riscv.<ext> (riscv.<op> a b) -> riscv.<op> a b` when the guarded operands already carry the
extension's high-bit pattern. `and` under a zero-extension needs only one guarded operand (SSA
`lhs` or `rhs`); every other combination needs both. -/

theorem zextw_and_lhs_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .zextw .and true false) := by
  proveCombineValid

theorem zextw_and_rhs_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .zextw .and false true) := by
  proveCombineValid

theorem zextw_or_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .zextw .or true true) := by
  proveCombineValid

theorem zextw_xor_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .zextw .xor true true) := by
  proveCombineValid

theorem zextb_and_lhs_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .zextb .and true false) := by
  proveCombineValid

theorem zextb_and_rhs_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .zextb .and false true) := by
  proveCombineValid

theorem zextb_or_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .zextb .or true true) := by
  proveCombineValid

theorem zextb_xor_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .zextb .xor true true) := by
  proveCombineValid

theorem zexth_and_lhs_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .zexth .and true false) := by
  proveCombineValid

theorem zexth_and_rhs_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .zexth .and false true) := by
  proveCombineValid

theorem zexth_or_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .zexth .or true true) := by
  proveCombineValid

theorem zexth_xor_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .zexth .xor true true) := by
  proveCombineValid

theorem sextw_and_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .sextw .and true true) := by
  proveCombineValid

theorem sextw_or_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .sextw .or true true) := by
  proveCombineValid

theorem sextw_xor_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .sextw .xor true true) := by
  proveCombineValid

theorem sextb_and_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .sextb .and true true) := by
  proveCombineValid

theorem sextb_or_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .sextb .or true true) := by
  proveCombineValid

theorem sextb_xor_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .sextb .xor true true) := by
  proveCombineValid

theorem sexth_and_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .sexth .and true true) := by
  proveCombineValid

theorem sexth_or_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .sexth .or true true) := by
  proveCombineValid

theorem sexth_xor_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .sexth .xor true true) := by
  proveCombineValid

/-! ## Extensions of a stored value

A word store (`sw`) writes the first four little-endian bytes of its value register, a halfword
store (`sh`) two and a byte store (`sb`) one (see the store cases of `Riscv.interpretOp'`). Each
extension below leaves those bytes unchanged. -/

/-- Prove the validity of a store combine, given a proof `bytes` that the dropped extension
does not change the stored bytes, usually `by veir_bv_decide`. -/
macro "proveStoreValid" bytes:term : tactic => `(tactic| (
  simp only [riscv_pattern]
  simpPuddleValid
  simp [puddle, riscv_combine]
  all_goals
    intros
    exact store_pure_store _
      (by simp [RuntimeValue.arrayIsRefinedBy_refl, ControlFlowAction.optionIsRefinedBy])
      _ _ _ _ _ _ _ $bytes))

theorem drop_zextw_sw_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_store_pattern .zextw .sw) := by
  proveStoreValid (by veir_bv_decide)

theorem drop_sextw_sw_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_store_pattern .sextw .sw) := by
  proveStoreValid (by veir_bv_decide)

theorem drop_zexth_sh_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_store_pattern .zexth .sh) := by
  proveStoreValid (by veir_bv_decide)

theorem drop_sexth_sh_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_store_pattern .sexth .sh) := by
  proveStoreValid (by veir_bv_decide)

theorem drop_zextb_sb_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_store_pattern .zextb .sb) := by
  proveStoreValid (by veir_bv_decide)

theorem drop_sextb_sb_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_store_pattern .sextb .sb) := by
  proveStoreValid (by veir_bv_decide)

theorem drop_zextw_sb_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_store_pattern .zextw .sb) := by
  proveStoreValid (by veir_bv_decide)

theorem drop_sextw_sb_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_store_pattern .sextw .sb) := by
  proveStoreValid (by veir_bv_decide)

/-! ## Extensions of `x0`

`riscv.<ext> x0 -> x0` (`ext_x0_pattern`) is valid only if every value of the
`x0` register type is zero. `RuntimeValue.Conforms` no longer states that invariant, because the
verifier does not stop other operations from producing `x0`-typed results, so the proofs are
disabled until the invariant is established elsewhere.

We leave these as axioms for now. -/

axiom zextw_x0_valid : Puddle.CTree.Pattern.Valid (ext_x0_pattern .zextw)

axiom sextw_x0_valid : Puddle.CTree.Pattern.Valid (ext_x0_pattern .sextw)

axiom zextb_x0_valid : Puddle.CTree.Pattern.Valid (ext_x0_pattern .zextb)

axiom zexth_x0_valid : Puddle.CTree.Pattern.Valid (ext_x0_pattern .zexth)

axiom sextb_x0_valid : Puddle.CTree.Pattern.Valid (ext_x0_pattern .sextb)

axiom sexth_x0_valid : Puddle.CTree.Pattern.Valid (ext_x0_pattern .sexth)

/-! ## `sextw` of a sign-extending producer

`riscv.sextw (op …) -> op …` (`sextw_signExtendingOpW`) when `op` already returns a sign-extended
32-bit value. -/

theorem sextw_addw_valid (h : IsSignExtendingOpW .addw 2 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .addw 2 _ h) := by
  proveCombineValid

theorem sextw_addiw_valid (h : IsSignExtendingOpW .addiw 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .addiw 1 _ h) := by
  proveCombineValid

theorem sextw_subw_valid (h : IsSignExtendingOpW .subw 2 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .subw 2 _ h) := by
  proveCombineValid

theorem sextw_mulw_valid (h : IsSignExtendingOpW .mulw 2 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .mulw 2 _ h) := by
  proveCombineValid

theorem sextw_divw_valid (h : IsSignExtendingOpW .divw 2 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .divw 2 _ h) := by
  proveCombineValid

theorem sextw_divuw_valid (h : IsSignExtendingOpW .divuw 2 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .divuw 2 _ h) := by
  proveCombineValid

theorem sextw_remw_valid (h : IsSignExtendingOpW .remw 2 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .remw 2 _ h) := by
  proveCombineValid

theorem sextw_remuw_valid (h : IsSignExtendingOpW .remuw 2 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .remuw 2 _ h) := by
  proveCombineValid

theorem sextw_sllw_valid (h : IsSignExtendingOpW .sllw 2 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .sllw 2 _ h) := by
  proveCombineValid

theorem sextw_slliw_valid (h : IsSignExtendingOpW .slliw 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .slliw 1 _ h) := by
  proveCombineValid

theorem sextw_srlw_valid (h : IsSignExtendingOpW .srlw 2 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .srlw 2 _ h) := by
  proveCombineValid

theorem sextw_srliw_valid (h : IsSignExtendingOpW .srliw 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .srliw 1 _ h) := by
  proveCombineValid

theorem sextw_sraw_valid (h : IsSignExtendingOpW .sraw 2 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .sraw 2 _ h) := by
  proveCombineValid

theorem sextw_sraiw_valid (h : IsSignExtendingOpW .sraiw 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .sraiw 1 _ h) := by
  proveCombineValid

theorem sextw_rolw_valid (h : IsSignExtendingOpW .rolw 2 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .rolw 2 _ h) := by
  proveCombineValid

theorem sextw_rorw_valid (h : IsSignExtendingOpW .rorw 2 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .rorw 2 _ h) := by
  proveCombineValid

theorem sextw_roriw_valid (h : IsSignExtendingOpW .roriw 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .roriw 1 _ h) := by
  proveCombineValid

theorem sextw_packw_valid (h : IsSignExtendingOpW .packw 2 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .packw 2 _ h) := by
  proveCombineValid

theorem sextw_lui_valid (h : IsSignExtendingOpW .lui 0 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .lui 0 _ h) := by
  proveCombineValid

theorem sextw_cpop_valid (h : IsSignExtendingOpW .cpop 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .cpop 1 _ h) := by
  proveCombineValid

theorem sextw_cpopw_valid (h : IsSignExtendingOpW .cpopw 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .cpopw 1 _ h) := by
  proveCombineValid

theorem sextw_clz_valid (h : IsSignExtendingOpW .clz 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .clz 1 _ h) := by
  proveCombineValid

theorem sextw_clzw_valid (h : IsSignExtendingOpW .clzw 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .clzw 1 _ h) := by
  proveCombineValid

theorem sextw_ctz_valid (h : IsSignExtendingOpW .ctz 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .ctz 1 _ h) := by
  proveCombineValid

theorem sextw_ctzw_valid (h : IsSignExtendingOpW .ctzw 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .ctzw 1 _ h) := by
  proveCombineValid

theorem sextw_slt_valid (h : IsSignExtendingOpW .slt 2 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .slt 2 _ h) := by
  proveCombineValid

theorem sextw_sltu_valid (h : IsSignExtendingOpW .sltu 2 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .sltu 2 _ h) := by
  proveCombineValid

theorem sextw_slti_valid (h : IsSignExtendingOpW .slti 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .slti 1 _ h) := by
  proveCombineValid

theorem sextw_sltiu_valid (h : IsSignExtendingOpW .sltiu 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .sltiu 1 _ h) := by
  proveCombineValid

theorem sextw_bext_valid (h : IsSignExtendingOpW .bext 2 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .bext 2 _ h) := by
  proveCombineValid

theorem sextw_bexti_valid (h : IsSignExtendingOpW .bexti 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .bexti 1 _ h) := by
  proveCombineValid

theorem sextw_sextb_valid (h : IsSignExtendingOpW .sextb 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .sextb 1 _ h) := by
  proveCombineValid

theorem sextw_sexth_valid (h : IsSignExtendingOpW .sexth 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .sexth 1 _ h) := by
  proveCombineValid

theorem sextw_zexth_valid (h : IsSignExtendingOpW .zexth 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .zexth 1 _ h) := by
  proveCombineValid

theorem sextw_packh_valid (h : IsSignExtendingOpW .packh 2 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .packh 2 _ h) := by
  proveCombineValid

theorem sextw_srai_valid
    (h : IsSignExtendingOpW .srai 1 (fun p => 32#6 ≤ p.immField 6)) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .srai 1 _ h) := by
  proveCombineValid

theorem sextw_srli_valid
    (h : IsSignExtendingOpW .srli 1 (fun p => 32#6 < p.immField 6)) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .srli 1 _ h) := by
  proveCombineValid

theorem sextw_andi_valid
    (h : IsSignExtendingOpW .andi 1 (fun p => !(p.immField 12).msb)) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .andi 1 _ h) := by
  proveCombineValid

theorem sextw_ori_valid
    (h : IsSignExtendingOpW .ori 1 (fun p => (p.immField 12).msb)) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .ori 1 _ h) := by
  proveCombineValid

/-! ## Extensions of an operand the consumer ignores

`riscv.<dst> (riscv.<ext> x) … -> riscv.<dst> x …` (`drop_ext_low_word`): the consumer reads only
operand bits 31:0, which `zextw` and `sextw` leave unchanged. `_rs1` and `_rs2` name the extended
SSA operand of a binary consumer. The amount (`rs2`) cases of `sllw`/`srlw`/`sraw` under `zextw`
are proved with the shift amounts above. -/

theorem drop_zextw_addw_rs1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .addw 2 0) := by
  proveCombineValid

theorem drop_zextw_addw_rs2_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .addw 2 1) := by
  proveCombineValid

theorem drop_zextw_addiw_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .addiw 1 0) := by
  proveCombineValid

theorem drop_zextw_roriw_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .roriw 1 0) := by
  proveCombineValid

theorem drop_zextw_srliw_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .srliw 1 0) := by
  proveCombineValid

theorem drop_zextw_subw_rs1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .subw 2 0) := by
  proveCombineValid

theorem drop_zextw_subw_rs2_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .subw 2 1) := by
  proveCombineValid

theorem drop_zextw_mulw_rs1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .mulw 2 0) := by
  proveCombineValid

theorem drop_zextw_mulw_rs2_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .mulw 2 1) := by
  proveCombineValid

theorem drop_zextw_divw_rs1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .divw 2 0) := by
  proveCombineValid

theorem drop_zextw_divw_rs2_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .divw 2 1) := by
  proveCombineValid

theorem drop_zextw_divuw_rs1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .divuw 2 0) := by
  proveCombineValid

theorem drop_zextw_divuw_rs2_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .divuw 2 1) := by
  proveCombineValid

theorem drop_zextw_remw_rs1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .remw 2 0) := by
  proveCombineValid

theorem drop_zextw_remw_rs2_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .remw 2 1) := by
  proveCombineValid

theorem drop_zextw_remuw_rs1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .remuw 2 0) := by
  proveCombineValid

theorem drop_zextw_remuw_rs2_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .remuw 2 1) := by
  proveCombineValid

theorem drop_zextw_sllw_rs1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .sllw 2 0) := by
  proveCombineValid

theorem drop_zextw_srlw_rs1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .srlw 2 0) := by
  proveCombineValid

theorem drop_zextw_sraw_rs1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .sraw 2 0) := by
  proveCombineValid

theorem drop_zextw_rolw_rs1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .rolw 2 0) := by
  proveCombineValid

theorem drop_zextw_rolw_rs2_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .rolw 2 1) := by
  proveCombineValid

theorem drop_zextw_rorw_rs1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .rorw 2 0) := by
  proveCombineValid

theorem drop_zextw_rorw_rs2_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .rorw 2 1) := by
  proveCombineValid

theorem drop_zextw_sraiw_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .sraiw 1 0) := by
  proveCombineValid

theorem drop_zextw_slliuw_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .slliuw 1 0) := by
  proveCombineValid

theorem drop_zextw_clzw_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .clzw 1 0) := by
  proveCombineValid

theorem drop_zextw_ctzw_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .ctzw 1 0) := by
  proveCombineValid

theorem drop_zextw_cpopw_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .cpopw 1 0) := by
  proveCombineValid

theorem drop_zextw_sextw_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .zextw .sextw 1 0) := by
  proveCombineValid

theorem drop_sextw_addw_rs1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .addw 2 0) := by
  proveCombineValid

theorem drop_sextw_addw_rs2_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .addw 2 1) := by
  proveCombineValid

theorem drop_sextw_addiw_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .addiw 1 0) := by
  proveCombineValid

theorem drop_sextw_roriw_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .roriw 1 0) := by
  proveCombineValid

theorem drop_sextw_srliw_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .srliw 1 0) := by
  proveCombineValid

theorem drop_sextw_subw_rs1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .subw 2 0) := by
  proveCombineValid

theorem drop_sextw_subw_rs2_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .subw 2 1) := by
  proveCombineValid

theorem drop_sextw_mulw_rs1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .mulw 2 0) := by
  proveCombineValid

theorem drop_sextw_mulw_rs2_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .mulw 2 1) := by
  proveCombineValid

theorem drop_sextw_divw_rs1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .divw 2 0) := by
  proveCombineValid

theorem drop_sextw_divw_rs2_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .divw 2 1) := by
  proveCombineValid

theorem drop_sextw_divuw_rs1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .divuw 2 0) := by
  proveCombineValid

theorem drop_sextw_divuw_rs2_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .divuw 2 1) := by
  proveCombineValid

theorem drop_sextw_remw_rs1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .remw 2 0) := by
  proveCombineValid

theorem drop_sextw_remw_rs2_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .remw 2 1) := by
  proveCombineValid

theorem drop_sextw_remuw_rs1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .remuw 2 0) := by
  proveCombineValid

theorem drop_sextw_remuw_rs2_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .remuw 2 1) := by
  proveCombineValid

theorem drop_sextw_sllw_rs1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .sllw 2 0) := by
  proveCombineValid

theorem drop_sextw_sllw_rs2_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .sllw 2 1) := by
  proveCombineValid

theorem drop_sextw_srlw_rs1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .srlw 2 0) := by
  proveCombineValid

theorem drop_sextw_srlw_rs2_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .srlw 2 1) := by
  proveCombineValid

theorem drop_sextw_sraw_rs1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .sraw 2 0) := by
  proveCombineValid

theorem drop_sextw_sraw_rs2_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .sraw 2 1) := by
  proveCombineValid

theorem drop_sextw_rolw_rs1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .rolw 2 0) := by
  proveCombineValid

theorem drop_sextw_rolw_rs2_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .rolw 2 1) := by
  proveCombineValid

theorem drop_sextw_rorw_rs1_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .rorw 2 0) := by
  proveCombineValid

theorem drop_sextw_rorw_rs2_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .rorw 2 1) := by
  proveCombineValid

theorem drop_sextw_sraiw_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .sraiw 1 0) := by
  proveCombineValid

theorem drop_sextw_slliuw_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .slliuw 1 0) := by
  proveCombineValid

theorem drop_sextw_clzw_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .clzw 1 0) := by
  proveCombineValid

theorem drop_sextw_ctzw_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .ctzw 1 0) := by
  proveCombineValid

theorem drop_sextw_cpopw_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .cpopw 1 0) := by
  proveCombineValid

theorem drop_sextw_zextw_valid :
    Puddle.CTree.Pattern.Valid (drop_unary_operand_pattern .sextw .zextw 1 0) := by
  proveCombineValid

end Veir.RISCV.CTreeProofs
