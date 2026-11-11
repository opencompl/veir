module

public import Veir.PatternRewriter.Puddle.CTreeValidity
public import Veir.PatternRewriter.Puddle.CTreeProofs
public import Veir.Passes.InstructionSelection.RISCV64
public import Veir.Passes.InstructionSelection.RISCV64Branches

import all Veir.Passes.InstructionSelection.RISCV64
import all Veir.Passes.InstructionSelection.RISCV64Branches

/-!
# CTree validity of the RISC-V 64 instruction selection

The statements of `Puddle.CTree.Pattern.Valid` for every Puddle pattern that `isel-riscv64` and
`isel-br-riscv64` run, in the order the passes try them, so that the whole pipeline from LLVM to
RISC-V has a certificate statement for each of its rewrites. None is proven yet: each is `sorry`,
to be closed with the local correctness lemmas of `Veir.Passes.InstructionSelection.Proofs`.

A pattern family the pass runs at several parameters, such as the loads at every addressing
mode, is stated once, quantified over the parameters the pass uses. The rewrites that are not
Puddle patterns have no statement: the local rewrites `splitLoad_local`, `splitStore_local`,
`memIntrinsicInline_local` and `getelementptrGeneral` of `isel-riscv64`, the branch lowering of
`isel-br-riscv64`, and `lowerReturn` and `lowerOp` of `isel-abi-riscv64`.
-/

namespace Veir.ISel.CTreeProofs

open Puddle

/-! ## Composed patterns (`gmirComposed`) -/

theorem binopNot_andn_valid (notLhs : Bool) :
    Puddle.CTree.Pattern.Valid (gmirBinopNot_pattern .g_and .andn () notLhs) := by
  sorry

theorem binopNot_orn_valid (notLhs : Bool) :
    Puddle.CTree.Pattern.Valid (gmirBinopNot_pattern .g_or .orn () notLhs) := by
  sorry

theorem binopNot_xnor_valid (notLhs : Bool) :
    Puddle.CTree.Pattern.Valid (gmirBinopNot_pattern .g_xor .xnor () notLhs) := by
  sorry

theorem orcb_valid (y : Nat) (hy : y < 8) : Puddle.CTree.Pattern.Valid (gmirOrcb_pattern y) := by
  sorry

theorem bexti_valid : Puddle.CTree.Pattern.Valid gmirBexti_pattern := by
  sorry

theorem slliuw_valid : Puddle.CTree.Pattern.Valid gmirSlliuw_pattern := by
  sorry

/-! ## Early patterns: intrinsics, memory accesses, selects of zero and immediates -/

theorem lifetime_start_valid : Puddle.CTree.Pattern.Valid (lowerLifetime .intr__lifetime__start) := by
  sorry

theorem lifetime_end_valid : Puddle.CTree.Pattern.Valid (lowerLifetime .intr__lifetime__end) := by
  sorry

theorem memcpy_call_valid : Puddle.CTree.Pattern.Valid (memIntrinsicCallPattern false) := by
  sorry

theorem memset_call_valid : Puddle.CTree.Pattern.Valid (memIntrinsicCallPattern true) := by
  sorry

theorem load_lbu_valid (mode : AddrMode) : Puddle.CTree.Pattern.Valid (lowerLoad mode 1 .lbu) := by
  sorry

theorem load_lh_valid (mode : AddrMode) : Puddle.CTree.Pattern.Valid (lowerLoad mode 2 .lh) := by
  sorry

theorem load_lw_valid (mode : AddrMode) : Puddle.CTree.Pattern.Valid (lowerLoad mode 4 .lw) := by
  sorry

theorem load_ld_valid (mode : AddrMode) : Puddle.CTree.Pattern.Valid (lowerLoad mode 8 .ld) := by
  sorry

theorem gmir_load_lbu_valid (mode : AddrMode) : Puddle.CTree.Pattern.Valid (gmirLoad_pattern mode 1 .lbu) := by
  sorry

theorem gmir_load_lh_valid (mode : AddrMode) : Puddle.CTree.Pattern.Valid (gmirLoad_pattern mode 2 .lh) := by
  sorry

theorem gmir_load_lw_valid (mode : AddrMode) : Puddle.CTree.Pattern.Valid (gmirLoad_pattern mode 4 .lw) := by
  sorry

theorem gmir_load_ld_valid (mode : AddrMode) : Puddle.CTree.Pattern.Valid (gmirLoad_pattern mode 8 .ld) := by
  sorry

theorem store_sb_valid (mode : AddrMode) : Puddle.CTree.Pattern.Valid (lowerStore mode 1 .sb) := by
  sorry

theorem store_sh_valid (mode : AddrMode) : Puddle.CTree.Pattern.Valid (lowerStore mode 2 .sh) := by
  sorry

theorem store_sw_valid (mode : AddrMode) : Puddle.CTree.Pattern.Valid (lowerStore mode 4 .sw) := by
  sorry

theorem store_sd_valid (mode : AddrMode) : Puddle.CTree.Pattern.Valid (lowerStore mode 8 .sd) := by
  sorry

theorem select_zero_of_setcc_eq_valid (zeroFalse zeroRhs : Bool) :
    Puddle.CTree.Pattern.Valid (gmirSelectZeroOfSetcc_pattern zeroFalse .eq zeroRhs) := by
  sorry

theorem select_zero_of_setcc_ne_valid (zeroFalse zeroRhs : Bool) :
    Puddle.CTree.Pattern.Valid (gmirSelectZeroOfSetcc_pattern zeroFalse .ne zeroRhs) := by
  sorry

theorem select_zero_valid (zeroFalse : Bool) : Puddle.CTree.Pattern.Valid (gmirSelectZero_pattern zeroFalse) := by
  sorry

theorem fshl_const_64_valid : Puddle.CTree.Pattern.Valid (lowerFshConst true 64) := by
  sorry

theorem fshl_const_32_valid : Puddle.CTree.Pattern.Valid (lowerFshConst true 32) := by
  sorry

theorem fshl_const_32_trunc_valid : Puddle.CTree.Pattern.Valid (lowerFshConst true 32 true) := by
  sorry

theorem fshr_const_64_valid : Puddle.CTree.Pattern.Valid (lowerFshConst false 64) := by
  sorry

theorem fshr_const_32_valid : Puddle.CTree.Pattern.Valid (lowerFshConst false 32) := by
  sorry

theorem fshr_const_32_trunc_valid : Puddle.CTree.Pattern.Valid (lowerFshConst false 32 true) := by
  sorry

theorem addi_valid : Puddle.CTree.Pattern.Valid gmirAddi_pattern := by
  sorry

theorem andi_valid : Puddle.CTree.Pattern.Valid gmirAndi_pattern := by
  sorry

theorem ori_valid : Puddle.CTree.Pattern.Valid gmirOri_pattern := by
  sorry

theorem xori_valid : Puddle.CTree.Pattern.Valid gmirXori_pattern := by
  sorry

theorem slli_valid : Puddle.CTree.Pattern.Valid gmirSlli_pattern := by
  sorry

theorem srli_valid : Puddle.CTree.Pattern.Valid gmirSrli_pattern := by
  sorry

theorem srai_valid : Puddle.CTree.Pattern.Valid gmirSrai_pattern := by
  sorry

theorem addiw_valid : Puddle.CTree.Pattern.Valid gmirRiscvAddiw_pattern := by
  sorry

theorem slliw_valid : Puddle.CTree.Pattern.Valid gmirRiscvSlliw_pattern := by
  sorry

theorem srliw_valid : Puddle.CTree.Pattern.Valid gmirRiscvSrliw_pattern := by
  sorry

theorem sraiw_valid : Puddle.CTree.Pattern.Valid gmirRiscvSraiw_pattern := by
  sorry

theorem cpopw_valid : Puddle.CTree.Pattern.Valid gmirCpopw_pattern := by
  sorry

theorem bseti_valid : Puddle.CTree.Pattern.Valid gmirBseti_pattern := by
  sorry

theorem binvi_valid : Puddle.CTree.Pattern.Valid gmirBinvi_pattern := by
  sorry

theorem bclri_valid : Puddle.CTree.Pattern.Valid gmirBclri_pattern := by
  sorry

theorem slti_valid (pred : Data.LLVM.IntPred)
    (hpred : pred ∈ [Data.LLVM.IntPred.slt, .ult, .sge, .uge, .sle, .ule]) :
    Puddle.CTree.Pattern.Valid (gmirSlti_pattern pred) := by
  sorry

/-! ## Main patterns: the per-operation lowerings -/

theorem select_valid : Puddle.CTree.Pattern.Valid gmirSelect_pattern := by
  sorry

theorem constant_valid : Puddle.CTree.Pattern.Valid constant_pattern := by
  sorry

theorem addressof_valid : Puddle.CTree.Pattern.Valid addressof_pattern := by
  sorry

theorem sext32_valid : Puddle.CTree.Pattern.Valid sext32_pattern := by
  sorry

theorem sext16_valid : Puddle.CTree.Pattern.Valid sext16_pattern := by
  sorry

theorem sext_inreg_8_valid : Puddle.CTree.Pattern.Valid (sextInRegExt_pattern 8 .sextb ()) := by
  sorry

theorem sext_inreg_16_valid : Puddle.CTree.Pattern.Valid (sextInRegExt_pattern 16 .sexth ()) := by
  sorry

theorem sext_inreg_32_valid : Puddle.CTree.Pattern.Valid (sextInRegExt_pattern 32 .sextw ()) := by
  sorry

theorem sext_inreg_shift_valid : Puddle.CTree.Pattern.Valid sextInRegShift_pattern := by
  sorry

theorem zext32_valid : Puddle.CTree.Pattern.Valid zext32_pattern := by
  sorry

theorem zext16_valid : Puddle.CTree.Pattern.Valid zext16_pattern := by
  sorry

theorem trunc_valid : Puddle.CTree.Pattern.Valid trunc_pattern := by
  sorry

theorem bitcast_valid : Puddle.CTree.Pattern.Valid bitcast_pattern := by
  sorry

theorem fshl64_valid : Puddle.CTree.Pattern.Valid fshl64_pattern := by
  sorry

theorem fshl32_valid : Puddle.CTree.Pattern.Valid fshl32_pattern := by
  sorry

theorem fshr64_valid : Puddle.CTree.Pattern.Valid fshr64_pattern := by
  sorry

theorem fshr32_valid : Puddle.CTree.Pattern.Valid fshr32_pattern := by
  sorry

theorem fshl_general_64_valid : Puddle.CTree.Pattern.Valid (lowerFshlGeneral 64) := by
  sorry

theorem fshl_general_32_valid : Puddle.CTree.Pattern.Valid (lowerFshlGeneral 32) := by
  sorry

theorem fshr_general_64_valid : Puddle.CTree.Pattern.Valid (lowerFshrGeneral 64) := by
  sorry

theorem fshr_general_32_valid : Puddle.CTree.Pattern.Valid (lowerFshrGeneral 32) := by
  sorry

theorem poison_const_valid : Puddle.CTree.Pattern.Valid poisonConst_pattern := by
  sorry

theorem zero_const_valid : Puddle.CTree.Pattern.Valid zeroConst_pattern := by
  sorry

theorem freeze_valid : Puddle.CTree.Pattern.Valid freeze_pattern := by
  sorry

theorem add_valid : Puddle.CTree.Pattern.Valid gmirAdd_pattern := by
  sorry

theorem sub_valid : Puddle.CTree.Pattern.Valid gmirSub_pattern := by
  sorry

theorem gmir_trunc_valid : Puddle.CTree.Pattern.Valid gmirTrunc_pattern := by
  sorry

theorem anyext_of_reg_valid : Puddle.CTree.Pattern.Valid gmirAnyextOfReg_pattern := by
  sorry

theorem anyext_valid : Puddle.CTree.Pattern.Valid gmirAnyext_pattern := by
  sorry

theorem shl_valid : Puddle.CTree.Pattern.Valid gmirShl_pattern := by
  sorry

theorem lshr_valid : Puddle.CTree.Pattern.Valid gmirLshr_pattern := by
  sorry

theorem ashr_valid : Puddle.CTree.Pattern.Valid gmirAshr_pattern := by
  sorry

theorem and_valid : Puddle.CTree.Pattern.Valid gmirAnd_pattern := by
  sorry

theorem or_valid : Puddle.CTree.Pattern.Valid gmirOr_pattern := by
  sorry

theorem xor_valid : Puddle.CTree.Pattern.Valid gmirXor_pattern := by
  sorry

theorem mul_valid : Puddle.CTree.Pattern.Valid gmirMul_pattern := by
  sorry

theorem sdiv_valid : Puddle.CTree.Pattern.Valid gmirSdiv_pattern := by
  sorry

theorem udiv_valid : Puddle.CTree.Pattern.Valid gmirUdiv_pattern := by
  sorry

theorem srem_valid : Puddle.CTree.Pattern.Valid gmirSrem_pattern := by
  sorry

theorem urem_valid : Puddle.CTree.Pattern.Valid gmirUrem_pattern := by
  sorry

theorem addw_valid : Puddle.CTree.Pattern.Valid gmirRiscvAddw_pattern := by
  sorry

theorem subw_valid : Puddle.CTree.Pattern.Valid gmirRiscvSubw_pattern := by
  sorry

theorem mulw_valid : Puddle.CTree.Pattern.Valid gmirRiscvMulw_pattern := by
  sorry

theorem divw_valid : Puddle.CTree.Pattern.Valid gmirRiscvDivw_pattern := by
  sorry

theorem divuw_valid : Puddle.CTree.Pattern.Valid gmirRiscvDivuw_pattern := by
  sorry

theorem remuw_valid : Puddle.CTree.Pattern.Valid gmirRiscvRemuw_pattern := by
  sorry

theorem sllw_valid : Puddle.CTree.Pattern.Valid gmirRiscvSllw_pattern := by
  sorry

theorem srlw_valid : Puddle.CTree.Pattern.Valid gmirRiscvSrlw_pattern := by
  sorry

theorem sraw_valid : Puddle.CTree.Pattern.Valid gmirRiscvSraw_pattern := by
  sorry

theorem clzw_valid : Puddle.CTree.Pattern.Valid gmirRiscvClzw_pattern := by
  sorry

theorem ctzw_valid : Puddle.CTree.Pattern.Valid gmirRiscvCtzw_pattern := by
  sorry

theorem gmir_constant_valid : Puddle.CTree.Pattern.Valid gmirConstant_pattern := by
  sorry

theorem ctlz_valid : Puddle.CTree.Pattern.Valid gmirCtlz_pattern := by
  sorry

theorem cttz_valid : Puddle.CTree.Pattern.Valid gmirCttz_pattern := by
  sorry

theorem ctpop_valid : Puddle.CTree.Pattern.Valid gmirCtpop_pattern := by
  sorry

theorem bswap_valid : Puddle.CTree.Pattern.Valid gmirBswap_pattern := by
  sorry

theorem brev8_valid : Puddle.CTree.Pattern.Valid gmirBrev8_pattern := by
  sorry

theorem bitreverse_valid : Puddle.CTree.Pattern.Valid gmirBitreverse_pattern := by
  sorry

theorem smax_valid : Puddle.CTree.Pattern.Valid gmirSmax_pattern := by
  sorry

theorem smin_valid : Puddle.CTree.Pattern.Valid gmirSmin_pattern := by
  sorry

theorem umax_valid : Puddle.CTree.Pattern.Valid gmirUmax_pattern := by
  sorry

theorem umin_valid : Puddle.CTree.Pattern.Valid gmirUmin_pattern := by
  sorry

/-- The `g_icmp` peepholes against zero, for `eq` and `ne`. -/
theorem icmp_zero_valid (pred : Data.LLVM.IntPred) (hpred : pred ∈ [Data.LLVM.IntPred.eq, .ne]) :
    Puddle.CTree.Pattern.Valid (gmirIcmp_pattern pred true) := by
  sorry

/-- The generic `g_icmp` lowering, for every predicate. -/
theorem icmp_valid (pred : Data.LLVM.IntPred) : Puddle.CTree.Pattern.Valid (gmirIcmp_pattern pred false) := by
  sorry

/-! ## Branches (`isel-br-riscv64`) -/

theorem unreachable_valid : Puddle.CTree.Pattern.Valid unreachable_pattern := by
  sorry

end Veir.ISel.CTreeProofs
