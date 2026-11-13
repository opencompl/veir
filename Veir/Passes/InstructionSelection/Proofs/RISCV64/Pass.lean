module

public import Veir.Passes.InstructionSelection.RISCV64
public import Veir.Passes.Pipeline.Soundness
import all Veir.Passes.InstructionSelection.RISCV64
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Arithmetic
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.BitManipulation
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Bitwise
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Casts
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Comparisons
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Constants
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.GMIRFoldedLoads
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.GMIRLoads
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Loads
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Memory
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Rotates
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Selects
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Shifts
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.StorePatterns

/-!
# Soundness of the `isel-riscv64` pass

Every pattern of the three selection loops is valid, by the validity theorem of its instance; the
pass is then sound.
-/

namespace Veir.RISCV64Proofs

open Puddle.CTree RewritePattern

theorem loadPatterns_valid : ∀ pattern ∈ loadPatterns, Pattern.Valid pattern := by
  intro pattern member
  simp only [loadPatterns, Array.mem_flatMap, List.mem_toArray, List.mem_cons, List.not_mem_nil,
    or_false] at member
  obtain ⟨mode, modeMember, member⟩ := member
  rcases modeMember with rfl | rfl | rfl <;> rcases member with rfl | rfl | rfl | rfl
  · exact lowerLoad_gepIndex_lbu_valid
  · exact lowerLoad_gepIndex_lh_valid
  · exact lowerLoad_gepIndex_lw_valid
  · exact lowerLoad_gepIndex_ld_valid
  · exact lowerLoad_gepConst_lbu_valid
  · exact lowerLoad_gepConst_lh_valid
  · exact lowerLoad_gepConst_lw_valid
  · exact lowerLoad_gepConst_ld_valid
  · exact lowerLoad_reg_lbu_valid
  · exact lowerLoad_reg_lh_valid
  · exact lowerLoad_reg_lw_valid
  · exact lowerLoad_reg_ld_valid

theorem gmirLoadPatterns_valid : ∀ pattern ∈ gmirLoadPatterns, Pattern.Valid pattern := by
  intro pattern member
  simp only [gmirLoadPatterns, Array.mem_flatMap, List.mem_toArray, List.mem_cons, List.not_mem_nil,
    or_false] at member
  obtain ⟨mode, modeMember, member⟩ := member
  rcases modeMember with rfl | rfl | rfl <;> rcases member with rfl | rfl | rfl | rfl
  · exact gmirLoad_gepIndex_lbu_valid
  · exact gmirLoad_gepIndex_lh_valid
  · exact gmirLoad_gepIndex_lw_valid
  · exact gmirLoad_gepIndex_ld_valid
  · exact gmirLoad_gepConst_lbu_valid
  · exact gmirLoad_gepConst_lh_valid
  · exact gmirLoad_gepConst_lw_valid
  · exact gmirLoad_gepConst_ld_valid
  · exact gmirLoad_reg_lbu_valid
  · exact gmirLoad_reg_lh_valid
  · exact gmirLoad_reg_lw_valid
  · exact gmirLoad_reg_ld_valid

theorem storePatterns_valid : ∀ pattern ∈ storePatterns, Pattern.Valid pattern := by
  intro pattern member
  simp only [storePatterns, Array.mem_flatMap, List.mem_toArray, List.mem_cons, List.not_mem_nil,
    or_false] at member
  obtain ⟨mode, modeMember, member⟩ := member
  rcases modeMember with rfl | rfl | rfl <;> rcases member with rfl | rfl | rfl | rfl
  · exact lowerStore_gepIndex_sb_valid
  · exact lowerStore_gepIndex_sh_valid
  · exact lowerStore_gepIndex_sw_valid
  · exact lowerStore_gepIndex_sd_valid
  · exact lowerStore_gepConst_sb_valid
  · exact lowerStore_gepConst_sh_valid
  · exact lowerStore_gepConst_sw_valid
  · exact lowerStore_gepConst_sd_valid
  · exact lowerStore_reg_sb_valid
  · exact lowerStore_reg_sh_valid
  · exact lowerStore_reg_sw_valid
  · exact lowerStore_reg_sd_valid

theorem gmirSelectZeroOfSetccPatterns_valid :
    ∀ pattern ∈ gmirSelectZeroOfSetccPatterns, Pattern.Valid pattern := by
  intro pattern member
  simp only [gmirSelectZeroOfSetccPatterns, Array.mem_flatMap, Array.mem_map, List.mem_toArray,
    List.mem_cons, List.not_mem_nil, or_false] at member
  obtain ⟨zeroRhs, rhsMember, zeroFalse, falseMember, pred, predMember, rfl⟩ := member
  rcases rhsMember with rfl | rfl <;> rcases falseMember with rfl | rfl <;>
    rcases predMember with rfl | rfl
  · exact gmirSelectZeroOfSetcc_true_ne_true_valid
  · exact gmirSelectZeroOfSetcc_true_eq_true_valid
  · exact gmirSelectZeroOfSetcc_false_ne_true_valid
  · exact gmirSelectZeroOfSetcc_false_eq_true_valid
  · exact gmirSelectZeroOfSetcc_true_ne_false_valid
  · exact gmirSelectZeroOfSetcc_true_eq_false_valid
  · exact gmirSelectZeroOfSetcc_false_ne_false_valid
  · exact gmirSelectZeroOfSetcc_false_eq_false_valid

theorem gmirSelectZeroPatterns_valid :
    ∀ pattern ∈ gmirSelectZeroPatterns, Pattern.Valid pattern := by
  intro pattern member
  simp only [gmirSelectZeroPatterns, Array.mem_map, List.mem_toArray, List.mem_cons,
    List.not_mem_nil,
    or_false] at member
  obtain ⟨zeroFalse, zeroMember, rfl⟩ := member
  rcases zeroMember with rfl | rfl
  · exact gmirSelectZeroFalse_pattern_valid
  · exact gmirSelectZeroTrue_pattern_valid

theorem gmirSltiPatterns_valid : ∀ pattern ∈ gmirSltiPatterns, Pattern.Valid pattern := by
  intro pattern member
  simp only [gmirSltiPatterns, Array.mem_map, List.mem_toArray, List.mem_cons, List.not_mem_nil,
    or_false] at member
  obtain ⟨pred, predMember, rfl⟩ := member
  rcases predMember with rfl | rfl | rfl | rfl | rfl | rfl
  · exact gmirSlti_slt_pattern_valid
  · exact gmirSlti_ult_pattern_valid
  · exact gmirSlti_sge_pattern_valid
  · exact gmirSlti_uge_pattern_valid
  · exact gmirSlti_sle_pattern_valid
  · exact gmirSlti_ule_pattern_valid

theorem gmirIcmpPatterns_valid : ∀ pattern ∈ gmirIcmpPatterns, Pattern.Valid pattern := by
  intro pattern member
  simp only [gmirIcmpPatterns, Array.mem_append, Array.mem_map, List.mem_toArray, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with ⟨pred, predMember, rfl⟩ | ⟨pred, predMember, rfl⟩
  · rcases predMember with rfl | rfl
    · exact gmirIcmp_eq_zero_pattern_valid
    · exact gmirIcmp_ne_zero_pattern_valid
  · rcases predMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact gmirIcmp_eq_pattern_valid
    · exact gmirIcmp_ne_pattern_valid
    · exact gmirIcmp_slt_pattern_valid
    · exact gmirIcmp_sgt_pattern_valid
    · exact gmirIcmp_ult_pattern_valid
    · exact gmirIcmp_ugt_pattern_valid
    · exact gmirIcmp_sge_pattern_valid
    · exact gmirIcmp_sle_pattern_valid
    · exact gmirIcmp_uge_pattern_valid
    · exact gmirIcmp_ule_pattern_valid

/-- The `orc.b` selections at each of the eight byte positions. -/
theorem gmirOrcb_valid (y : Nat) (bound : y < 8) : Pattern.Valid (gmirOrcb_pattern y) :=
  match y, bound with
  | 0, _ => gmirOrcb_0_pattern_valid
  | 1, _ => gmirOrcb_1_pattern_valid
  | 2, _ => gmirOrcb_2_pattern_valid
  | 3, _ => gmirOrcb_3_pattern_valid
  | 4, _ => gmirOrcb_4_pattern_valid
  | 5, _ => gmirOrcb_5_pattern_valid
  | 6, _ => gmirOrcb_6_pattern_valid
  | 7, _ => gmirOrcb_7_pattern_valid
  | _ + 8, bound => absurd bound (by omega)

theorem gmirComposedPatterns_valid :
    ∀ pattern ∈ gmirComposedPatterns, Pattern.Valid pattern := by
  intro pattern member
  simp only [gmirComposedPatterns, Array.mem_append, List.mem_range, Array.mem_flatMap,
    Array.mem_map, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (⟨notLhs, notMember, rfl | rfl | rfl⟩ | ⟨y, bound, rfl⟩) | rfl | rfl
  · rcases notMember with rfl | rfl
    · exact gmirAndn_rhs_valid
    · exact gmirAndn_lhs_valid
  · rcases notMember with rfl | rfl
    · exact gmirOrn_rhs_valid
    · exact gmirOrn_lhs_valid
  · rcases notMember with rfl | rfl
    · exact gmirXnor_rhs_valid
    · exact gmirXnor_lhs_valid
  · exact gmirOrcb_valid y bound
  · exact gmirBexti_pattern_valid
  · exact gmirSlliuw_pattern_valid

public section

/-- Every pattern of the composed loop is valid. -/
theorem iselComposedPatterns_valid : ∀ pattern ∈ iselComposedPatterns, Pattern.Valid pattern :=
  gmirComposedPatterns_valid

/-- Every pattern of the early loop is valid. -/
theorem iselEarlyPatterns_valid : ∀ pattern ∈ iselEarlyPatterns, Pattern.Valid pattern := by
  intro pattern member
  simp only [iselEarlyPatterns, Array.mem_append, List.mem_toArray, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with
    (((((((rfl | rfl) | load) | gmirLoad) | store) | setcc) | zero) |
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl)) | slti
  · exact lifetimeStart_valid
  · exact lifetimeEnd_valid
  · exact loadPatterns_valid pattern load
  · exact gmirLoadPatterns_valid pattern gmirLoad
  · exact storePatterns_valid pattern store
  · exact gmirSelectZeroOfSetccPatterns_valid pattern setcc
  · exact gmirSelectZeroPatterns_valid pattern zero
  · exact fshlConst64_valid
  · exact fshlConst32_valid
  · exact fshrConst64_valid
  · exact fshrConst32_valid
  · exact fshlConst32Trunc_valid
  · exact fshrConst32Trunc_valid
  · exact gmirAddi_pattern_valid
  · exact gmirAndi_pattern_valid
  · exact gmirOri_pattern_valid
  · exact gmirXori_pattern_valid
  · exact gmirSlli_pattern_valid
  · exact gmirSrli_pattern_valid
  · exact gmirSrai_pattern_valid
  · exact gmirRiscvAddiw_pattern_valid
  · exact gmirRiscvSlliw_pattern_valid
  · exact gmirRiscvSrliw_pattern_valid
  · exact gmirRiscvSraiw_pattern_valid
  · exact gmirCpopw_pattern_valid
  · exact gmirBseti_pattern_valid
  · exact gmirBinvi_pattern_valid
  · exact gmirBclri_pattern_valid
  · exact gmirSltiPatterns_valid pattern slti

/-- Every pattern of the main loop is valid. -/
theorem iselMainPatterns_valid : ∀ pattern ∈ iselMainPatterns, Pattern.Valid pattern := by
  intro pattern member
  simp only [iselMainPatterns, Array.mem_append, List.mem_toArray, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with
    (((((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | load) |
      gmirLoad) | store) |
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl)) | icmp
  · exact gmirSelect_pattern_valid
  · exact constant_pattern_valid
  · exact addressof_pattern_valid
  · exact sext32_pattern_valid
  · exact sext16_pattern_valid
  · exact sextInReg8_valid
  · exact sextInReg16_valid
  · exact sextInReg32_valid
  · exact sextInRegShift_pattern_valid
  · exact zext32_pattern_valid
  · exact zext16_pattern_valid
  · exact trunc_pattern_valid
  · exact bitcast_pattern_valid
  · exact loadPatterns_valid pattern load
  · exact gmirLoadPatterns_valid pattern gmirLoad
  · exact storePatterns_valid pattern store
  · exact fshl64_pattern_valid
  · exact fshl32_pattern_valid
  · exact fshr64_pattern_valid
  · exact fshr32_pattern_valid
  · exact fshlGeneral64_valid
  · exact fshlGeneral32_valid
  · exact fshrGeneral64_valid
  · exact fshrGeneral32_valid
  · exact gmirPoison_pattern_valid
  · exact zeroConst_pattern_valid
  · exact freeze_pattern_valid
  · exact gmirAdd_pattern_valid
  · exact gmirSub_pattern_valid
  · exact gmirTrunc_pattern_valid
  · exact gmirAnyextOfReg_pattern_valid
  · exact gmirAnyext_pattern_valid
  · exact gmirShl_pattern_valid
  · exact gmirLshr_pattern_valid
  · exact gmirAshr_pattern_valid
  · exact gmirAnd_pattern_valid
  · exact gmirOr_pattern_valid
  · exact gmirXor_pattern_valid
  · exact gmirMul_pattern_valid
  · exact gmirSdiv_pattern_valid
  · exact gmirUdiv_pattern_valid
  · exact gmirSrem_pattern_valid
  · exact gmirUrem_pattern_valid
  · exact gmirRiscvAddw_pattern_valid
  · exact gmirRiscvSubw_pattern_valid
  · exact gmirRiscvMulw_pattern_valid
  · exact gmirRiscvDivw_pattern_valid
  · exact gmirRiscvDivuw_pattern_valid
  · exact gmirRiscvRemuw_pattern_valid
  · exact gmirRiscvSllw_pattern_valid
  · exact gmirRiscvSrlw_pattern_valid
  · exact gmirRiscvSraw_pattern_valid
  · exact gmirRiscvClzw_pattern_valid
  · exact gmirRiscvCtzw_pattern_valid
  · exact gmirConstant_pattern_valid
  · exact gmirCtlz_pattern_valid
  · exact gmirCttz_pattern_valid
  · exact gmirCtpop_pattern_valid
  · exact gmirBswap_pattern_valid
  · exact gmirBrev8_pattern_valid
  · exact gmirBitreverse_pattern_valid
  · exact gmirSmax_pattern_valid
  · exact gmirSmin_pattern_valid
  · exact gmirUmax_pattern_valid
  · exact gmirUmin_pattern_valid
  · exact gmirIcmpPatterns_valid pattern icmp

/-- The `isel-riscv64` pass refines the module and leaves it verified. -/
theorem ISelPass.run_sound : ISelPass.run.Sound :=
  checkedFunctionsPasses_sound fun pattern member => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact PointwiseValid.greedy_compiled iselComposedPatterns_valid
    · exact PointwiseValid.greedy_compiled iselEarlyPatterns_valid
    · exact PointwiseValid.greedy_compiled iselMainPatterns_valid

/-- The pass with its IO returns what `ISelPass.run` does. -/
theorem ISelPass.impl_eq_run (ctx : WfIRContext OpCode) (op : OperationPtr)
    (opIn : op.InBounds ctx.raw) :
    ISelPass.impl ctx op opIn = ExceptT.mk (pure (ISelPass.run ctx op)) := by
  rw [ISelPass.impl]

end
end Veir.RISCV64Proofs
