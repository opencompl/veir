module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Common

/-! Instruction-selection validity proofs: Integer comparisons and conditional selects. -/

namespace Veir

open Puddle
open _root_.CTree

set_option warn.sorry false

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Llvm.interpretOp' GMIR.interpretOp'
  Builtin.interpretOpCTree Llvm.interpretOpCTree GMIR.interpretOpCTree

attribute [local implicit_reducible] TypeAttr

theorem gmirSelectZeroFalse_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirSelectZero_pattern true) := by
  dsimp only [gmirSelectZero_pattern, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirSelectZeroTrue_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirSelectZero_pattern false) := by
  dsimp only [gmirSelectZero_pattern, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirSelect_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirSelect_pattern := by
  unfold gmirSelect_pattern
  simp only [matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirIcmp_eq_zero_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirIcmp_pattern .eq true) := by
  dsimp only [gmirIcmp_pattern, matchLegal, icmpEmit, icmpEmitCmp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirIcmp_eq_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirIcmp_pattern .eq false) := by
  dsimp only [gmirIcmp_pattern, matchLegal, icmpEmit, icmpEmitCmp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirIcmp_ne_zero_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirIcmp_pattern .ne true) := by
  dsimp only [gmirIcmp_pattern, matchLegal, icmpEmit, icmpEmitCmp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirIcmp_ne_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirIcmp_pattern .ne false) := by
  dsimp only [gmirIcmp_pattern, matchLegal, icmpEmit, icmpEmitCmp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirIcmp_slt_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirIcmp_pattern .slt false) := by
  dsimp only [gmirIcmp_pattern, matchLegal, icmpEmit, icmpEmitCmp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirIcmp_sgt_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirIcmp_pattern .sgt false) := by
  dsimp only [gmirIcmp_pattern, matchLegal, icmpEmit, icmpEmitCmp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirIcmp_ult_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirIcmp_pattern .ult false) := by
  dsimp only [gmirIcmp_pattern, matchLegal, icmpEmit, icmpEmitCmp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirIcmp_ugt_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirIcmp_pattern .ugt false) := by
  dsimp only [gmirIcmp_pattern, matchLegal, icmpEmit, icmpEmitCmp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirIcmp_sge_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirIcmp_pattern .sge false) := by
  dsimp only [gmirIcmp_pattern, matchLegal, icmpEmit, icmpEmitCmp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirIcmp_sle_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirIcmp_pattern .sle false) := by
  dsimp only [gmirIcmp_pattern, matchLegal, icmpEmit, icmpEmitCmp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirIcmp_uge_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirIcmp_pattern .uge false) := by
  dsimp only [gmirIcmp_pattern, matchLegal, icmpEmit, icmpEmitCmp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirIcmp_ule_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirIcmp_pattern .ule false) := by
  dsimp only [gmirIcmp_pattern, matchLegal, icmpEmit, icmpEmitCmp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirSlti_slt_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirSlti_pattern .slt) := by
  dsimp only [gmirSlti_pattern, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirSlti_ult_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirSlti_pattern .ult) := by
  dsimp only [gmirSlti_pattern, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirSlti_sge_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirSlti_pattern .sge) := by
  dsimp only [gmirSlti_pattern, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirSlti_uge_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirSlti_pattern .uge) := by
  dsimp only [gmirSlti_pattern, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirSlti_sle_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirSlti_pattern .sle) := by
  dsimp only [gmirSlti_pattern, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirSlti_ule_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirSlti_pattern .ule) := by
  dsimp only [gmirSlti_pattern, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

end Veir
