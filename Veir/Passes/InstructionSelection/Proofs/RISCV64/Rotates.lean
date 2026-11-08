module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Common

/-! Instruction-selection validity proofs: Rotates and funnel shifts. -/

namespace Veir

open Puddle
open _root_.CTree

set_option warn.sorry false

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Llvm.interpretOp' GMIR.interpretOp'
  Builtin.interpretOpCTree Llvm.interpretOpCTree GMIR.interpretOpCTree

attribute [local implicit_reducible] TypeAttr

theorem fshl64_pattern_valid :
    Puddle.CTree.Pattern.Valid fshl64_pattern := by
  unfold fshl64_pattern
  simp only [lowerRotate]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem fshl32_pattern_valid :
    Puddle.CTree.Pattern.Valid fshl32_pattern := by
  unfold fshl32_pattern
  simp only [lowerRotate]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem fshr64_pattern_valid :
    Puddle.CTree.Pattern.Valid fshr64_pattern := by
  unfold fshr64_pattern
  simp only [lowerRotate]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem fshr32_pattern_valid :
    Puddle.CTree.Pattern.Valid fshr32_pattern := by
  unfold fshr32_pattern
  simp only [lowerRotate]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem fshrConst64_valid :
    Puddle.CTree.Pattern.Valid (lowerFshConst false 64) := by
  dsimp only [lowerFshConst]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem fshrConst32_valid :
    Puddle.CTree.Pattern.Valid (lowerFshConst false 32) := by
  dsimp only [lowerFshConst]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem fshrConst32Trunc_valid :
    Puddle.CTree.Pattern.Valid (lowerFshConst false 32 true) := by
  dsimp only [lowerFshConst]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem fshlConst64_valid :
    Puddle.CTree.Pattern.Valid (lowerFshConst true 64) := by
  dsimp only [lowerFshConst]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem fshlConst32_valid :
    Puddle.CTree.Pattern.Valid (lowerFshConst true 32) := by
  dsimp only [lowerFshConst]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem fshlConst32Trunc_valid :
    Puddle.CTree.Pattern.Valid (lowerFshConst true 32 true) := by
  dsimp only [lowerFshConst]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem fshlGeneral64_valid :
    Puddle.CTree.Pattern.Valid (lowerFshlGeneral 64) := by
  dsimp only [lowerFshlGeneral]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem fshlGeneral32_valid :
    Puddle.CTree.Pattern.Valid (lowerFshlGeneral 32) := by
  dsimp only [lowerFshlGeneral]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem fshrGeneral64_valid :
    Puddle.CTree.Pattern.Valid (lowerFshrGeneral 64) := by
  dsimp only [lowerFshrGeneral]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem fshrGeneral32_valid :
    Puddle.CTree.Pattern.Valid (lowerFshrGeneral 32) := by
  dsimp only [lowerFshrGeneral]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

end Veir
