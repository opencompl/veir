module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Common

/-! Instruction-selection validity proofs: Integer shifts, including word and immediate forms. -/

namespace Veir

open Puddle
open _root_.CTree

set_option warn.sorry false

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Llvm.interpretOp' GMIR.interpretOp'
  Builtin.interpretOpCTree Llvm.interpretOpCTree GMIR.interpretOpCTree

attribute [local implicit_reducible] TypeAttr

theorem gmirShl_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirShl_pattern := by
  unfold gmirShl_pattern
  simp only [lowerBinary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirLshr_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirLshr_pattern := by
  unfold gmirLshr_pattern
  simp only [lowerBinary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirAshr_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirAshr_pattern := by
  unfold gmirAshr_pattern
  simp only [lowerBinary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirSlli_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirSlli_pattern := by
  unfold gmirSlli_pattern
  simp only [lowerBinaryImm, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirSrli_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirSrli_pattern := by
  unfold gmirSrli_pattern
  simp only [lowerBinaryImm, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirSrai_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirSrai_pattern := by
  unfold gmirSrai_pattern
  simp only [lowerBinaryImm, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirRiscvSlliw_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirRiscvSlliw_pattern := by
  unfold gmirRiscvSlliw_pattern
  simp only [lowerBinaryImm, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirRiscvSrliw_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirRiscvSrliw_pattern := by
  unfold gmirRiscvSrliw_pattern
  simp only [lowerBinaryImm, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirRiscvSraiw_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirRiscvSraiw_pattern := by
  unfold gmirRiscvSraiw_pattern
  simp only [lowerBinaryImm, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirSlliuw_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirSlliuw_pattern := by
  unfold gmirSlliuw_pattern
  simp only [matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirRiscvSllw_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirRiscvSllw_pattern := by
  unfold gmirRiscvSllw_pattern
  simp only [lowerBinary]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirRiscvSrlw_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirRiscvSrlw_pattern := by
  unfold gmirRiscvSrlw_pattern
  simp only [lowerBinary]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirRiscvSraw_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirRiscvSraw_pattern := by
  unfold gmirRiscvSraw_pattern
  simp only [lowerBinary]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

end Veir
