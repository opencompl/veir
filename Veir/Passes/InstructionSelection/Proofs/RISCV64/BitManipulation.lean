module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Common

/-! Instruction-selection validity proofs: Single-bit operations, byte combining, bit counting, and bit reversal. -/

namespace Veir

open Puddle
open _root_.CTree

set_option warn.sorry false

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Llvm.interpretOp' GMIR.interpretOp'
  Builtin.interpretOpCTree Llvm.interpretOpCTree GMIR.interpretOpCTree

attribute [local implicit_reducible] TypeAttr

theorem gmirBseti_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirBseti_pattern := by
  unfold gmirBseti_pattern
  simp only [gmirSingleBit_pattern, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirBinvi_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirBinvi_pattern := by
  unfold gmirBinvi_pattern
  simp only [gmirSingleBit_pattern, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirBclri_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirBclri_pattern := by
  unfold gmirBclri_pattern
  simp only [gmirSingleBit_pattern, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirOrcb_0_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirOrcb_pattern 0) := by
  dsimp only [gmirOrcb_pattern, matchConstant64, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirOrcb_1_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirOrcb_pattern 1) := by
  dsimp only [gmirOrcb_pattern, matchConstant64, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirOrcb_2_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirOrcb_pattern 2) := by
  dsimp only [gmirOrcb_pattern, matchConstant64, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirOrcb_3_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirOrcb_pattern 3) := by
  dsimp only [gmirOrcb_pattern, matchConstant64, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirOrcb_4_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirOrcb_pattern 4) := by
  dsimp only [gmirOrcb_pattern, matchConstant64, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirOrcb_5_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirOrcb_pattern 5) := by
  dsimp only [gmirOrcb_pattern, matchConstant64, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirOrcb_6_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirOrcb_pattern 6) := by
  dsimp only [gmirOrcb_pattern, matchConstant64, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirOrcb_7_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirOrcb_pattern 7) := by
  dsimp only [gmirOrcb_pattern, matchConstant64, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirBexti_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirBexti_pattern := by
  unfold gmirBexti_pattern
  simp only [matchLegal, matchConstant64, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirRiscvClzw_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirRiscvClzw_pattern := by
  unfold gmirRiscvClzw_pattern
  simp only [lowerUnary]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirRiscvCtzw_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirRiscvCtzw_pattern := by
  unfold gmirRiscvCtzw_pattern
  simp only [lowerUnary]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirCtlz_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirCtlz_pattern := by
  unfold gmirCtlz_pattern
  simp only [lowerUnary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirCttz_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirCttz_pattern := by
  unfold gmirCttz_pattern
  simp only [lowerUnary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirCtpop_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirCtpop_pattern := by
  unfold gmirCtpop_pattern
  simp only [lowerUnary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirCpopw_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirCpopw_pattern := by
  unfold gmirCpopw_pattern
  simp only [matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirBswap_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirBswap_pattern := by
  unfold gmirBswap_pattern
  simp only [lowerUnary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirBrev8_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirBrev8_pattern := by
  unfold gmirBrev8_pattern
  simp only [lowerUnary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirBitreverse_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirBitreverse_pattern := by
  unfold gmirBitreverse_pattern
  simp only [matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

end Veir
