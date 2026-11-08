module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Common

/-! Instruction-selection validity proofs: Boolean bitwise operations, including immediate and inverted operands. -/

namespace Veir

open Puddle
open _root_.CTree

set_option warn.sorry false

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Llvm.interpretOp' GMIR.interpretOp'
  Builtin.interpretOpCTree Llvm.interpretOpCTree GMIR.interpretOpCTree

attribute [local implicit_reducible] TypeAttr

theorem gmirAnd_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirAnd_pattern := by
  unfold gmirAnd_pattern
  simp only [lowerBinary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirOr_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirOr_pattern := by
  unfold gmirOr_pattern
  simp only [lowerBinary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirXor_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirXor_pattern := by
  unfold gmirXor_pattern
  simp only [lowerBinary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirAndi_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirAndi_pattern := by
  unfold gmirAndi_pattern
  simp only [lowerBinaryImm, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirOri_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirOri_pattern := by
  unfold gmirOri_pattern
  simp only [lowerBinaryImm, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirXori_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirXori_pattern := by
  unfold gmirXori_pattern
  simp only [lowerBinaryImm, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirAndn_rhs_valid :
    Puddle.CTree.Pattern.Valid (gmirBinopNot_pattern .g_and .andn () false) := by
  dsimp only [gmirBinopNot_pattern, matchConstant64, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirOrn_rhs_valid :
    Puddle.CTree.Pattern.Valid (gmirBinopNot_pattern .g_or .orn () false) := by
  dsimp only [gmirBinopNot_pattern, matchConstant64, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirXnor_rhs_valid :
    Puddle.CTree.Pattern.Valid (gmirBinopNot_pattern .g_xor .xnor () false) := by
  dsimp only [gmirBinopNot_pattern, matchConstant64, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirAndn_lhs_valid :
    Puddle.CTree.Pattern.Valid (gmirBinopNot_pattern .g_and .andn () true) := by
  dsimp only [gmirBinopNot_pattern, matchConstant64, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirOrn_lhs_valid :
    Puddle.CTree.Pattern.Valid (gmirBinopNot_pattern .g_or .orn () true) := by
  dsimp only [gmirBinopNot_pattern, matchConstant64, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirXnor_lhs_valid :
    Puddle.CTree.Pattern.Valid (gmirBinopNot_pattern .g_xor .xnor () true) := by
  dsimp only [gmirBinopNot_pattern, matchConstant64, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

end Veir
