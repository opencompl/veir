module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Common

/-! Instruction-selection validity proofs: Integer arithmetic and min/max operations. -/

namespace Veir

open Puddle
open _root_.CTree

set_option warn.sorry false

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Llvm.interpretOp' GMIR.interpretOp' GMIR_RISCV.interpretOp'
  Builtin.interpretOpCTree Llvm.interpretOpCTree GMIR.interpretOpCTree

attribute [local implicit_reducible] TypeAttr

theorem gmirAdd_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirAdd_pattern := by
  unfold gmirAdd_pattern
  simp only [lowerBinary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirSub_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirSub_pattern := by
  unfold gmirSub_pattern
  simp only [lowerBinary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirAddi_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirAddi_pattern := by
  unfold gmirAddi_pattern
  simp only [lowerBinaryImm, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  rintro signedness a ⟨property⟩
  simp [ctree_semantics]
  sorry

theorem gmirRiscvAddiw_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirRiscvAddiw_pattern := by
  unfold gmirRiscvAddiw_pattern
  simp only [lowerBinaryImm, createRegOp]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of, GMIR_RISCV.base]
  rintro signedness a ⟨property⟩
  simp [ctree_semantics]
  sorry

theorem gmirMul_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirMul_pattern := by
  unfold gmirMul_pattern
  simp only [lowerBinary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirSdiv_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirSdiv_pattern := by
  unfold gmirSdiv_pattern
  simp only [lowerBinary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirUdiv_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirUdiv_pattern := by
  unfold gmirUdiv_pattern
  simp only [lowerBinary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirSrem_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirSrem_pattern := by
  unfold gmirSrem_pattern
  simp only [lowerBinary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirUrem_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirUrem_pattern := by
  unfold gmirUrem_pattern
  simp only [lowerBinary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirRiscvAddw_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirRiscvAddw_pattern := by
  unfold gmirRiscvAddw_pattern
  simp only [lowerBinary]
  simpPuddleValid
  simp [ctree_semantics, GMIR_RISCV.base]
  sorry

theorem gmirRiscvSubw_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirRiscvSubw_pattern := by
  unfold gmirRiscvSubw_pattern
  simp only [lowerBinary]
  simpPuddleValid
  simp [ctree_semantics, GMIR_RISCV.base]
  sorry

theorem gmirRiscvMulw_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirRiscvMulw_pattern := by
  unfold gmirRiscvMulw_pattern
  simp only [lowerBinary]
  simpPuddleValid
  simp [ctree_semantics, GMIR_RISCV.base]
  sorry

theorem gmirRiscvDivw_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirRiscvDivw_pattern := by
  unfold gmirRiscvDivw_pattern
  simp only [lowerBinary]
  simpPuddleValid
  simp [ctree_semantics, GMIR_RISCV.base]
  sorry

theorem gmirRiscvDivuw_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirRiscvDivuw_pattern := by
  unfold gmirRiscvDivuw_pattern
  simp only [lowerBinary]
  simpPuddleValid
  simp [ctree_semantics, GMIR_RISCV.base]
  sorry

theorem gmirRiscvRemuw_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirRiscvRemuw_pattern := by
  unfold gmirRiscvRemuw_pattern
  simp only [lowerBinary]
  simpPuddleValid
  simp [ctree_semantics, GMIR_RISCV.base]
  sorry

theorem gmirSmax_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirSmax_pattern := by
  unfold gmirSmax_pattern
  simp only [lowerBinary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirSmin_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirSmin_pattern := by
  unfold gmirSmin_pattern
  simp only [lowerBinary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirUmax_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirUmax_pattern := by
  unfold gmirUmax_pattern
  simp only [lowerBinary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirUmin_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirUmin_pattern := by
  unfold gmirUmin_pattern
  simp only [lowerBinary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

end Veir
