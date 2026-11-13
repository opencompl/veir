module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Common
import all Veir.Dialects.RISCV.Interpreter

/-! Instruction-selection validity proofs: Boolean bitwise operations, including immediate and inverted operands. -/

namespace Veir

open Puddle
open _root_.CTree


attribute [local ctree_semantics]
  Riscv.interpretOpCTree
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
  intro s a b p _verified legal x hx y hy
  cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_decide

theorem gmirOr_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirOr_pattern := by
  unfold gmirOr_pattern
  simp only [lowerBinary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  intro s a b p _verified legal x hx y hy
  cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_decide

theorem gmirXor_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirXor_pattern := by
  unfold gmirXor_pattern
  simp only [lowerBinary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  intro s a b p _verified legal x hx y hy
  cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_decide

theorem gmirAndi_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirAndi_pattern := by
  unfold gmirAndi_pattern
  simp only [lowerBinaryImm, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  rintro s a ⟨c⟩ _verifiedConst p _verified legal range
  simp only [Bool.and_eq_true, decide_eq_true_eq] at range
  simp [ctree_semantics]
  intro x hx
  cases a <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_normalize
  all_goals rw [mkRISCVImm_signExtend_12 c.value range.1 range.2]
  all_goals veir_bv_decide

theorem gmirOri_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirOri_pattern := by
  unfold gmirOri_pattern
  simp only [lowerBinaryImm, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  rintro s a ⟨c⟩ _verifiedConst p _verified legal range
  simp only [Bool.and_eq_true, decide_eq_true_eq] at range
  simp [ctree_semantics]
  intro x hx
  cases a <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_normalize
  all_goals rw [mkRISCVImm_signExtend_12 c.value range.1 range.2]
  all_goals veir_bv_decide

theorem gmirXori_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirXori_pattern := by
  unfold gmirXori_pattern
  simp only [lowerBinaryImm, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  rintro s a ⟨c⟩ _verifiedConst p _verified legal range
  simp only [Bool.and_eq_true, decide_eq_true_eq] at range
  simp [ctree_semantics]
  intro x hx
  cases a <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_normalize
  all_goals rw [mkRISCVImm_signExtend_12 c.value range.1 range.2]
  all_goals veir_bv_decide

theorem gmirAndn_rhs_valid :
    Puddle.CTree.Pattern.Valid (gmirBinopNot_pattern .g_and .andn () false) := by
  dsimp only [gmirBinopNot_pattern, matchConstant64, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  rintro s a b ⟨c⟩ ones _verifiedConst xp _verifiedXor p _verified legal x hx y hy
  simp only [decide_eq_true_eq] at ones
  cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_decide

theorem gmirOrn_rhs_valid :
    Puddle.CTree.Pattern.Valid (gmirBinopNot_pattern .g_or .orn () false) := by
  dsimp only [gmirBinopNot_pattern, matchConstant64, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  rintro s a b ⟨c⟩ ones _verifiedConst xp _verifiedXor p _verified legal x hx y hy
  simp only [decide_eq_true_eq] at ones
  cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_decide

theorem gmirXnor_rhs_valid :
    Puddle.CTree.Pattern.Valid (gmirBinopNot_pattern .g_xor .xnor () false) := by
  dsimp only [gmirBinopNot_pattern, matchConstant64, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  rintro s a b ⟨c⟩ ones _verifiedConst xp _verifiedXor p _verified legal x hx y hy
  simp only [decide_eq_true_eq] at ones
  cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_decide

theorem gmirAndn_lhs_valid :
    Puddle.CTree.Pattern.Valid (gmirBinopNot_pattern .g_and .andn () true) := by
  dsimp only [gmirBinopNot_pattern, matchConstant64, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  rintro s a b ⟨c⟩ ones _verifiedConst xp _verifiedXor p _verified legal x hx y hy
  simp only [decide_eq_true_eq] at ones
  cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_decide

theorem gmirOrn_lhs_valid :
    Puddle.CTree.Pattern.Valid (gmirBinopNot_pattern .g_or .orn () true) := by
  dsimp only [gmirBinopNot_pattern, matchConstant64, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  rintro s a b ⟨c⟩ ones _verifiedConst xp _verifiedXor p _verified legal x hx y hy
  simp only [decide_eq_true_eq] at ones
  cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_decide

theorem gmirXnor_lhs_valid :
    Puddle.CTree.Pattern.Valid (gmirBinopNot_pattern .g_xor .xnor () true) := by
  dsimp only [gmirBinopNot_pattern, matchConstant64, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  rintro s a b ⟨c⟩ ones _verifiedConst xp _verifiedXor p _verified legal x hx y hy
  simp only [decide_eq_true_eq] at ones
  cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_decide

end Veir
