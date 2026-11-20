module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Common
import all Veir.Dialects.RISCV.Interpreter
meta import Veir.Meta.ProofKind

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

@[proof_bv]
theorem gmirAnd_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirAnd_pattern := by
  proveIselValid

@[proof_bv]
theorem gmirOr_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirOr_pattern := by
  proveIselValid

@[proof_bv]
theorem gmirXor_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirXor_pattern := by
  proveIselValid

@[proof_bv]
theorem gmirAndi_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirAndi_pattern := by
  simpIselSemantics [←Attribute.integerType_eq_of]
  rintro s a ⟨c⟩ _verifiedConst p _verified legal range
  simp only [Bool.and_eq_true, decide_eq_true_eq] at range
  simp [ctree_semantics]
  intro x hx
  cases a <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_normalize
  all_goals rw [mkRISCVImm_signExtend_12 c.value range.1 range.2]
  all_goals veir_bv_decide

@[proof_bv]
theorem gmirOri_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirOri_pattern := by
  simpIselSemantics [←Attribute.integerType_eq_of]
  rintro s a ⟨c⟩ _verifiedConst p _verified legal range
  simp only [Bool.and_eq_true, decide_eq_true_eq] at range
  simp [ctree_semantics]
  intro x hx
  cases a <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_normalize
  all_goals rw [mkRISCVImm_signExtend_12 c.value range.1 range.2]
  all_goals veir_bv_decide

@[proof_bv]
theorem gmirXori_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirXori_pattern := by
  simpIselSemantics [←Attribute.integerType_eq_of]
  rintro s a ⟨c⟩ _verifiedConst p _verified legal range
  simp only [Bool.and_eq_true, decide_eq_true_eq] at range
  simp [ctree_semantics]
  intro x hx
  cases a <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_normalize
  all_goals rw [mkRISCVImm_signExtend_12 c.value range.1 range.2]
  all_goals veir_bv_decide

@[proof_bv]
theorem gmirZexth_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirZexth_pattern := by
  proveIselValid [←Attribute.integerType_eq_of]

@[proof_bv]
theorem gmirZextw_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirZextw_pattern := by
  proveIselValid [←Attribute.integerType_eq_of]

@[proof_bv]
theorem gmirAndn_rhs_valid :
    Puddle.CTree.Pattern.Valid (gmirBinopNot_pattern .g_and .andn () false) := by
  proveIselValid [←Attribute.integerType_eq_of]

@[proof_bv]
theorem gmirOrn_rhs_valid :
    Puddle.CTree.Pattern.Valid (gmirBinopNot_pattern .g_or .orn () false) := by
  proveIselValid [←Attribute.integerType_eq_of]

@[proof_bv]
theorem gmirXnor_rhs_valid :
    Puddle.CTree.Pattern.Valid (gmirBinopNot_pattern .g_xor .xnor () false) := by
  proveIselValid [←Attribute.integerType_eq_of]

@[proof_bv]
theorem gmirAndn_lhs_valid :
    Puddle.CTree.Pattern.Valid (gmirBinopNot_pattern .g_and .andn () true) := by
  proveIselValid [←Attribute.integerType_eq_of]

@[proof_bv]
theorem gmirOrn_lhs_valid :
    Puddle.CTree.Pattern.Valid (gmirBinopNot_pattern .g_or .orn () true) := by
  proveIselValid [←Attribute.integerType_eq_of]

@[proof_bv]
theorem gmirXnor_lhs_valid :
    Puddle.CTree.Pattern.Valid (gmirBinopNot_pattern .g_xor .xnor () true) := by
  proveIselValid [←Attribute.integerType_eq_of]

end Veir
