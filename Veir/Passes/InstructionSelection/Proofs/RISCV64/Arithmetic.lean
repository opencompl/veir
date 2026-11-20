module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Common
import all Veir.Dialects.RISCV.Interpreter
meta import Veir.Meta.ProofKind

/-! Instruction-selection validity proofs: Integer arithmetic and min/max operations. -/

namespace Veir

open Puddle
open _root_.CTree


attribute [local ctree_semantics]
  Riscv.interpretOpCTree
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Llvm.interpretOp' GMIR.interpretOp' GMIR_RISCV.interpretOp'
  Builtin.interpretOpCTree Llvm.interpretOpCTree GMIR.interpretOpCTree

attribute [local implicit_reducible] TypeAttr

@[proof_bv]
theorem gmirAdd_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirAdd_pattern := by
  proveIselValid

@[proof_bv]
theorem gmirSub_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirSub_pattern := by
  proveIselValid

@[proof_bv]
theorem gmirAddi_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirAddi_pattern := by
  simpIselSemantics [←Attribute.integerType_eq_of]
  rintro signedness a ⟨property⟩ _verifiedConst
  simp [ctree_semantics]
  intro p _verified legal lo hi x hx
  cases a <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_normalize
  all_goals rw [mkRISCVImm_signExtend_12 property.value lo hi]
  all_goals veir_bv_decide

@[proof_bv]
theorem gmirRiscvAddiw_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirRiscvAddiw_pattern := by
  simpIselSemantics [←Attribute.integerType_eq_of, GMIR_RISCV.base]
  rintro signedness a ⟨property⟩ _verifiedConst
  simp [ctree_semantics]
  intro p _verified lo hi x hx
  cases a <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_normalize
  all_goals rw [mkRISCVImm_signExtend_12 property.value lo hi]
  all_goals have bridge := BitVec.setWidth_ofInt_32_64 property.value
  all_goals veir_bv_decide

@[proof_manual]
theorem gmirMul_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirMul_pattern := by
  simpIselSemantics
  intro s a b p _verified legal x hx y hy
  cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_normalize
  all_goals simp_all only [BitVec.mul_comm, implies_true, not_false_eq_true, not_true_eq_false, false_implies]

@[proof_manual]
theorem gmirSdiv_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirSdiv_pattern := by
  simpIselSemantics
  intro s a b p _verified legal mem
  by_cases h : a.isSignedDivisionUB b = true <;> simp [h, ctree_semantics]
  intro x hx y hy
  cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals first | solve | veir_bv_normalize; simp_all
                  | veir_bv_decide

@[proof_manual]
theorem gmirUdiv_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirUdiv_pattern := by
  simpIselSemantics
  intro s a b p _verified legal mem
  by_cases h : b.isUnsignedDivisionUB = true <;> simp [h, ctree_semantics]
  intro x hx y hy
  cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals first | solve | veir_bv_normalize; simp_all
                  | veir_bv_decide

@[proof_manual]
theorem gmirSrem_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirSrem_pattern := by
  simpIselSemantics
  intro s a b p _verified legal mem
  by_cases h : a.isSignedDivisionUB b = true <;> simp [h, ctree_semantics]
  intro x hx y hy
  cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals first | solve | veir_bv_normalize; simp_all
                  | veir_bv_decide

@[proof_manual]
theorem gmirUrem_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirUrem_pattern := by
  simpIselSemantics
  intro s a b p _verified legal mem
  by_cases h : b.isUnsignedDivisionUB = true <;> simp [h, ctree_semantics]
  intro x hx y hy
  cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals first | solve | veir_bv_normalize; simp_all
                  | veir_bv_decide

@[proof_bv]
theorem gmirRiscvAddw_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirRiscvAddw_pattern := by
  proveIselValid [GMIR_RISCV.base]

@[proof_bv]
theorem gmirRiscvSubw_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirRiscvSubw_pattern := by
  proveIselValid [GMIR_RISCV.base]

@[proof_bv]
theorem gmirRiscvMulw_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirRiscvMulw_pattern := by
  simpIselSemantics [GMIR_RISCV.base]
  intro s a b p _verified x hx y hy
  cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_normalize
  all_goals simp -failIfUnchanged only [*]
  all_goals veir_bv_decide

@[proof_bv]
theorem gmirRiscvDivw_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirRiscvDivw_pattern := by
  simpIselSemantics [GMIR_RISCV.base]
  intro s a b p _verified mem
  by_cases h : (a.trunc 32 false false (by veir_bv_decide)).isSignedDivisionUB (b.trunc 32 false false (by veir_bv_decide)) = true <;> simp [h, ctree_semantics]
  intro x hx y hy
  cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_normalize
  all_goals simp -failIfUnchanged only [*]
  all_goals veir_bv_decide

@[proof_bv]
theorem gmirRiscvDivuw_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirRiscvDivuw_pattern := by
  simpIselSemantics [GMIR_RISCV.base]
  intro s a b p _verified mem
  by_cases h : (b.trunc 32 false false (by veir_bv_decide)).isUnsignedDivisionUB = true <;> simp [h, ctree_semantics]
  intro x hx y hy
  cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_normalize
  all_goals simp -failIfUnchanged only [*]
  all_goals veir_bv_decide

@[proof_bv]
theorem gmirRiscvRemuw_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirRiscvRemuw_pattern := by
  simpIselSemantics [GMIR_RISCV.base]
  intro s a b p _verified mem
  by_cases h : (b.trunc 32 false false (by veir_bv_decide)).isUnsignedDivisionUB = true <;> simp [h, ctree_semantics]
  intro x hx y hy
  cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_normalize
  all_goals simp -failIfUnchanged only [*]
  all_goals veir_bv_decide

@[proof_bv]
theorem gmirSmax_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirSmax_pattern := by
  proveIselValid

@[proof_bv]
theorem gmirSmin_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirSmin_pattern := by
  proveIselValid

@[proof_bv]
theorem gmirUmax_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirUmax_pattern := by
  proveIselValid

@[proof_bv]
theorem gmirUmin_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirUmin_pattern := by
  proveIselValid

end Veir
