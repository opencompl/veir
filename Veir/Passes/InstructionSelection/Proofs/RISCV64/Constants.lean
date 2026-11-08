module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Common

/-! Instruction-selection validity proofs: Constant materialization and freeze. -/

namespace Veir

open Puddle
open _root_.CTree

set_option warn.sorry false

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Llvm.interpretOp' GMIR.interpretOp'
  Builtin.interpretOpCTree Llvm.interpretOpCTree GMIR.interpretOpCTree

@[simp, ctree_semantics]
private theorem tt (P : propertiesOf (OpCode.gmir GMIR.g_constant) → Prop) :
    (∀ (property : propertiesOf (OpCode.gmir GMIR.g_constant)), P property) ↔
    (∀ (value : IntegerAttr), P { value := value }) := by
  constructor
  · grind
  · intro h ⟨prop⟩
    grind

attribute [local implicit_reducible] TypeAttr

theorem constant_pattern_valid :
    Puddle.CTree.Pattern.Valid constant_pattern := by
  unfold constant_pattern
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  intro x xBw property hProperty
  obtain ⟨propVal, rfl⟩ : exists value, property = { value := LLVMConstantValue.integer value } := by
    cases property; grind
  simp [ctree_semantics]
  sorry

theorem poisonConstInt_pattern_valid :
    Puddle.CTree.Pattern.Valid (poisonConst_pattern IntegerType) := by
  unfold poisonConst_pattern
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  sorry

theorem poisonConstPtr_pattern_valid :
    Puddle.CTree.Pattern.Valid (poisonConst_pattern LLVM.PointerType) := by
  unfold poisonConst_pattern
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.llvmPointerType_eq_of]
  sorry

theorem zeroConstInt_pattern_valid :
    Puddle.CTree.Pattern.Valid (zeroConst_pattern IntegerType (·.bitwidth)) := by
  unfold zeroConst_pattern
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  sorry

theorem zeroConstPtr_pattern_valid :
    Puddle.CTree.Pattern.Valid (zeroConst_pattern LLVM.PointerType (fun _ => 64)) := by
  unfold zeroConst_pattern
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.llvmPointerType_eq_of]
  sorry

theorem freeze_pattern_valid :
    Puddle.CTree.Pattern.Valid freeze_pattern := by
  unfold freeze_pattern
  simp only [lowerRegCast]
  simpPuddleValid
  simp [ctree_semantics]
  rintro x x₂ (v | _)
  · simp
    intro xBw rfl
    grind
  · simp [ctree_semantics, Functor.map]
    intro xBw rfl
    simp

theorem gmirConstant_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirConstant_pattern := by
  unfold gmirConstant_pattern
  simp only [matchLegal]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  sorry

end Veir
