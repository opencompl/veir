module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Common
import all Veir.Interpreter.Memory
import all Veir.Data.LLVM.Ptr.Basic
import all Veir.Data.Pointer.Basic
import all Veir.Passes.Legalization.RISCV64LegalizerInfo
import all Veir.Passes.Legalization.LegalizerInfo

/-! Instruction-selection validity proofs: Constant materialization and freeze. -/

namespace Veir

open Puddle
open _root_.CTree

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Llvm.interpretOp' GMIR.interpretOp'
  Builtin.interpretOpCTree Llvm.interpretOpCTree GMIR.interpretOpCTree

@[simp, ctree_semantics]
private theorem forall_gmirConstantProperties (P : propertiesOf (OpCode.gmir GMIR.g_constant) → Prop) :
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
  intro x xBw property hProperty _hVerified
  obtain ⟨propVal, rfl⟩ : exists value, property = { value := LLVMConstantValue.integer value } := by
    cases property; grind
  simp [ctree_semantics]
  simp only [Data.RISCV.val_li]
  ext i hi
  simp [BitVec.getElem_signExtend, hi, Nat.lt_of_lt_of_le hi xBw]

theorem poisonConst_pattern_valid :
    Puddle.CTree.Pattern.Valid poisonConst_pattern := by
  unfold poisonConst_pattern
  simpPuddleValid
  simp [ctree_semantics]
  intro ⟨attr, hattr⟩
  cases attr <;> simp [icmpTypeWidth?, ctree_semantics, RuntimeValue.isRefinedBy,
    Data.LLVM.Int.mlir_poison, Data.RISCV.val_li, MemoryState.ptrFromInt,
    MemoryState.decode, Data.LLVM.Ptr.null, Data.Pointer.null, Data.LLVM.Ptr.isRefinedBy]

theorem zeroConst_pattern_valid :
    Puddle.CTree.Pattern.Valid zeroConst_pattern := by
  unfold zeroConst_pattern
  simpPuddleValid
  simp [ctree_semantics]
  intro ⟨attr, hattr⟩
  cases attr <;> simp [icmpTypeWidth?, ctree_semantics, RuntimeValue.isRefinedBy,
    Data.LLVM.Int.mlir_poison, Data.RISCV.val_li, MemoryState.ptrFromInt,
    MemoryState.decode, Data.LLVM.Ptr.null, Data.Pointer.null, Data.LLVM.Ptr.isRefinedBy]

theorem freeze_pattern_valid :
    Puddle.CTree.Pattern.Valid freeze_pattern := by
  unfold freeze_pattern
  simp only [lowerRegCast]
  simpPuddleValid
  simp [ctree_semantics]
  intro ⟨src, hsrc⟩ ⟨dst, hdst⟩ value hc props hv hlegal
  cases src <;> cases dst <;> simp at hlegal
  obtain ⟨hw, rfl⟩ := hlegal
  cases value <;> simp [RuntimeValue.Conforms] at hc
  cases hc
  rename_i bits
  cases bits <;> simp [ctree_semantics, ←Attribute.integerType_eq_of, Builtin.interpretUnrealizedConversionCastCTree, ←Attribute.registerType_eq_of]
  all_goals intros
  all_goals simp_all [ctree_semantics, RISCV.Reg.toInt, BitVec.setWidth_setWidth_of_le _ hw, ←Attribute.integerType_eq_of,
    ←Attribute.registerType_eq_of, Functor.map, CTree.choose_def, CTree.tau_def, Bind.bind]

theorem gmirConstant_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirConstant_pattern := by
  unfold gmirConstant_pattern
  simp only [matchLegal]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  intro a value _hVerified legal
  simp only [Data.RISCV.val_li]
  by_cases h : a.bitwidth = 64
  · rcases a with ⟨width, signedness⟩
    cases h
    rfl
  · cbv at legal
    by_cases hw : a.bitwidth < 64 <;>
      simp [h, hw, LegalizeRule.minScalar, LegalizeRule.widenScalarIf,
        LegalityPredicate.scalarNarrowerThan, LegalityQuery.getLLT!] at legal

end Veir
