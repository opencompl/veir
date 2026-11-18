module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Common
import all Veir.Dialects.RISCV.Interpreter
import all Veir.Interpreter.Memory
import all Veir.Data.LLVM.Ptr.Basic
import all Veir.Data.Pointer.Basic
import all Veir.Passes.Legalization.RISCV64LegalizerInfo
import all Veir.Passes.Legalization.LegalizerInfo
meta import Veir.Meta.ProofKind

/-! Instruction-selection validity proofs: Constant materialization and freeze. -/

namespace Veir

open Puddle
open _root_.CTree

attribute [local ctree_semantics]
  Riscv.interpretOpCTree
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

@[proof_manual]
theorem constant_pattern_valid :
    Puddle.CTree.Pattern.Valid constant_pattern := by
  simpIselSemantics [←Attribute.integerType_eq_of]
  intro x xBw property hProperty _hVerified
  obtain ⟨propVal, rfl⟩ : exists value, property = { value := LLVMConstantValue.integer value } := by
    cases property; grind
  simp [ctree_semantics]
  simp only [Data.RISCV.val_li]
  ext i hi
  simp [BitVec.getElem_signExtend, hi, Nat.lt_of_lt_of_le hi xBw]

@[proof_manual]
theorem gmirPoison_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirPoison_pattern := by
  simpIselSemantics
  intro ⟨attr, hattr⟩
  cases attr <;> simp [ctree_semantics, RuntimeValue.isRefinedBy,
    Data.RISCV.val_li, MemoryState.ptrFromInt,
    MemoryState.decode, Data.LLVM.Ptr.isRefinedBy]

-- The simp arguments below are each needed on some of the goals the `cases` produce.
set_option linter.unusedSimpArgs false in
@[proof_manual]
theorem freeze_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirFreeze_pattern := by
  simpIselSemantics
  intro src dst value hc props hv hlegal
  obtain rfl := hv.gmir_freeze_type_eq
  obtain ⟨s, rfl⟩ := isLegal_g_freeze_types _ props hlegal
  cases value <;> simp [RuntimeValue.Conforms] at hc
  cases hc
  rename_i bits
  cases bits <;> simp [ctree_semantics, ←Attribute.integerType_eq_of, Builtin.interpretUnrealizedConversionCastCTree, ←Attribute.registerType_eq_of]
  all_goals intros
  all_goals simp_all [ctree_semantics, RISCV.Reg.toInt, BitVec.setWidth_eq, ←Attribute.integerType_eq_of,
    ←Attribute.registerType_eq_of, Functor.map, CTree.choose_def, CTree.tau_def, Bind.bind,
    Builtin.intToRegCTree]

@[proof_manual]
theorem gmirConstant_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirConstant_pattern := by
  simpIselSemantics
  intro ⟨attr, hattr⟩ value _hVerified legal
  -- `riscv64LegalizerInfo` makes `g_constant` legal only for `i64` and pointers.
  cases attr <;> simp [ctree_semantics, RuntimeValue.isRefinedBy,
    Data.RISCV.val_li, MemoryState.ptrFromInt, MemoryState.decode]
  rename_i type
  by_cases h : type.bitwidth = 64
  · rcases type with ⟨width, signedness⟩
    cases h
    rfl
  · cbv at legal
    by_cases hw : type.bitwidth < 64 <;>
      simp [h, hw, LegalizeRule.minScalar, LegalizeRule.widenScalarIf,
        LegalityPredicate.scalarNarrowerThan, LegalityQuery.getLLT!] at legal

end Veir
