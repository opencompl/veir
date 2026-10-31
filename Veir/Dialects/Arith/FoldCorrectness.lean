module

public import Veir.Interfaces.FoldInterfaces.Correctness
import Veir.Interpreter.Refinement.Lemmas
import Veir.Data.LLVM.Int.FoldLemmas

import all Veir.GlobalOpInfo
import all Veir.Verifier
import all Veir.Verifier.Basic
import all Veir.Dialects.Arith.OpInfo

/-!
# Correctness of the `arith` fold table

Each theorem covers every successful lookup for a verified operation of its
opcode, with arbitrary known operands and properties.
-/

public section

namespace Veir
open Data

/-- The operand and result types of a verified `arith.addui_extended`: both operands and the sum
share one integer type, and the carry is `i1`. -/
theorem OperationPtr.Verified.arith_addui_extended {ctx : WfIRContext OpCode} {op : OperationPtr}
    {opInBounds} (opVerify : op.Verified ctx opInBounds)
    (opType : op.getOpType! ctx.raw = .arith .addui_extended) :
    ∃ type carry : IntegerType, carry.bitwidth = 1 ∧
      op.getOperandTypes! ctx.raw = #[(type : TypeAttr), (type : TypeAttr)] ∧
      op.getResultTypes! ctx.raw = #[(type : TypeAttr), (carry : TypeAttr)] := by
  simp only [OperationPtr.Verified, OperationPtr.verifyLocalInvariants,
    HasOpInfo.verifyLocalInvariants, OpCode.verifyLocalInvariants,
    ← OperationPtr.getOpType!_eq_getOpType, opType, Arith.verifyLocalInvariants,
    OperationPtr.verifyArithExtendedOp, OperationPtr.verifyPlainOpCounts,
    OperationPtr.verifyOperandTypesMatch, OperationPtr.verifyResultTypeMatches,
    TypeAttr.verifyIntegerType, TypeAttr.verifyI1, ne_eq, bind, Except.bind, throw,
    throwThe, MonadExceptOf.throw, pure, Except.pure, ite_true] at opVerify
  have hCounts : op.getNumOperands! ctx.raw = 2 ∧ op.getNumResults! ctx.raw = 2 := by grind
  simp [Array.ext_iff, TypeAttr.inj, ← Attribute.integerType_eq_of,
    OperationPtr.getOperandTypes!.size_eq_getNumOperands!,
    OperationPtr.getResultTypes!.size_eq_getNumResults!, hCounts, Nat.forall_lt_succ_left']
  grind

private theorem arith_addi_lookup
    (h : HasOpInfo.tryFold (OpCode.arith .addi) properties types known = some decisions) :
    ∃ left width, known = #[left, some (.int width (.val (0#width)))] ∧
      decisions = #[.useOperand 0] := by
  simp only [HasOpInfo.tryFold, OpCode.tryFold, Arith.tryFold] at h
  grind [Array.toList_inj]

private theorem arith_addui_extended_lookup
    (h : HasOpInfo.tryFold (OpCode.arith .addui_extended) properties types known = some decisions) :
    ∃ left width, known = #[left, some (.int width (.val (0#width)))] ∧
      decisions = #[.useOperand 0, .useConstant (.int 1 (.val 0))] := by
  simp only [HasOpInfo.tryFold, OpCode.tryFold, Arith.tryFold] at h
  grind [Array.toList_inj]

variable {ctx : WfIRContext OpCode} {op : OperationPtr}

/-- The verified arithmetic add-zero entry, including arbitrary overflow flags and poison inputs. -/
theorem Arith.tryFold_addi_correct (opType : op.getOpType! ctx.raw = .arith .addi) :
    FoldTable.CorrectAt ctx op := .of_verified fun _ verified => by
  obtain ⟨type, hOperands, hResults⟩ := (verified.arith_addi opType).types
  apply FoldTable.correctAt_int_rhs hOperands (fun width => .val (0#width))
    (decisions := #[.useOperand 0])
    (fun _ _ h => arith_addi_lookup (opType ▸ h))
  · grind [FoldDecision.HasType]
  · simp only [OperationPtr.interpret]
    rw [opType]
    simp [FoldDecision.resolveAll, FoldDecision.resolve, Veir.interpretOp', Arith.interpretOp',
      LLVM.Int.cast_self, LLVM.Int.add_zero, Interp.isRefinedBy]

/-- The extended-add entry refines both results, even when the unknown operand
is poison: its poison overflow flag may be replaced with concrete false. -/
theorem Arith.tryFold_addui_extended_correct
    (opType : op.getOpType! ctx.raw = .arith .addui_extended) :
    FoldTable.CorrectAt ctx op := .of_verified fun _ verified => by
  obtain ⟨type, carry, hCarry, hOperands, hResults⟩ := verified.arith_addui_extended opType
  apply FoldTable.correctAt_int_rhs hOperands (fun width => .val (0#width))
    (decisions := #[.useOperand 0, .useConstant (.int 1 (.val 0))])
    (fun _ _ h => arith_addui_extended_lookup (opType ▸ h))
  · grind [FoldDecision.HasType]
  · simp only [OperationPtr.interpret]
    rw [opType]
    simp [FoldDecision.resolveAll, FoldDecision.resolve, Veir.interpretOp', Arith.interpretOp',
      LLVM.Int.cast_self, LLVM.Int.add_zero, Interp.isRefinedBy, OperationResult.isRefinedBy,
      RuntimeValue.isRefinedBy, LLVM.Int.uaddOverflowFlag_zero]

/-- Every `arith` fold table entry is correct. The case analysis is exhaustive:
adding a table entry without a proof breaks this theorem. -/
theorem Arith.tryFold_correct (opType : op.getOpType! ctx.raw = .arith arithOp) :
    FoldTable.CorrectAt ctx op := by
  by_cases hAddi : arithOp = .addi
  · exact Arith.tryFold_addi_correct (hAddi ▸ opType)
  by_cases hAddUiExtended : arithOp = .addui_extended
  · exact Arith.tryFold_addui_extended_correct (hAddUiExtended ▸ opType)
  apply FoldTable.CorrectAt.of_tryFold_none
  generalize op.getOpType! ctx.raw = opCode at *
  subst opType
  intro properties resultTypes known
  simp only [HasOpInfo.tryFold, OpCode.tryFold, Arith.tryFold]
  split <;> simp_all

end Veir
