module

public import Veir.Interfaces.FoldInterfaces.Lemmas

import all Veir.Data.Refinement
import all Veir.IR.Attribute
import all Veir.IR.Basic
import all Veir.Interpreter.Basic
import all Veir.GlobalOpInfo
import all Veir.Dialects.Arith.OpInfo
import all Veir.Dialects.LLVM.OpInfo
import all Veir.Dialects.RISCV.OpInfo
import all Veir.Dialects.RISCV.Properties
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.RISCV.Reg.Basic
import all Veir.Verifier
import all Veir.Verifier.Basic

/-!
# Proofs for dialect fold-table entries

Each theorem covers every successful lookup for a verified operation of its
opcode, with arbitrary known operands and properties. Operand and result types
are derived from verification, without assumptions about the folding driver.
-/

public section

namespace Veir
open Data

private theorem fold_add_zero (x : LLVM.Int w) (nsw nuw : Bool) :
    LLVM.Int.add x (.val (0#w)) nsw nuw = x := by
  cases x <;> simp [LLVM.Int.add, Id.run, BitVec.saddOverflow_eq, BitVec.uaddOverflow, BitVec.isLt]

private theorem overflow_zero (x : LLVM.Int w) :
    LLVM.Int.uaddOverflowFlag x (.val (0#w)) ⊒ .val (0#1) := by
  cases x <;> simp [LLVM.Int.uaddOverflowFlag, Id.run, BitVec.uaddOverflow_eq, isRefinedBy,
    BitVec.msb_eq_getLsbD_last]

private theorem riscv_andi_lookup
    (h : HasOpInfo.tryFold (OpCode.riscv .andi) properties types known = some decisions) :
    properties.value = 0 ∧ decisions = #[.useConstant (.reg ⟨0⟩)] := by
  simp only [HasOpInfo.tryFold, OpCode.tryFold, Riscv.tryFold] at h
  grind

variable {ctx : WfIRContext OpCode} {op : OperationPtr} {opIn : op.InBounds ctx.raw}

private theorem arith_addui_extended_types (verified : op.Verified ctx opIn)
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
    throwThe, MonadExceptOf.throw, pure, Except.pure, ite_true] at verified
  have hCounts : op.getNumOperands! ctx.raw = 2 ∧ op.getNumResults! ctx.raw = 2 := by grind
  simp [Array.ext_iff, TypeAttr.inj, ← Attribute.integerType_eq_of,
    OperationPtr.getOperandTypes!.size_eq_getNumOperands!,
    OperationPtr.getResultTypes!.size_eq_getNumResults!, hCounts, Nat.forall_lt_succ_left']
  grind

private theorem riscv_andi_types (verified : op.Verified ctx opIn)
    (opType : op.getOpType! ctx.raw = .riscv .andi) :
    ∃ operandType resultType : RegisterType,
      op.getOperandTypes! ctx.raw = #[(operandType : TypeAttr)] ∧
      op.getResultTypes! ctx.raw = #[(resultType : TypeAttr)] := by
  simp only [OperationPtr.Verified, OperationPtr.verifyLocalInvariants,
    HasOpInfo.verifyLocalInvariants, OpCode.verifyLocalInvariants,
    ← OperationPtr.getOpType!_eq_getOpType, opType, Riscv.verifyLocalInvariants] at verified
  obtain ⟨_, hTypes, hCounts⟩ := Except.bind_eq_ok.mp verified
  simp only [OperationPtr.verifyRISCVimm12, OperationPtr.verifyPlainOpCounts, ne_eq, bind,
    Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at hCounts
  have hCounts : (op.getOperandTypes! ctx.raw).size = 1 ∧
      op.getNumResults ctx.raw opIn = 1 := by grind
  simp [OperationPtr.verifyRISCVRegisterTypes, hCounts, bind, Except.bind, throw,
    throwThe, MonadExceptOf.throw, pure, Except.pure] at hTypes
  simp [Array.ext_iff, TypeAttr.inj, ← Attribute.registerType_eq_of, hCounts,
    OperationPtr.getResultTypes!.size_eq_getNumResults!,
    OperationPtr.getNumResults!_eq_getNumResults opIn]
  grind

/-- The verified arithmetic add-zero entry, including arbitrary overflow flags and poison inputs. -/
theorem Arith.tryFold_addi_correct (verified : op.Verified ctx opIn)
    (opType : op.getOpType! ctx.raw = .arith .addi) :
    FoldTable.CorrectAt ctx op verified := by
  obtain ⟨type, hOperands, hResults⟩ := (verified.arith_addi opType).types
  apply FoldTable.correctAt_int_rhs verified hOperands (fun width => .val (0#width))
    (decisions := #[.useOperand 0]) (fun _ _ h => by
      have h := opType ▸ h
      simp only [HasOpInfo.tryFold, OpCode.tryFold, Arith.tryFold] at h
      grind [Array.toList_inj])
  · simp [hOperands, hResults, FoldDecision.HasType]
  · simp only [OperationPtr.interpret]
    rw [opType]
    simp [FoldDecision.resolveAll, FoldDecision.resolve, Veir.interpretOp', Arith.interpretOp',
      LLVM.Int.cast_self, fold_add_zero, Interp.isRefinedBy]

/-- The extended-add entry refines both results, even when the unknown operand
is poison: its poison overflow flag may be replaced with concrete false. -/
theorem Arith.tryFold_addui_extended_correct (verified : op.Verified ctx opIn)
    (opType : op.getOpType! ctx.raw = .arith .addui_extended) :
    FoldTable.CorrectAt ctx op verified := by
  obtain ⟨type, carry, hCarry, hOperands, hResults⟩ := arith_addui_extended_types verified opType
  apply FoldTable.correctAt_int_rhs verified hOperands (fun width => .val (0#width))
    (decisions := #[.useOperand 0, .useConstant (.int 1 (.val 0))]) (fun _ _ h => by
      have h := opType ▸ h
      simp only [HasOpInfo.tryFold, OpCode.tryFold, Arith.tryFold] at h
      grind [Array.toList_inj])
  · rw [hOperands, hResults, FoldDecision.hasTypes_pair]
    exact ⟨rfl, hCarry⟩
  · simp only [OperationPtr.interpret]
    rw [opType]
    simp [FoldDecision.resolveAll, FoldDecision.resolve, Veir.interpretOp', Arith.interpretOp',
      LLVM.Int.cast_self, fold_add_zero, Interp.isRefinedBy, OperationResult.isRefinedBy,
      RuntimeValue.isRefinedBy, overflow_zero]

/-- Verified LLVM add-zero is correct for every choice of overflow flags. -/
theorem Llvm.tryFold_add_correct (verified : op.Verified ctx opIn)
    (opType : op.getOpType! ctx.raw = .llvm .add) :
    FoldTable.CorrectAt ctx op verified := by
  obtain ⟨type, hOperands, hResults⟩ := (verified.llvm_add opType).types
  apply FoldTable.correctAt_int_rhs verified hOperands (fun width => .val (0#width))
    (decisions := #[.useOperand 0]) (fun _ _ h => by
      have h := opType ▸ h
      simp only [HasOpInfo.tryFold, OpCode.tryFold, Llvm.tryFold] at h
      grind [Array.toList_inj])
  · simp [hOperands, hResults, FoldDecision.HasType]
  · simp only [OperationPtr.interpret]
    rw [opType]
    simp [FoldDecision.resolveAll, FoldDecision.resolve, Veir.interpretOp', Llvm.interpretOp',
      LLVM.Int.cast_self, fold_add_zero, Interp.isRefinedBy]

/-- The RISC-V immediate-and-zero entry is correct for every register value.
The operand and result may have different register allocations. The successful
lookup itself establishes that the immediate is zero. -/
theorem Riscv.tryFold_andi_correct (verified : op.Verified ctx opIn)
    (opType : op.getOpType! ctx.raw = .riscv .andi) :
    FoldTable.CorrectAt ctx op verified := by
  obtain ⟨operandType, resultType, hOperands, hResults⟩ := riscv_andi_types verified opType
  constructor
  · intro known decisions _ hFold
    obtain ⟨_, rfl⟩ := riscv_andi_lookup (opType ▸ hFold)
    simp [hResults, FoldDecision.HasType]
  · intro known decisions hFold operands hConform _ memory layout
    obtain ⟨hZero, rfl⟩ := riscv_andi_lookup (opType ▸ hFold)
    obtain ⟨value, rfl⟩ := (hOperands ▸ hConform).reg_single
    rw [OperationPtr.interpret, opType]
    simp [FoldDecision.resolveAll, FoldDecision.resolve, Veir.interpretOp', Riscv.interpretOp',
      RISCVImmediateProperties.immField, hZero, RISCV.andi, Interp.isRefinedBy]

end Veir
