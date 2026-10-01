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
  cases x with
  | poison => rfl
  | val x =>
    simp [LLVM.Int.add, Id.run, BitVec.saddOverflow, BitVec.uaddOverflow,
      Nat.not_le.mpr x.isLt, Int.not_le.mpr (BitVec.toInt_lt (x := x)),
      Int.not_lt.mpr (BitVec.le_toInt x)]

private theorem overflow_zero (x : LLVM.Int w) :
    LLVM.Int.uaddOverflowFlag x (.val (0#w)) ⊒ .val (0#1) := by
  cases x with
  | poison => simp [LLVM.Int.uaddOverflowFlag, Id.run, isRefinedBy]
  | val x =>
    simp [LLVM.Int.uaddOverflowFlag, Id.run, BitVec.uaddOverflow,
      Nat.not_le.mpr x.isLt, isRefinedBy]

private theorem arith_addi_lookup
    (h : HasOpInfo.tryFold (OpCode.arith .addi) properties types known = some decisions) :
    ∃ lhs bw, known = #[lhs, some (.int bw (.val 0))] ∧
      decisions = #[.useOperand 0] := by
  change Arith.tryFold .addi properties types known = some decisions at h
  unfold Arith.tryFold at h
  repeat first | split at h | contradiction
  all_goals grind [Array.toList_inj]

private theorem arith_addui_extended_lookup
    (h : HasOpInfo.tryFold (OpCode.arith .addui_extended) properties types known = some decisions) :
    ∃ lhs bw, known = #[lhs, some (.int bw (.val 0))] ∧
      decisions = #[.useOperand 0, .useConstant (.int 1 (.val 0))] := by
  change Arith.tryFold .addui_extended properties types known = some decisions at h
  unfold Arith.tryFold at h
  repeat first | split at h | contradiction
  all_goals grind [Array.toList_inj]

private theorem llvm_add_lookup
    (h : HasOpInfo.tryFold (OpCode.llvm .add) properties types known = some decisions) :
    ∃ lhs bw, known = #[lhs, some (.int bw (.val 0))] ∧
      decisions = #[.useOperand 0] := by
  change Llvm.tryFold .add properties types known = some decisions at h
  unfold Llvm.tryFold at h
  repeat first | split at h | contradiction
  all_goals grind [Array.toList_inj]

private theorem riscv_andi_lookup
    (h : HasOpInfo.tryFold (OpCode.riscv .andi) properties types known = some decisions) :
    properties.value = 0 ∧ decisions = #[.useConstant (.reg ⟨0⟩)] := by
  change Riscv.tryFold .andi properties types known = some decisions at h
  unfold Riscv.tryFold at h
  repeat first | split at h | contradiction
  all_goals grind

variable {ctx : WfIRContext OpCode} {op : OperationPtr} {opIn : op.InBounds ctx.raw}

private theorem arith_addui_extended_types (verified : op.Verified ctx opIn)
    (opType : op.getOpType! ctx.raw = .arith .addui_extended) :
    ∃ type carry : IntegerType, carry.bitwidth = 1 ∧
      op.getOperandTypes! ctx.raw = #[(type : TypeAttr), (type : TypeAttr)] ∧
      op.getResultTypes! ctx.raw = #[(type : TypeAttr), (carry : TypeAttr)] := by
  simp only [OperationPtr.Verified, OperationPtr.verifyLocalInvariants,
    HasOpInfo.verifyLocalInvariants, OpCode.verifyLocalInvariants,
    ← OperationPtr.getOpType!_eq_getOpType, opType, Arith.verifyLocalInvariants] at verified
  replace verified := Except.ok_of_bind_ok verified
  obtain ⟨_, h, _⟩ := Except.bind_eq_ok.mp verified
  simp only [OperationPtr.verifyArithExtendedOp, OperationPtr.verifyPlainOpCounts,
    OperationPtr.verifyOperandTypesMatch, OperationPtr.verifyResultTypeMatches,
    TypeAttr.verifyIntegerType, TypeAttr.verifyI1, ne_eq, bind, Except.bind, throw,
    throwThe, MonadExceptOf.throw, pure, Except.pure, ite_true] at h
  have hOperand : ∃ type : IntegerType,
      ((op.getOperand! ctx.raw 0).getType! ctx.raw).val = .integerType type := by grind
  have hCarry : ∃ type : IntegerType,
      ((op.getResult 1).get! ctx.raw).type.val = .integerType type := by
    cases ht : ((op.getResult 1).get! ctx.raw).type.val with
    | integerType type => exact ⟨type, rfl⟩
    | _ => simp only [ht] at h; grind
  obtain ⟨type, hOperand⟩ := hOperand
  obtain ⟨carry, hCarry⟩ := hCarry
  have hshape : op.getNumResults! ctx.raw = 2 ∧ op.getNumOperands! ctx.raw = 2 ∧
      ∃ type carry : IntegerType, carry.bitwidth = 1 ∧
        ((op.getOperand! ctx.raw 0).getType! ctx.raw).val = .integerType type ∧
        ((op.getOperand! ctx.raw 1).getType! ctx.raw).val = .integerType type ∧
        ((op.getResult 0).get! ctx.raw).type.val = .integerType type ∧
        ((op.getResult 1).get! ctx.raw).type.val = .integerType carry := by
    refine ⟨?_, ?_, type, carry, ?_, hOperand, ?_, ?_, hCarry⟩ <;> grind
  obtain ⟨_, _, type, carry, hcarry, h0, h1, hr0, hr1⟩ := hshape
  have h0 : (op.getOperand! ctx.raw 0).getType! ctx.raw = (type : TypeAttr) := TypeAttr.inj.mpr h0
  have h1 : (op.getOperand! ctx.raw 1).getType! ctx.raw = (type : TypeAttr) := TypeAttr.inj.mpr h1
  have hr0 : ((op.getResult 0).get! ctx.raw).type = (type : TypeAttr) := TypeAttr.inj.mpr hr0
  have hr1 : ((op.getResult 1).get! ctx.raw).type = (carry : TypeAttr) := TypeAttr.inj.mpr hr1
  refine ⟨type, carry, hcarry, ?_, ?_⟩ <;> apply Array.ext <;> grind

private theorem riscv_andi_types (verified : op.Verified ctx opIn)
    (opType : op.getOpType! ctx.raw = .riscv .andi) :
    ∃ operandType resultType : RegisterType,
      op.getOperandTypes! ctx.raw = #[(operandType : TypeAttr)] ∧
      op.getResultTypes! ctx.raw = #[(resultType : TypeAttr)] := by
  simp only [OperationPtr.Verified, OperationPtr.verifyLocalInvariants,
    HasOpInfo.verifyLocalInvariants, OpCode.verifyLocalInvariants,
    ← OperationPtr.getOpType!_eq_getOpType, opType, Riscv.verifyLocalInvariants] at verified
  obtain ⟨_, hTypes, hCounts⟩ := Except.bind_eq_ok.mp verified
  obtain ⟨_, hImm, _⟩ := Except.bind_eq_ok.mp hCounts
  obtain ⟨_, hCounts, _⟩ := Except.bind_eq_ok.mp hImm
  simp only [OperationPtr.verifyPlainOpCounts, ne_eq, bind, Except.bind, throw,
    throwThe, MonadExceptOf.throw, pure, Except.pure] at hCounts
  have hOperands : (op.getOperandTypes! ctx.raw).size = 1 := by grind
  have hResults : op.getNumResults ctx.raw opIn = 1 := by grind
  obtain ⟨operandType, hOperands⟩ := Array.size_eq_one_iff.mp hOperands
  simp [OperationPtr.verifyRISCVRegisterTypes, hOperands, hResults] at hTypes
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw,
    pure, Except.pure, Functor.map, Except.map] at hTypes
  have hshape : ∃ a b : RegisterType,
      operandType.val = .registerType a ∧ ((op.getResult 0).get! ctx.raw).type.val = .registerType b := by
    grind
  obtain ⟨a, b, ha, hb⟩ := hshape
  have ha : operandType = (a : TypeAttr) := TypeAttr.inj.mpr ha
  have hb : ((op.getResult 0).get! ctx.raw).type = (b : TypeAttr) := TypeAttr.inj.mpr hb
  subst operandType
  refine ⟨a, b, hOperands, ?_⟩
  apply Array.ext <;> grind

/-- The verified arithmetic add-zero entry, including arbitrary overflow flags and poison inputs. -/
theorem Arith.tryFold_addi_correct (verified : op.Verified ctx opIn)
    (opType : op.getOpType! ctx.raw = .arith .addi) :
    FoldTable.CorrectAt ctx op verified := by
  obtain ⟨type, hOperands, hResults⟩ := (verified.arith_addi opType).types
  apply FoldTable.correctAt_int_rhs verified hOperands (fun width => .val (0#width))
    (fun _ _ h => arith_addi_lookup (by rw [opType] at h; exact h))
  · simp [hOperands, hResults, FoldDecision.HasType]
  · intro lhs memory layout
    refine ⟨#[.int type.bitwidth lhs], ?_, ?_⟩
    · simp [FoldDecision.resolveAll, FoldDecision.resolve]
    · simp only [OperationPtr.interpret]
      rw [opType]
      simp [Veir.interpretOp', Arith.interpretOp',
        LLVM.Int.cast_self, fold_add_zero, Interp.isRefinedBy, OperationResult.isRefinedBy,
        ControlFlowAction.optionIsRefinedBy]

/-- The extended-add entry refines both results, even when the unknown operand
is poison: its poison overflow flag may be replaced with concrete false. -/
theorem Arith.tryFold_addui_extended_correct (verified : op.Verified ctx opIn)
    (opType : op.getOpType! ctx.raw = .arith .addui_extended) :
    FoldTable.CorrectAt ctx op verified := by
  obtain ⟨type, carry, hCarry, hOperands, hResults⟩ := arith_addui_extended_types verified opType
  apply FoldTable.correctAt_int_rhs verified hOperands (fun width => .val (0#width))
    (fun _ _ h => arith_addui_extended_lookup (by rw [opType] at h; exact h))
  · rw [hOperands, hResults, FoldDecision.hasTypes_pair]
    exact ⟨rfl, hCarry⟩
  · intro lhs memory layout
    refine ⟨#[.int type.bitwidth lhs, .int 1 (.val 0)], ?_, ?_⟩
    · simp [FoldDecision.resolveAll, FoldDecision.resolve]
    · simp only [OperationPtr.interpret]
      rw [opType]
      simp [Veir.interpretOp', Arith.interpretOp',
        LLVM.Int.cast_self, fold_add_zero, Interp.isRefinedBy, OperationResult.isRefinedBy,
        ControlFlowAction.optionIsRefinedBy, RuntimeValue.isRefinedBy, overflow_zero]

/-- Verified LLVM add-zero is correct for every choice of overflow flags. -/
theorem Llvm.tryFold_add_correct (verified : op.Verified ctx opIn)
    (opType : op.getOpType! ctx.raw = .llvm .add) :
    FoldTable.CorrectAt ctx op verified := by
  obtain ⟨type, hOperands, hResults⟩ := (verified.llvm_add opType).types
  apply FoldTable.correctAt_int_rhs verified hOperands (fun width => .val (0#width))
    (fun _ _ h => llvm_add_lookup (by rw [opType] at h; exact h))
  · simp [hOperands, hResults, FoldDecision.HasType]
  · intro lhs memory layout
    refine ⟨#[.int type.bitwidth lhs], ?_, ?_⟩
    · simp [FoldDecision.resolveAll, FoldDecision.resolve]
    · simp only [OperationPtr.interpret]
      rw [opType]
      simp [Veir.interpretOp', Llvm.interpretOp',
        LLVM.Int.cast_self, fold_add_zero, Interp.isRefinedBy, OperationResult.isRefinedBy,
        ControlFlowAction.optionIsRefinedBy]

/-- The RISC-V immediate-and-zero entry is correct for every register value.
The operand and result may have different register allocations. The successful
lookup itself establishes that the immediate is zero. -/
theorem Riscv.tryFold_andi_correct (verified : op.Verified ctx opIn)
    (opType : op.getOpType! ctx.raw = .riscv .andi) :
    FoldTable.CorrectAt ctx op verified := by
  obtain ⟨operandType, resultType, hOperands, hResults⟩ := riscv_andi_types verified opType
  constructor
  · intro known decisions _ hFold
    obtain ⟨_, rfl⟩ := riscv_andi_lookup (by rw [opType] at hFold; exact hFold)
    simp [hResults, FoldDecision.HasType]
  · intro known decisions hFold operands hConform _ memory layout
    obtain ⟨hZero, rfl⟩ := riscv_andi_lookup (by rw [opType] at hFold; exact hFold)
    rw [hOperands] at hConform
    obtain ⟨value, rfl⟩ := hConform.reg_single
    refine ⟨#[.reg ⟨0⟩], ?_, ?_⟩
    · simp [FoldDecision.resolveAll, FoldDecision.resolve]
    · simp only [OperationPtr.interpret]
      rw [opType]
      simp [Veir.interpretOp', Riscv.interpretOp',
        RISCVImmediateProperties.immField, hZero, RISCV.andi, Interp.isRefinedBy,
        OperationResult.isRefinedBy, ControlFlowAction.optionIsRefinedBy]

end Veir
