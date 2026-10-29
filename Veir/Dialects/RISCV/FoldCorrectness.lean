module

public import Veir.Interfaces.FoldInterfaces.Correctness
import Veir.Interpreter.Refinement.Lemmas

import all Veir.GlobalOpInfo
import all Veir.Verifier
import all Veir.Verifier.Basic
import all Veir.Dialects.RISCV.OpInfo
import all Veir.Dialects.RISCV.Properties
import all Veir.Data.RISCV.Reg.Basic

/-!
# Correctness of the `riscv` fold table

Each theorem covers every successful lookup for a verified operation of its
opcode, with arbitrary known operands and properties.
-/

public section

namespace Veir
open Data

/-- The operand and result types of a verified `riscv.andi`: one register each, possibly with
different allocations. -/
theorem OperationPtr.Verified.riscv_andi {ctx : WfIRContext OpCode} {op : OperationPtr}
    {opInBounds} (opVerify : op.Verified ctx opInBounds)
    (opType : op.getOpType! ctx.raw = .riscv .andi) :
    ∃ operandType resultType : RegisterType,
      op.getOperandTypes! ctx.raw = #[(operandType : TypeAttr)] ∧
      op.getResultTypes! ctx.raw = #[(resultType : TypeAttr)] := by
  simp only [OperationPtr.Verified, OperationPtr.verifyLocalInvariants,
    HasOpInfo.verifyLocalInvariants, OpCode.verifyLocalInvariants,
    ← OperationPtr.getOpType!_eq_getOpType, opType, Riscv.verifyLocalInvariants] at opVerify
  obtain ⟨_, hTypes, hCounts⟩ := Except.bind_eq_ok.mp opVerify
  simp only [OperationPtr.verifyRISCVimm12, OperationPtr.verifyPlainOpCounts, ne_eq, bind,
    Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at hCounts
  have hCounts : (op.getOperandTypes! ctx.raw).size = 1 ∧
      op.getNumResults ctx.raw opInBounds = 1 := by grind
  simp [OperationPtr.verifyRISCVRegisterTypes, hCounts, bind, Except.bind, throw,
    throwThe, MonadExceptOf.throw, pure, Except.pure] at hTypes
  simp [Array.ext_iff, TypeAttr.inj, ← Attribute.registerType_eq_of, hCounts,
    OperationPtr.getResultTypes!.size_eq_getNumResults!,
    OperationPtr.getNumResults!_eq_getNumResults opInBounds]
  grind

private theorem riscv_andi_lookup
    (h : HasOpInfo.tryFold (OpCode.riscv .andi) properties types known = some decisions) :
    properties.value = 0 ∧ decisions = #[.useConstant (.reg ⟨0⟩)] := by
  simp only [HasOpInfo.tryFold, OpCode.tryFold, Riscv.tryFold] at h
  grind

variable {ctx : WfIRContext OpCode} {op : OperationPtr}

/-- The RISC-V immediate-and-zero entry is correct for every register value.
The operand and result may have different register allocations. The successful
lookup itself establishes that the immediate is zero. -/
theorem Riscv.tryFold_andi_correct (opType : op.getOpType! ctx.raw = .riscv .andi) :
    FoldTable.CorrectAt ctx op := .of_verified fun _ verified => by
  obtain ⟨operandType, resultType, hOperands, hResults⟩ := verified.riscv_andi opType
  constructor
  · intro _ _ known decisions _ hFold
    obtain ⟨_, rfl⟩ := riscv_andi_lookup (opType ▸ hFold)
    simp [hResults, FoldDecision.HasType]
  · intro _ _ known decisions hFold operands hConform _ memory layout
    obtain ⟨hZero, rfl⟩ := riscv_andi_lookup (opType ▸ hFold)
    obtain ⟨value, rfl⟩ := by simpa [hOperands] using hConform
    rw [OperationPtr.interpret, opType]
    simp [FoldDecision.resolveAll, FoldDecision.resolve, Veir.interpretOp', Riscv.interpretOp',
      RISCVImmediateProperties.immField, hZero, RISCV.andi, Interp.isRefinedBy]

end Veir
