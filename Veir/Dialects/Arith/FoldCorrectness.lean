module

public import Veir.Interfaces.FoldInterfaces.Correctness
import Veir.Interpreter.Refinement.Lemmas
import Veir.Data.LLVM.Int.Lemmas

import all Veir.GlobalOpInfo
import all Veir.Dialects.Arith.OpInfo

/-!
# Correctness of the `arith` fold table

Each theorem covers every successful lookup for a verified operation of its
opcode, with arbitrary known operands and properties.
-/

public section

namespace Veir
open Data

variable {ctx : WfIRContext OpCode} {op : OperationPtr}

/-- The verified arithmetic add-zero entry, including arbitrary overflow flags and poison inputs. -/
theorem Arith.tryFold_addi_correct (opType : op.getOpType! ctx.raw = .arith .addi) :
    FoldTable.CorrectAt ctx op := .of_verified fun _ verified => by
  obtain ⟨type, hOperands, hResults⟩ := (verified.arith_addi opType).types
  apply FoldTable.correctAt_int_rhs hOperands (fun width => .val (0#width))
    (decisions := #[.useOperand 0]) (fun _ _ h => by
      have h := opType ▸ h
      simp only [HasOpInfo.tryFold, OpCode.tryFold, Arith.tryFold] at h
      grind [Array.toList_inj])
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
    (decisions := #[.useOperand 0, .useConstant (.int 1 (.val 0))]) (fun _ _ h => by
      have h := opType ▸ h
      simp only [HasOpInfo.tryFold, OpCode.tryFold, Arith.tryFold] at h
      grind [Array.toList_inj])
  · grind [FoldDecision.HasType]
  · simp only [OperationPtr.interpret]
    rw [opType]
    simp [FoldDecision.resolveAll, FoldDecision.resolve, Veir.interpretOp', Arith.interpretOp',
      LLVM.Int.cast_self, LLVM.Int.add_zero, Interp.isRefinedBy, OperationResult.isRefinedBy,
      RuntimeValue.isRefinedBy, LLVM.Int.uaddOverflowFlag_zero]

end Veir
