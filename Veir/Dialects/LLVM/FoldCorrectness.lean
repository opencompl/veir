module

public import Veir.Interfaces.FoldInterfaces.Correctness
import Veir.Interpreter.Refinement.Lemmas
import Veir.Data.LLVM.Int.FoldLemmas

import all Veir.GlobalOpInfo
import all Veir.Dialects.LLVM.OpInfo

/-!
# Correctness of the `llvm` fold table

Each theorem covers every successful lookup for a verified operation of its
opcode, with arbitrary known operands and properties.
-/

public section

namespace Veir
open Data

private theorem llvm_add_lookup
    (h : HasOpInfo.tryFold (OpCode.llvm .add) properties types known = some decisions) :
    ∃ left width, known = #[left, some (.int width (.val (0#width)))] ∧
      decisions = #[.useOperand 0] := by
  simp only [HasOpInfo.tryFold, OpCode.tryFold, Llvm.tryFold] at h
  grind [Array.toList_inj]

variable {ctx : WfIRContext OpCode} {op : OperationPtr}

/-- Verified LLVM add-zero is correct for every choice of overflow flags. -/
theorem Llvm.tryFold_add_correct (opType : op.getOpType! ctx.raw = .llvm .add) :
    FoldTable.CorrectAt ctx op := .of_verified fun _ verified => by
  obtain ⟨type, hOperands, hResults⟩ := (verified.llvm_add opType).types
  apply FoldTable.correctAt_int_rhs hOperands (fun width => .val (0#width))
    (decisions := #[.useOperand 0])
    (fun _ _ h => llvm_add_lookup (opType ▸ h))
  · grind [FoldDecision.HasType]
  · simp only [OperationPtr.interpret]
    rw [opType]
    simp [FoldDecision.resolveAll, FoldDecision.resolve, Veir.interpretOp', Llvm.interpretOp',
      LLVM.Int.cast_self, LLVM.Int.add_zero, Interp.isRefinedBy]

end Veir
