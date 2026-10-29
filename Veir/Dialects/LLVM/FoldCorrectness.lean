module

public import Veir.Interfaces.FoldInterfaces.Correctness
import Veir.Interpreter.Refinement.Lemmas
public import Veir.Data.LLVM.Int.Lemmas

import all Veir.IR.Basic
import all Veir.Interpreter.Basic
import all Veir.GlobalOpInfo
import all Veir.Dialects.LLVM.OpInfo
import all Veir.Data.LLVM.Int.Basic

/-!
# Correctness of the `llvm` fold table

Each theorem covers every successful lookup for a verified operation of its
opcode, with arbitrary known operands and properties.
-/

public section

namespace Veir
open Data

variable {ctx : WfIRContext OpCode} {op : OperationPtr} {opIn : op.InBounds ctx.raw}

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
  · grind [FoldDecision.HasType]
  · simp only [OperationPtr.interpret]
    rw [opType]
    simp [FoldDecision.resolveAll, FoldDecision.resolve, Veir.interpretOp', Llvm.interpretOp',
      LLVM.Int.cast_self, LLVM.Int.add_zero, Interp.isRefinedBy]

end Veir
