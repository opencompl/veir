module

public import Veir.Interpreter.ResultsConform

import all Veir.Interpreter.CTreeInterpreter
import all Veir.Interpreter.Basic
import all Veir.Dialects.Func.OpInfo
import all Veir.Verifier

public section

/-!
# The results of the `func` operations conform to their types

`func.return` is a terminator, which returns no results, and the other `func` operations fail.
-/

namespace Veir

/-- The results of a CTree run of every `func` opcode conform to their types. -/
theorem OpCode.resultsConform_func (funcOp : Func) : OpCode.ResultsConform (.func funcOp) := by
  refine OpCode.resultsConform_def.mpr
    fun ctx op opIn hType opVerif operands mem conforms vals mem' act h => ?_
  have hType! : op.getOpType! ctx.raw = .func funcOp := by
    rw [OperationPtr.getOpType!_eq_getOpType opIn]; exact hType
  rw [OperationPtr.interpretCTree_def!, hType!] at h
  simp only [CTree.interpretOp', CTree.MayReturn.monadLift_iff] at h
  cases funcOp
  case «return» =>
    simp only [interpretOp', Interp.pure_eq, Interp.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -, -⟩ := h
    simp only [OperationPtr.Verified, OperationPtr.verifyLocalInvariants,
      HasOpInfo.verifyLocalInvariants, OpCode.verifyLocalInvariants,
      ← OperationPtr.getOpType!_eq_getOpType, hType!, Func.verifyLocalInvariants] at opVerif
    have hR := OperationPtr.verifyTerminatorCounts_eq_ok (Except.ok_left_of_bind_ok opVerif)
    exact ⟨by simp [OperationPtr.getResultTypes!.size_eq_getNumResults!, hR], by simp⟩
  all_goals simp [interpretOp'] at h

instance (funcOp : Func) : ResultsConform (.func funcOp) := ⟨OpCode.resultsConform_func funcOp⟩

end Veir

end
