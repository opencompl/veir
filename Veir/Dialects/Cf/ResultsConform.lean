module

public import Veir.Interpreter.ResultsConform

import all Veir.Interpreter.CTreeInterpreter
import all Veir.Dialects.Cf.OpInfo
import all Veir.Verifier

public section

/-!
# The results of the `cf` operations conform to their types

Both `cf` operations are terminators, which return no results, so their results trivially conform.
-/

namespace Veir

/-- A verified `cf` operation declares no results: both its opcodes are terminators. -/
private theorem cf_numResults_eq_zero {ctx : WfIRContext OpCode} {op : OperationPtr}
    {opIn : op.InBounds ctx.raw} {cfOp : Cf} (hType : op.getOpType! ctx.raw = .cf cfOp)
    (opVerif : op.Verified ctx opIn) : op.getNumResults! ctx.raw = 0 := by
  have hV : Cf.verifyLocalInvariants cfOp op ctx opIn = .ok () := by
    simp only [OperationPtr.Verified, OperationPtr.verifyLocalInvariants,
      HasOpInfo.verifyLocalInvariants, OpCode.verifyLocalInvariants,
      ← OperationPtr.getOpType!_eq_getOpType, hType] at opVerif
    exact opVerif
  cases cfOp with
  | br =>
    simp only [Cf.verifyLocalInvariants, OperationPtr.verifyUnconditionalBranch] at hV
    exact OperationPtr.verifyTerminatorCounts_eq_ok (Except.ok_left_of_bind_ok hV)
  | cond_br =>
    simp only [Cf.verifyLocalInvariants] at hV
    exact OperationPtr.verifyTerminatorCounts_eq_ok (Except.ok_left_of_bind_ok hV)

/-- The results of a CTree run of every `cf` opcode conform to their types. -/
theorem OpCode.resultsConform_cf (cfOp : Cf) : OpCode.ResultsConform (.cf cfOp) := by
  refine OpCode.resultsConform_def.mpr
    fun ctx op opIn hType opVerif operands mem conforms vals mem' act h => ?_
  have hType! : op.getOpType! ctx.raw = .cf cfOp := by
    rw [OperationPtr.getOpType!_eq_getOpType opIn]; exact hType
  have hR := cf_numResults_eq_zero hType! opVerif
  obtain rfl : vals = #[] := by
    rw [OperationPtr.interpretCTree_def!, hType!] at h
    simp only [CTree.interpretOp', CTree.MayReturn.monadLift_iff] at h
    simp only [interpretOp', Cf.interpretOp'] at h
    cases cfOp <;> (repeat' split at h) <;>
      first
        | (simp at h; done)
        | (simp only [Interp.pure_eq] at h; grind)
  exact ⟨by simp [OperationPtr.getResultTypes!.size_eq_getNumResults!, hR], by simp⟩

instance (cfOp : Cf) : ResultsConform (.cf cfOp) := ⟨OpCode.resultsConform_cf cfOp⟩

end Veir

end
