module

public import Veir.Interpreter.ResultsConform

import all Veir.Interpreter.CTreeInterpreter
import all Veir.Interpreter.Basic
import all Veir.Dialects.RISCV_Cf.OpInfo
import all Veir.Verifier

public section

/-!
# The results of the `riscv_cf` operations conform to their types

Every `riscv_cf` operation that returns is a branch or a return, both terminators, which return no
results. `riscv_cf.func` and `riscv_cf.call` fail and `riscv_cf.unreachable` is undefined
behavior.
-/

namespace Veir

/-- The results of a CTree run of every `riscv_cf` opcode conform to their types. -/
theorem OpCode.resultsConform_riscv_cf (cfOp : Riscv_Cf) :
    OpCode.ResultsConform (.riscv_cf cfOp) := by
  refine OpCode.resultsConform_def.mpr
    fun ctx op opIn hType opVerif operands mem conforms vals mem' act h => ?_
  have hType! : op.getOpType! ctx.raw = .riscv_cf cfOp := by
    rw [OperationPtr.getOpType!_eq_getOpType opIn]; exact hType
  rw [OperationPtr.interpretCTree_def!, hType!] at h
  simp only [CTree.interpretOp', CTree.MayReturn.monadLift_iff, interpretOp'] at h
  simp only [OperationPtr.Verified, OperationPtr.verifyLocalInvariants,
    HasOpInfo.verifyLocalInvariants, OpCode.verifyLocalInvariants,
    ← OperationPtr.getOpType!_eq_getOpType, hType!] at opVerif
  cases cfOp
  case func | call | unreachable => simp [Riscv_Cf.interpretOp'] at h
  all_goals
    have hR : op.getNumResults! ctx.raw = 0 := by
      simp only [Riscv_Cf.verifyLocalInvariants, OperationPtr.verifyUnconditionalBranch] at opVerif
      first
        | exact OperationPtr.verifyTerminatorCounts_eq_ok (Except.ok_left_of_bind_ok opVerif)
        | exact OperationPtr.verifyTerminatorCounts_eq_ok
            (Except.ok_left_of_bind_ok (Except.ok_left_of_bind_ok opVerif))
    obtain rfl : vals = #[] := by
      simp only [Riscv_Cf.interpretOp'] at h
      (repeat' split at h) <;>
        first
          | (simp at h; done)
          | (simp only [Interp.pure_eq] at h; grind)
    exact ⟨by simp [OperationPtr.getResultTypes!.size_eq_getNumResults!, hR], by simp⟩

instance (cfOp : Riscv_Cf) : ResultsConform (.riscv_cf cfOp) :=
  ⟨OpCode.resultsConform_riscv_cf cfOp⟩

end Veir

end
