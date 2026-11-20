module

public import Veir.Interpreter.ResultsConform

import all Veir.Interpreter.CTreeInterpreter
import all Veir.Interpreter.Basic

public section

/-!
# The results of the `test` operations conform to their types

A `test` operation has no semantics: interpreting it fails, so it returns no results.
-/

namespace Veir

/-- The results of a CTree run of every `test` opcode conform to their types. -/
theorem OpCode.resultsConform_test (testOp : Test) : OpCode.ResultsConform (.test testOp) := by
  refine OpCode.resultsConform_def.mpr fun ctx op opIn hType _ _ _ _ _ _ _ h => ?_
  have hType! : op.getOpType! ctx.raw = .test testOp := by
    rw [OperationPtr.getOpType!_eq_getOpType opIn]; exact hType
  rw [OperationPtr.interpretCTree_def!, hType!] at h
  simp [CTree.interpretOp', interpretOp'] at h

instance (testOp : Test) : ResultsConform (.test testOp) := ⟨OpCode.resultsConform_test testOp⟩

end Veir

end
