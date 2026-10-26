module

public import Veir.Passes.DCE.OperationRefinement
public import Veir.Interpreter.CTreeRefinement.RegionNormalization

import all Veir.Interpreter.CTreeInterpreter
import all Veir.Interpreter.CTreeRefinement.Embedding
import all Veir.Interpreter.CTree
import all CTree.Defs
import all CTree.Interp

public section

open CTree

namespace Veir.CTree

/-- The closed operation interpreter retains both event-handler layers used by
ordinary region interpretation, including their silent steps. -/
theorem interpretOp_eq_embedOperationTree (op : OperationPtr) {ctx : WfIRContext OpCode}
    (state : InterpreterState ctx) (opIn : op.InBounds ctx.raw) :
    interpretOp op state opIn =
      Tree.embedRegion ctx (InterpreterState ctx) (interpretOperationTree op state opIn) := by
  cases hoperands : state.variables.getOperandValues op with
  | none => simp [interpretOp, interpretOperationTree, hoperands]
  | some operands =>
    simp only [interpretOp, interpretOperationTree, hoperands]
    simp only [interpretOp']
    rw [Tree.interp_embedRegion ctx MemoryState]
    rw [Tree.interp_embedRegion_closed ctx ctx MemoryState (InterpreterState ctx) _ (by intro; rfl)]
    simp only [Bind.bind]
    rw [Tree.embedRegion_bind]
    congr 1
    · simp only [Tree.inflate]
      congr 3 <;> grind
    · funext result
      cases hresults : state.variables.setResultValues? op result.1 opIn <;> simp

end Veir.CTree
