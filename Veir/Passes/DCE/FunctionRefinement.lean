module

public import Veir.Passes.DCE.CFGNormalization
public import Veir.Interpreter.CTreeRefinement.Program

import all Veir.Interpreter.CTreeInterpreter
import all Veir.Interpreter.VariableState
import all Veir.Passes.DCE.StateRefinement

public section

open CTree

namespace Veir.DCE

/-- A direct refinement proof for the closed CFG gives refinement through the
existing memory-aware function API. Only the successful return relation is projected. -/
theorem functionRefines_of_closedCFG
    {sourceCtx targetCtx : WfIRContext OpCode} {sourceOp targetOp : OperationPtr}
    (source : FunctionOp sourceCtx.raw sourceOp) (target : FunctionOp targetCtx.raw targetOp)
    (sourceIn : sourceOp.InBounds sourceCtx.raw) (targetIn : targetOp.InBounds targetCtx.raw)
    (sourceRegions : sourceOp.getNumRegions sourceCtx.raw sourceIn = 1)
    (targetRegions : targetOp.getNumRegions targetCtx.raw targetIn = 1)
    (live : ValuePtr → Prop)
    (hcfg : ∀ (sourceValues targetValues : Array RuntimeValue) (memory : MemoryState),
      RuntimeValue.arrayIsRefinedBy sourceValues targetValues →
      Tree.Refines (CFGReturnRefinesOn live)
        (CTree.interpretCFGTree (source.getFunctionBody sourceIn (by omega)) sourceValues
          (⟨.empty sourceCtx, memory⟩ : InterpreterState sourceCtx))
        (CTree.interpretCFGTree (target.getFunctionBody targetIn (by omega)) targetValues
          (⟨.empty targetCtx, memory⟩ : InterpreterState targetCtx))) :
    Tree.Refinement.FunctionOp.isRefinedBy source target sourceIn targetIn := by
  intro sourceValues targetValues memory hvalues
  simp only [CTree.interpretFunctionWithMemory, sourceRegions, targetRegions,
    ne_eq, not_true_eq_false, dite_false]
  rw [CTree.interpretRegion_eq_inflateCFGTree, CTree.interpretRegion_eq_inflateCFGTree]
  apply Tree.refines_bind (Tree.refines_inflate (hcfg sourceValues targetValues memory hvalues))
  intro sourceResult targetResult hresult
  apply (Tree.refines_pure _ _ _).mpr
  simp only [CFGReturnRefinesOn, StatesRefineOn] at hresult
  exact ⟨hresult.1.1, hresult.2⟩

end Veir.DCE
