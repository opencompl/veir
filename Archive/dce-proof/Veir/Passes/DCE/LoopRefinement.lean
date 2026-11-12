module

public import Veir.Passes.DCE.CFGNormalization
public import Veir.Passes.DCE.MacroSteps

import all Veir.Passes.DCE.CFGRefinement
import all Veir.Interpreter.CTreeRefinement.Iteration

public section

open CTree

namespace Veir.DCE

/-- One direct simulation of the original program's grouped CFG body lifts to
its whole CFG. The finite grouping is an exact equality, not semantic composition. -/
theorem ErasureTrace.interpretCFGTree_refines_of_macroBody
    {sourceCtx targetCtx : WfIRContext OpCode} {operations : List OperationPtr}
    (trace : ErasureTrace sourceCtx operations targetCtx)
    (operationAt : (CTree.interpretCFG.StateLocation sourceCtx × InterpreterState sourceCtx) →
      Option OperationPtr)
    (live : ValuePtr → Prop)
    (hbody : ∀ (source : CTree.interpretCFG.StateLocation sourceCtx × InterpreterState sourceCtx)
      (target : CTree.interpretCFG.StateLocation targetCtx × InterpreterState targetCtx),
      CFGStateRefinesOn live Eq source target →
      Tree.Refines (Sum.LiftRel (CFGStateRefinesOn live Eq) (CFGReturnRefinesOn live))
        (macroBody operationAt
          (fun (location, state) => CTree.interpretCFGTreeStep location state) operations source)
        (CTree.interpretCFGTreeStep target.1 target.2))
    (region : RegionPtr) (sourceValues targetValues : Array RuntimeValue)
    (source : InterpreterState sourceCtx) (target : InterpreterState targetCtx)
    (sourceIn : region.InBounds sourceCtx.raw) (targetIn : region.InBounds targetCtx.raw)
    (hvalues : RuntimeValue.arrayIsRefinedBy sourceValues targetValues)
    (hstate : StatesRefineOn live source target) :
    Tree.Refines (CFGReturnRefinesOn live)
      (CTree.interpretCFGTree region sourceValues source sourceIn)
      (CTree.interpretCFGTree region targetValues target targetIn) := by
  have hfirst := trace.erasures.region_firstBlock region
  simp only [CTree.interpretCFGTree]
  split
  · rename_i firstBlock sourceFirst
    split
    · rename_i targetFirstBlock targetFirst
      rw [iter_eq_macroBody operationAt _ operations]
      apply Tree.refines_iter (CFGStateRefinesOn live Eq) (CFGReturnRefinesOn live)
        _ _ hbody
      refine ⟨⟨?_, hvalues⟩, hstate⟩
      grind
    · grind
  · exact Tree.refines_fail _ _

end Veir.DCE
