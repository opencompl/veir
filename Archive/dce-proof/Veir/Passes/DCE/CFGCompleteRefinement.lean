module

public import Veir.Passes.DCE.CFGMacroBlock
public import Veir.Passes.DCE.CFGMacroOperation
public import Veir.Passes.DCE.LoopRefinement

import all Veir.Passes.DCE.CFGRefinement

public section

namespace Veir.DCE

/-- A direct original-to-final macrostep simulation: the source executes all
removed finite operations before matching the next surviving target location. -/
theorem ErasureTrace.macroBody_refines
    {sourceCtx targetCtx : WfIRContext OpCode} {operations : List OperationPtr}
    (trace : ErasureTrace sourceCtx operations targetCtx)
    (source : CTree.interpretCFG.StateLocation sourceCtx × InterpreterState sourceCtx)
    (target : CTree.interpretCFG.StateLocation targetCtx × InterpreterState targetCtx)
    (related : CFGStateRefinesOn (fun value => value.InBounds targetCtx.raw) Eq source target) :
    Tree.Refines
      (Sum.LiftRel
        (CFGStateRefinesOn (sourceCtx := sourceCtx) (targetCtx := targetCtx)
          (fun value => value.InBounds targetCtx.raw) Eq)
        (CFGReturnRefinesOn (sourceCtx := sourceCtx) (targetCtx := targetCtx)
          (fun value => value.InBounds targetCtx.raw)))
      (macroBody cfgOperationAt
        (fun (location, state) => CTree.interpretCFGTreeStep location state) operations source)
      (CTree.interpretCFGTreeStep target.1 target.2) := by
  rcases source with ⟨sourceLocation, sourceState⟩
  rcases target with ⟨targetLocation, targetState⟩
  rcases related with ⟨hlocation, hstate⟩
  cases sourceLocation with
  | inl sourceEntry =>
    cases targetLocation with
    | inr targetOperation => cases hlocation
    | inl targetEntry =>
      rcases sourceEntry with ⟨⟨sourceBlock, sourceIn⟩, sourceValues⟩
      rcases targetEntry with ⟨⟨targetBlock, targetIn⟩, targetValues⟩
      rcases hlocation with ⟨sameBlock, hvalues⟩
      subst targetBlock
      exact trace.macroBody_block_refines sourceBlock sourceIn targetIn
        sourceValues targetValues sourceState targetState hvalues hstate
  | inr sourceOperation =>
    cases targetLocation with
    | inl targetEntry => cases hlocation
    | inr targetOperation =>
      rcases sourceOperation with ⟨sourceOp, sourceIn⟩
      rcases targetOperation with ⟨targetOp, targetIn⟩
      change sourceOp = targetOp at hlocation
      subst targetOp
      exact trace.macroBody_operation_refines sourceOp sourceIn targetIn sourceState targetState hstate

/-- Every syntactic DCE deletion sequence refines a region's entire CTree CFG,
including possibly infinite control flow and related runtime inputs. -/
theorem Erasures.interpretCFGTree_refines
    {sourceCtx targetCtx : WfIRContext OpCode}
    (erases : Erasures sourceCtx targetCtx) (region : RegionPtr)
    (sourceIn : region.InBounds sourceCtx.raw) (targetIn : region.InBounds targetCtx.raw)
    (sourceValues targetValues : Array RuntimeValue)
    (source : InterpreterState sourceCtx) (target : InterpreterState targetCtx)
    (hvalues : RuntimeValue.arrayIsRefinedBy sourceValues targetValues)
    (hstate : StatesRefineOn (fun value => value.InBounds targetCtx.raw) source target) :
    Tree.Refines (CFGReturnRefinesOn (fun value => value.InBounds targetCtx.raw))
      (CTree.interpretCFGTree region sourceValues source sourceIn)
      (CTree.interpretCFGTree region targetValues target targetIn) := by
  obtain ⟨operations, trace⟩ := erases.exists_trace
  exact trace.interpretCFGTree_refines_of_macroBody cfgOperationAt
    (fun value => value.InBounds targetCtx.raw) trace.macroBody_refines
    region sourceValues targetValues source target sourceIn targetIn hvalues hstate

end Veir.DCE
