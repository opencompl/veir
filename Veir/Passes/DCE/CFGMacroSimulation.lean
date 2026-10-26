module

public import Veir.Passes.DCE.CFGMacroNormalForm
public import Veir.Interpreter.CTreeRefinement.Finite

import all Veir.Passes.DCE.CFGRefinement
import all Veir.Passes.DCE.StateRefinement
import all Veir.Passes.DCE.MacroSuffix
import all Veir.Interpreter.CTreeRefinement.Iteration

public section

namespace Veir.DCE

/-- A finite deleted suffix reaches the corresponding surviving target operation,
with related memory and every final-live variable preserved. -/
theorem ErasureTrace.macroSuffix_operation_refines_pure
    {sourceCtx targetCtx : WfIRContext OpCode} {operations : List OperationPtr}
    (trace : ErasureTrace sourceCtx operations targetCtx)
    (operation targetOperation : OperationPtr)
    (sourceIn : operation.InBounds sourceCtx.raw) (targetIn : targetOperation.InBounds targetCtx.raw)
    (source : InterpreterState sourceCtx) (target : InterpreterState targetCtx)
    (hstate : StatesRefineOn (fun value => value.InBounds targetCtx.raw) source target)
    (hpath : Skips sourceCtx targetCtx (some operation) (some targetOperation)) :
    Tree.Refines
      (Sum.LiftRel (CFGStateRefinesOn (sourceCtx := sourceCtx) (targetCtx := targetCtx) (fun value => value.InBounds targetCtx.raw) Eq)
        (CFGReturnRefinesOn (sourceCtx := sourceCtx) (targetCtx := targetCtx) (fun value => value.InBounds targetCtx.raw)))
      (macroSuffix cfgOperationAt (fun (location, state) => CTree.interpretCFGTreeStep location state)
        operations (.inl (.inr ⟨operation, sourceIn⟩, source)))
      (pure (.inl (.inr ⟨targetOperation, targetIn⟩, target))) := by
  apply Tree.refines_pure_of_finite
  · exact macroSuffix_finite (cfgOperationAt (ctx := sourceCtx)) _
      (fun (location, state) => interpretCFGTreeStep_pureOrErr location state) operations _
  · intro result executes
    obtain ⟨endpoint, endpointIn, nextState, rfl, hequal, hstates⟩ :=
      macroSuffix_operation_success trace.erasures operations
        (fun op member => (trace.deleted_iff op (trace.original_inBounds op member)).mp member)
        operation sourceIn source target hstate (some targetOperation) hpath
        (by intro op equal; cases Option.some.inj equal; exact targetIn) result executes
        (by
          intro next endpoint equal identifies
          exact trace.macroSuffix_endpoint_survives _ next endpoint
            (by simpa only [equal] using executes) identifies)
    have : endpoint = targetOperation := Option.some.inj hequal
    subst endpoint
    exact .inl ⟨rfl, hstates⟩

/-- If the entire original suffix was deleted, no normalized source suffix can
succeed. It therefore refines the failed target next-operation lookup. -/
theorem ErasureTrace.macroSuffix_operation_refines_fail
    {sourceCtx targetCtx : WfIRContext OpCode} {operations : List OperationPtr}
    (trace : ErasureTrace sourceCtx operations targetCtx)
    (operation : OperationPtr) (sourceIn : operation.InBounds sourceCtx.raw)
    (source : InterpreterState sourceCtx) (target : InterpreterState targetCtx)
    (hstate : StatesRefineOn (fun value => value.InBounds targetCtx.raw) source target)
    (hpath : Skips sourceCtx targetCtx (some operation) none) :
    Tree.Refines
      (Sum.LiftRel (CFGStateRefinesOn (sourceCtx := sourceCtx) (targetCtx := targetCtx) (fun value => value.InBounds targetCtx.raw) Eq)
        (CFGReturnRefinesOn (sourceCtx := sourceCtx) (targetCtx := targetCtx) (fun value => value.InBounds targetCtx.raw)))
      (macroSuffix cfgOperationAt (fun (location, state) => CTree.interpretCFGTreeStep location state)
        operations (.inl (.inr ⟨operation, sourceIn⟩, source))) fail := by
  apply Tree.refines_of_finite
  · exact macroSuffix_finite (cfgOperationAt (ctx := sourceCtx)) _
      (fun (location, state) => interpretCFGTreeStep_pureOrErr location state) operations _
  · intro result executes
    obtain ⟨endpoint, endpointIn, nextState, _, hequal, _⟩ :=
      macroSuffix_operation_success trace.erasures operations
        (fun op member => (trace.deleted_iff op (trace.original_inBounds op member)).mp member)
        operation sourceIn source target hstate none hpath (by simp) result executes
        (by
          intro next endpoint equal identifies
          exact trace.macroSuffix_endpoint_survives _ next endpoint
            (by simpa only [equal] using executes) identifies)
    cases hequal

end Veir.DCE
