module

public import Veir.Passes.DCE.CFGMacroSimulation
public import Veir.Passes.DCE.CFGLive

import all Veir.Passes.DCE.CFGRefinement
import all Veir.Passes.DCE.StateRefinement
import all Veir.Passes.DCE.MacroSuffix
import all Veir.Interpreter.CTreeRefinement.Iteration

public section

namespace Veir.DCE

/-- Continue related surviving-operation actions while consuming the original
source's finite deleted suffix. This includes a deleted terminal suffix. -/
theorem ErasureTrace.continue_macroSuffix_refines
    {sourceCtx targetCtx : WfIRContext OpCode} {operations : List OperationPtr}
    (trace : ErasureTrace sourceCtx operations targetCtx) (operation : OperationPtr)
    (sourceIn : operation.InBounds sourceCtx.raw) (targetIn : operation.InBounds targetCtx.raw)
    (source : InterpreterState sourceCtx) (target : InterpreterState targetCtx)
    (sourceAction targetAction : Option ControlFlowAction)
    (hstate : StatesRefineOn (fun value => value.InBounds targetCtx.raw) source target)
    (haction : ControlFlowAction.optionIsRefinedBy sourceAction targetAction) :
    Tree.Refines
      (Sum.LiftRel
        (CFGStateRefinesOn (sourceCtx := sourceCtx) (targetCtx := targetCtx)
          (fun value => value.InBounds targetCtx.raw) Eq)
        (CFGReturnRefinesOn (sourceCtx := sourceCtx) (targetCtx := targetCtx)
          (fun value => value.InBounds targetCtx.raw)))
      (CTree.interpretCFGTreeContinue operation source sourceAction sourceIn >>=
        macroSuffix cfgOperationAt (fun (location, state) => CTree.interpretCFGTreeStep location state) operations)
      (CTree.interpretCFGTreeContinue operation target targetAction targetIn) := by
  cases sourceAction with
  | none =>
    cases targetAction with
    | some action => cases haction
    | none =>
      simp only [CTree.interpretCFGTreeContinue]
      split
      · rename_i nextSource hnextSource
        simp only [pure_bind]
        have hpath := trace.erasures.next_skips operation targetIn
        split
        · rename_i nextTarget hnextTarget
          apply trace.macroSuffix_operation_refines_pure nextSource nextTarget (by grind) (by grind)
            source target hstate
          have hs : operation.getNextOp! sourceCtx.raw = some nextSource := by grind
          have ht : operation.getNextOp! targetCtx.raw = some nextTarget := by grind
          simpa only [hs, ht] using hpath
        · rename_i hnextTarget
          apply trace.macroSuffix_operation_refines_fail nextSource (by grind) source target hstate
          have hs : operation.getNextOp! sourceCtx.raw = some nextSource := by grind
          have ht : operation.getNextOp! targetCtx.raw = none := by
            rw [OperationPtr.getNextOp!_eq_getNextOp targetIn]
            cases hchecked : operation.getNextOp targetCtx.raw with
            | none => rfl
            | some next => exact False.elim (hnextTarget next hchecked)
          simpa only [hs, ht] using hpath
      · simp only [Bind.bind, Tree.fail_bind]
        exact Tree.refines_fail _ _
  | some sourceAction =>
    cases targetAction with
    | none => cases haction
    | some targetAction =>
      cases sourceAction <;> cases targetAction <;>
        simp only [ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy] at haction
      · simp only [CTree.interpretCFGTreeContinue, pure_bind, macroSuffix_return]
        exact (Tree.refines_pure _ _ _).mpr (.inr ⟨hstate, haction⟩)
      · obtain ⟨hdest, hvalues⟩ := haction
        subst hdest
        simp only [CTree.interpretCFGTreeContinue]
        split
        · rename_i hsource
          simp only [dite_eq_left ((trace.erasures.block_inBounds_iff _).mpr hsource), pure_bind]
          rw [macroSuffix_eq_pure_of_not_deleted]
          · exact (Tree.refines_pure _ _ _).mpr (.inl ⟨⟨rfl, hvalues⟩, hstate⟩)
          · simp [outcomeOperationAt, cfgOperationAt]
        · simp only [Bind.bind, Tree.fail_bind]
          exact Tree.refines_fail _ _

end Veir.DCE

namespace Veir.DCE

/-- A surviving operation and its grouped deleted suffix directly refine the
corresponding target CFG step. No semantic transitivity is used. -/
theorem ErasureTrace.macroBody_operation_refines
    {sourceCtx targetCtx : WfIRContext OpCode} {operations : List OperationPtr}
    (trace : ErasureTrace sourceCtx operations targetCtx) (operation : OperationPtr)
    (sourceIn : operation.InBounds sourceCtx.raw) (targetIn : operation.InBounds targetCtx.raw)
    (source : InterpreterState sourceCtx) (target : InterpreterState targetCtx)
    (hstate : StatesRefineOn (fun value => value.InBounds targetCtx.raw) source target) :
    Tree.Refines
      (Sum.LiftRel
        (CFGStateRefinesOn (sourceCtx := sourceCtx) (targetCtx := targetCtx)
          (fun value => value.InBounds targetCtx.raw) Eq)
        (CFGReturnRefinesOn (sourceCtx := sourceCtx) (targetCtx := targetCtx)
          (fun value => value.InBounds targetCtx.raw)))
      (macroBody cfgOperationAt (fun (location, state) => CTree.interpretCFGTreeStep location state)
        operations (.inr ⟨operation, sourceIn⟩, source))
      (CTree.interpretCFGTreeStep (.inr ⟨operation, targetIn⟩) target) := by
  rw [macroBody_eq_bind_suffix]
  simp only [CTree.interpretCFGTreeStep, bind_assoc]
  apply Tree.refines_bind
    (interpretOperationTree_refinesOn_of_erasures trace.erasures operation source target sourceIn targetIn
      (fun value => value.InBounds targetCtx.raw) hstate
      (fun value live => trace.erasures.value_inBounds value live)
      (fun _ live => live) (trace.erasures.operands_live operation targetIn))
  rintro ⟨nextSource, sourceAction⟩ ⟨nextTarget, targetAction⟩ ⟨hstates, hactions⟩
  exact trace.continue_macroSuffix_refines operation sourceIn targetIn nextSource nextTarget
    sourceAction targetAction hstates hactions

end Veir.DCE
