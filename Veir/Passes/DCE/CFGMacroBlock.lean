module

public import Veir.Passes.DCE.CFGMacroSimulation

import all Veir.Passes.DCE.CFGRefinement
import all Veir.Passes.DCE.StateRefinement

public section

open CTree

namespace Veir.DCE

/-- Related block-entry arguments reach the same surviving operation after
normalizing the finite deleted prefix of the original block. -/
theorem ErasureTrace.macroBody_block_refines
    {sourceCtx targetCtx : WfIRContext OpCode} {operations : List OperationPtr}
    (trace : ErasureTrace sourceCtx operations targetCtx) (block : BlockPtr)
    (sourceIn : block.InBounds sourceCtx.raw) (targetIn : block.InBounds targetCtx.raw)
    (sourceValues targetValues : Array RuntimeValue)
    (source : InterpreterState sourceCtx) (target : InterpreterState targetCtx)
    (hvalues : RuntimeValue.arrayIsRefinedBy sourceValues targetValues)
    (hstate : StatesRefineOn (fun value => value.InBounds targetCtx.raw) source target) :
    Tree.Refines
      (Sum.LiftRel
        (CFGStateRefinesOn (sourceCtx := sourceCtx) (targetCtx := targetCtx)
          (fun value => value.InBounds targetCtx.raw) Eq)
        (CFGReturnRefinesOn (sourceCtx := sourceCtx) (targetCtx := targetCtx)
          (fun value => value.InBounds targetCtx.raw)))
      (macroBody cfgOperationAt
        (fun (location, state) => CTree.interpretCFGTreeStep location state) operations
        (.inl (⟨block, sourceIn⟩, sourceValues), source))
      (CTree.interpretCFGTreeStep (.inl (⟨block, targetIn⟩, targetValues)) target) := by
  rw [macroBody_eq_bind_suffix]
  simp only [CTree.interpretCFGTreeStep]
  split
  · simp only [Bind.bind, Tree.fail_bind]
    exact Tree.refines_fail _ _
  · rename_i correctSize
    have hsize : sourceValues.size = block.getNumArguments! sourceCtx.raw := by simpa using correctSize
    have hcount := trace.erasures.block_numArguments block
    have htargetSize : targetValues.size = block.getNumArguments! targetCtx.raw := by
      have := hvalues.1
      omega
    simp only [htargetSize, bne_self_eq_false, Bool.false_eq_true, ite_false]
    cases hset : source.variables.setArgumentValues? block sourceValues sourceIn with
    | none =>
      simp only [Bind.bind, Tree.fail_bind]
      exact Tree.refines_fail _ _
    | some nextVariables =>
      have htypes : ∀ index, index < block.getNumArguments! sourceCtx.raw →
          (block.getArgument index : ValuePtr).getType! targetCtx.raw =
            (block.getArgument index : ValuePtr).getType! sourceCtx.raw := by
        intro index indexIn
        have targetValueIn : (block.getArgument index : ValuePtr).InBounds targetCtx.raw := by grind
        exact trace.erasures.value_getType _ targetValueIn
      obtain ⟨targetVariables, htargetSet, hvariables⟩ :=
        setBlockArguments_refineOn (targetIn := targetIn) hstate.2 hcount htypes hsize hvalues hset
      simp only [htargetSet]
      split
      · rename_i first sourceFirst
        split
        · rename_i targetFirst targetFirstEq
          simp only [Bind.bind, Tree.bind_pure_left]
          apply trace.macroSuffix_operation_refines_pure first targetFirst
            (by grind) (by grind)
            (⟨nextVariables, source.memory⟩ : InterpreterState sourceCtx)
            (⟨targetVariables, target.memory⟩ : InterpreterState targetCtx) ⟨hstate.1, hvariables⟩
          have sourceFirstBang : block.getFirstOp! sourceCtx.raw = some first := by grind
          have targetFirstBang : block.getFirstOp! targetCtx.raw = some targetFirst := by grind
          simpa only [sourceFirstBang, targetFirstBang] using trace.erasures.firstOp_skips block sourceIn
        · rename_i targetMissing
          simp only [Bind.bind, Tree.bind_pure_left]
          apply trace.macroSuffix_operation_refines_fail first (by grind)
            (⟨nextVariables, source.memory⟩ : InterpreterState sourceCtx)
            (⟨targetVariables, target.memory⟩ : InterpreterState targetCtx) ⟨hstate.1, hvariables⟩
          have sourceFirstBang : block.getFirstOp! sourceCtx.raw = some first := by grind
          have targetFirstBang : block.getFirstOp! targetCtx.raw = none := by
            rw [BlockPtr.getFirstOp!_eq_getFirstOp targetIn]
            cases hfirst : block.getFirstOp targetCtx.raw targetIn with
            | none => rfl
            | some operation => exact False.elim (targetMissing operation hfirst)
          simpa only [sourceFirstBang, targetFirstBang] using trace.erasures.firstOp_skips block sourceIn
      · simp only [Bind.bind, Tree.fail_bind]
        exact Tree.refines_fail _ _

end Veir.DCE
