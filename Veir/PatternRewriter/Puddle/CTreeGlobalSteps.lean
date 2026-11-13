module

public import Veir.PatternRewriter.Puddle.CTreeRewriteInvariant
import all Veir.Interpreter.CTreeStateRefinement
import all Veir.Interpreter.VariableState

public section

namespace Veir.Puddle.CTree

private theorem core_block_eq_of_set {ctx : WfIRContext OpCode}
    (block : {b : BlockPtr // b.InBounds ctx.raw}) (args : Array RuntimeValue)
    (state : InterpreterState ctx) {variables : VariableState ctx}
    (set : state.variables.setArgumentValues? block args block.property = some variables)
    {first : OperationPtr} (firstIn : first.InBounds ctx.raw)
    (firstGet : block.val.getFirstOp! ctx.raw = some first) :
    Veir.CTree.interpretCFGCore.iter (.inl (block, args)) state =
      pure (.inl (.inr ⟨first, firstIn⟩, ⟨variables, state.memory⟩)) := by
  have size : args.size = block.val.getNumArguments! ctx.raw := by
    unfold VariableState.setArgumentValues? at set
    split at set <;> simp_all
  have size' : args.size = block.val.getNumArguments ctx.raw block.property := by
    simpa only [BlockPtr.getNumArguments!_eq_getNumArguments block.property] using size
  have firstGet' : block.val.getFirstOp ctx.raw block.property = some first := by
    simpa only [BlockPtr.getFirstOp!_eq_getFirstOp block.property] using firstGet
  simp only [Veir.CTree.interpretCFGCore.iter, size', bne_self_eq_false, Bool.false_eq_true,
    ↓reduceIte, set]
  split <;> simp_all

/-- The actual CFG block-entry step consumes the pending argument-installation invariant. -/
theorem rewriteCFGInvariant_block_step
    {sourceCtx targetCtx : WfIRContext OpCode} {mapping : ValueMapping sourceCtx targetCtx}
    {root : OperationPtr} {newOps : Array OperationPtr} {sourceRegion targetRegion : RegionPtr}
    {sourceBlock : {b : BlockPtr // b.InBounds sourceCtx.raw}}
    {targetBlock : {b : BlockPtr // b.InBounds targetCtx.raw}}
    {sourceArgs targetArgs : Array RuntimeValue}
    {sourceState : InterpreterState sourceCtx} {targetState : InterpreterState targetCtx}
    (pending : ∀ sourceVariables,
      sourceState.variables.setArgumentValues? sourceBlock sourceArgs sourceBlock.property = some sourceVariables →
      ∀ sourceFirst (sourceFirstIn : sourceFirst.InBounds sourceCtx.raw),
      sourceBlock.val.getFirstOp! sourceCtx.raw = some sourceFirst →
      ∃ (targetVariables : VariableState targetCtx) (targetFirst : OperationPtr)
        (targetFirstIn : targetFirst.InBounds targetCtx.raw),
        targetState.variables.setArgumentValues? targetBlock targetArgs targetBlock.property = some targetVariables ∧
        targetBlock.val.getFirstOp! targetCtx.raw = some targetFirst ∧
        RewriteOpInvariant mapping root newOps sourceRegion targetRegion
          ⟨sourceFirst, sourceFirstIn⟩ ⟨targetFirst, targetFirstIn⟩
          ⟨sourceVariables, sourceState.memory⟩ ⟨targetVariables, targetState.memory⟩)
    (returnRelation : (InterpreterState targetCtx × Array RuntimeValue) →
      (InterpreterState sourceCtx × Array RuntimeValue) → Prop) :
    _root_.CTree.Sim
      (Sum.LiftRel (RewriteCFGInvariant mapping root newOps sourceRegion targetRegion) returnRelation)
      (Veir.CTree.interpretCFGCore.iter (.inl (targetBlock, targetArgs)) targetState)
      (Veir.CTree.interpretCFGCore.iter (.inl (sourceBlock, sourceArgs)) sourceState) := by
  cases sourceSet : sourceState.variables.setArgumentValues? sourceBlock sourceArgs sourceBlock.property with
  | none =>
    have failed : Veir.CTree.interpretCFGCore.iter (.inl (sourceBlock, sourceArgs)) sourceState = fail := by
      simp only [Veir.CTree.interpretCFGCore.iter, sourceSet]
      split <;> simp
    rw [failed]
    exact sim_fail _ _
  | some sourceVariables =>
    cases firstGet : sourceBlock.val.getFirstOp! sourceCtx.raw with
    | none =>
      have firstGet' : sourceBlock.val.getFirstOp sourceCtx.raw sourceBlock.property = none := by
        simpa only [BlockPtr.getFirstOp!_eq_getFirstOp sourceBlock.property] using firstGet
      have failed : Veir.CTree.interpretCFGCore.iter (.inl (sourceBlock, sourceArgs)) sourceState = fail := by
        simp only [Veir.CTree.interpretCFGCore.iter, sourceSet]
        repeat split
        all_goals simp_all
      rw [failed]
      exact sim_fail _ _
    | some sourceFirst =>
      have sourceFirstIn : sourceFirst.InBounds sourceCtx.raw := by grind
      obtain ⟨targetVariables, targetFirst, targetFirstIn, targetSet, targetFirstGet, invariant⟩ :=
        pending sourceVariables sourceSet sourceFirst sourceFirstIn firstGet
      rw [core_block_eq_of_set sourceBlock sourceArgs sourceState sourceSet sourceFirstIn firstGet,
        core_block_eq_of_set targetBlock targetArgs targetState targetSet targetFirstIn targetFirstGet]
      apply (_root_.CTree.Sim.pure _ _ _).mpr
      exact Sum.LiftRel.inl (RewriteCFGInvariant.operation invariant)

end Veir.Puddle.CTree
