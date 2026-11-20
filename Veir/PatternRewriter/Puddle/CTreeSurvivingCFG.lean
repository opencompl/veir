module

public import Veir.PatternRewriter.Puddle.CTreeSurvivingStep
public import Veir.PatternRewriter.Puddle.CTreeSurvivingNext
public import Veir.PatternRewriter.Puddle.CTreeSurvivingBranch
import all Veir.Interpreter.CTreeStateRefinement
import all Veir.Interpreter.Refinement.Basic
import all Veir.PatternRewriter.Puddle.CTreeSurvivingStep
import all Veir.IR.Basic
import all Veir.IRNesting
import all Veir.Dominance.Basic
import all Veir.PatternRewriter.Puddle.CTreeModuleSoundness

public section
namespace Veir.Puddle.CTree

/-- The CFG dispatcher preserves simulation when the concrete successful core
outcomes preserve the instruction and branch-entry invariants. -/
theorem surviving_CFG_step
    {sourceCtx targetCtx : WfIRContext OpCode} {mapping : ValueMapping sourceCtx targetCtx}
    {root op : OperationPtr} {newOps : Array OperationPtr} {body : RegionPtr}
    (sourceIn : op.InBounds sourceCtx.raw) (targetIn : op.InBounds targetCtx.raw)
    (sourceState : InterpreterState sourceCtx) (targetState : InterpreterState targetCtx)
    (post : InterpreterState sourceCtx → InterpreterState targetCtx → Prop)
    (core : _root_.CTree.Sim
      (fun t s => post s.1 t.1 ∧ ControlFlowAction.optionIsRefinedBy s.2 t.2 ∧
        PureOrErr.CanInterpretTo (Veir.CTree.interpretOpCore op targetState targetIn) (.ok t) ∧
        PureOrErr.CanInterpretTo (Veir.CTree.interpretOpCore op sourceState sourceIn) (.ok s))
      (Veir.CTree.interpretOpCore op targetState targetIn)
      (Veir.CTree.interpretOpCore op sourceState sourceIn))
    (next : ∀ sourceFinal targetFinal sourceNext (sourceNextIn : sourceNext.InBounds sourceCtx.raw),
      op.getNextOp! sourceCtx.raw = some sourceNext → post sourceFinal targetFinal →
      ∃ (targetNext : OperationPtr) (targetNextIn : targetNext.InBounds targetCtx.raw),
        op.getNextOp! targetCtx.raw = some targetNext ∧
        RewriteOpInvariant mapping root newOps body body
          ⟨sourceNext, sourceNextIn⟩ ⟨targetNext, targetNextIn⟩ sourceFinal targetFinal)
    (branch : ∀ sourceFinal targetFinal (sourceArgs targetArgs : Array RuntimeValue) dest,
      post sourceFinal targetFinal → RuntimeValue.arrayIsRefinedBy sourceArgs targetArgs →
      PureOrErr.CanInterpretTo (Veir.CTree.interpretOpCore op sourceState sourceIn)
        (.ok (sourceFinal, some (.branch sourceArgs dest))) →
      PureOrErr.CanInterpretTo (Veir.CTree.interpretOpCore op targetState targetIn)
        (.ok (targetFinal, some (.branch targetArgs dest))) →
      ∃ (sourceDestIn : dest.InBounds sourceCtx.raw) (targetDestIn : dest.InBounds targetCtx.raw),
        RewriteCFGInvariant mapping root newOps body body
          (.inl (⟨dest, targetDestIn⟩, targetArgs), targetFinal)
          (.inl (⟨dest, sourceDestIn⟩, sourceArgs), sourceFinal)) :
    _root_.CTree.Sim
      (Sum.LiftRel (RewriteCFGInvariant mapping root newOps body body)
        (fun t s => RuntimeValue.arrayIsRefinedBy s.2 t.2))
      (Veir.CTree.interpretCFGCore.iter (.inr ⟨op, targetIn⟩) targetState)
      (Veir.CTree.interpretCFGCore.iter (.inr ⟨op, sourceIn⟩) sourceState) := by
  simp only [Veir.CTree.interpretCFGCore.iter]
  apply _root_.CTree.Sim.bind _ _ _ _ core
  rintro ⟨targetFinal, targetAction⟩ ⟨sourceFinal, sourceAction⟩ ⟨after, actions, targetOutcome, sourceOutcome⟩
  dsimp only
  cases sourceAction with
  | none =>
    cases targetAction with
    | some action => cases actions
    | none =>
      dsimp only
      cases sourceNext : op.getNextOp! sourceCtx.raw with
      | none =>
        have sourceNext' : op.getNextOp sourceCtx.raw sourceIn = none := by
          simpa only [OperationPtr.getNextOp!_eq_getNextOp sourceIn] using sourceNext
        repeat split
        all_goals simp_all
        all_goals exact sim_fail _ _
      | some sourceNextOp =>
        have sourceNextIn : sourceNextOp.InBounds sourceCtx.raw := by grind
        obtain ⟨targetNextOp, targetNextIn, targetNext, nextInvariant⟩ :=
          next sourceFinal targetFinal sourceNextOp sourceNextIn sourceNext after
        clear next
        have sourceNext' : op.getNextOp sourceCtx.raw sourceIn = some sourceNextOp := by
          simpa only [OperationPtr.getNextOp!_eq_getNextOp sourceIn] using sourceNext
        have targetNext' : op.getNextOp targetCtx.raw targetIn = some targetNextOp := by
          simpa only [OperationPtr.getNextOp!_eq_getNextOp targetIn] using targetNext
        repeat split
        all_goals simp_all
        all_goals exact RewriteCFGInvariant.operation nextInvariant
  | some sourceAction =>
    cases targetAction with
    | none => cases actions
    | some targetAction =>
      cases sourceAction <;> cases targetAction
      all_goals simp only [ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy] at actions
      all_goals try contradiction
      · exact (_root_.CTree.Sim.pure _ _ _).mpr (Sum.LiftRel.inr actions)
      · rcases actions with ⟨sameDestination, args⟩
        subst sameDestination
        obtain ⟨sourceDestIn, targetDestIn, nextInvariant⟩ :=
          branch _ _ _ _ _ after args sourceOutcome targetOutcome
        simp only [dite_eq_left sourceDestIn, dite_eq_left targetDestIn]
        exact (_root_.CTree.Sim.pure _ _ _).mpr (Sum.LiftRel.inl nextInvariant)

/-- Every surviving instruction of the actual compiled program preserves the global CFG relation. -/
theorem Pattern.Valid.surviving_CFG
    {rule : Veir.Puddle.Pattern OpCode} (valid : Pattern.Valid rule)
    {rewriter result : PatternRewriter OpCode} {root moduleOp : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (sourceVerified : rewriter.ctx.Verified moduleOp) (targetVerified : result.ctx.Verified moduleOp)
    (rootRooted : root.RootedAt moduleOp rewriter.ctx)
    (rootRegion : root.getParentRegion! rewriter.ctx.raw = some region)
    (rootSSA : region.hasSSADominance rewriter.ctx)
    (rootReachable : root.HierarchicallyReachable rewriter.ctx)
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (notOwn : ∀ value ∈ replacements, ∀ index < root.getNumResults! rewriter.ctx.raw,
      (root.getResult index : ValuePtr) ≠ value)
    {mapping : ValueMapping rewriter.ctx result.ctx}
    (canonical : mapping = rule.fromLocalRewrite_mapping localRun run attached regions notOwn)
    (mappingEq : ∀ value (valueIn : value.InBounds rewriter.ctx.raw),
      (mapping ⟨value, valueIn⟩).val = renameRootResults root replacements.zipIdx.toList value)
    (otherResults : ∀ op, op.InBounds rewriter.ctx.raw → op ≠ root →
      mapping.applyToArray (op.getResults! rewriter.ctx.raw) (by grind) = op.getResults! rewriter.ctx.raw)
    {body : RegionPtr} {function : OperationPtr}
    (functionCode : function.getOpType! rewriter.ctx.raw = .func .func)
    (sourceBodyParent : body.getParent! rewriter.ctx.raw = some function)
    (targetBodyParent : body.getParent! result.ctx.raw = some function)
    (targetFunction : FunctionOp result.ctx.raw function)
    (sourceBodyRooted : body.RootedAt moduleOp rewriter.ctx)
    (targetBodyRooted : body.RootedAt moduleOp result.ctx)
    (bodySSA : body.hasSSADominance rewriter.ctx)
    {op : OperationPtr} (sourceIn : op.InBounds rewriter.ctx.raw) (targetIn : op.InBounds result.ctx.raw)
    (different : op ≠ root)
    {sourceState : InterpreterState rewriter.ctx} {targetState : InterpreterState result.ctx}
    (invariant : RewriteOpInvariant mapping root newOps body body
      ⟨op, sourceIn⟩ ⟨op, targetIn⟩ sourceState targetState) :
    _root_.CTree.Sim
      (Sum.LiftRel (RewriteCFGInvariant mapping root newOps body body)
        (fun t s => RuntimeValue.arrayIsRefinedBy s.2 t.2))
      (Veir.CTree.interpretCFGCore.iter (.inr ⟨op, targetIn⟩) targetState)
      (Veir.CTree.interpretCFGCore.iter (.inr ⟨op, sourceIn⟩) sourceState) := by
  have sourceDom : rewriter.ctx.Dom moduleOp := sourceVerified.dominance
  have targetDom : result.ctx.Dom moduleOp := targetVerified.dominance
  obtain ⟨sourceBlock, sourceParent, sourceBlockParent⟩ :=
    OperationPtr.getParentRegion!_eq_some_iff.mp invariant.sourceParent
  obtain ⟨targetBlock, targetParent, targetBlockParent⟩ :=
    OperationPtr.getParentRegion!_eq_some_iff.mp invariant.targetParent
  have sourceRooted : op.RootedAt moduleOp rewriter.ctx :=
    ⟨sourceBodyRooted.1.trans (IRNode.Ancestor.of_getParentRegion!_eq_some invariant.sourceParent), sourceBodyRooted.2⟩
  have targetRooted : op.RootedAt moduleOp result.ctx :=
    ⟨targetBodyRooted.1.trans (IRNode.Ancestor.of_getParentRegion!_eq_some invariant.targetParent), targetBodyRooted.2⟩
  have frame := valid.surviving_frame sourceDom targetDom rootRooted rootRegion rootSSA rootReachable
    localRun run attached regions mappingEq otherResults sourceIn targetIn different sourceRooted targetRooted
    invariant.sourceReachable invariant.targetReachable sourceParent targetParent sourceBlockParent targetBlockParent
  have header := (valid.fromLocalRewrite_existing_frame sourceDom rootRooted rootRegion rootSSA rootReachable
    localRun run attached regions op sourceIn different).1
  have targetScope := targetFunction.owned_region_scope targetBodyParent
  have core := invariant.surviving_core sourceIn targetIn sourceVerified targetVerified targetRooted targetScope.1
    header sourceParent targetParent frame
  let post := RewritePointInvariant mapping root body
    (.after op rewriter.ctx.raw sourceBlock sourceParent sourceIn)
    (.after op result.ctx.raw targetBlock targetParent targetIn) (by grind) (by grind)
  apply surviving_CFG_step sourceIn targetIn sourceState targetState post
  · apply _root_.CTree.Sim.mono core
    intro target source related
    refine ⟨?_, related.1.2, related.2.1, related.2.2⟩
    exact valid.surviving_after sourceDom rootRooted rootRegion rootSSA rootReachable localRun run attached regions
      sourceIn targetIn different sourceRooted sourceParent targetParent sourceBlockParent targetBlockParent bodySSA
      frame.results.symm invariant related.1.1 related.2.2 related.2.1
  · intro sourceFinal targetFinal sourceNext sourceNextIn sourceNextEq after
    exact valid.surviving_next sourceDom sourceVerified rootRooted rootRegion rootSSA rootReachable localRun run
      attached regions functionCode sourceBodyParent sourceIn targetIn different sourceParent targetParent
      sourceBlockParent targetBlockParent invariant.sourceReachable invariant.targetReachable after sourceNextEq
  · intro sourceFinal targetFinal sourceArgs targetArgs dest after args sourceOutcome targetOutcome
    exact valid.surviving_branch sourceDom rootRooted rootRegion rootSSA bodySSA targetScope.2 rootReachable
      localRun run attached regions notOwn canonical sourceVerified targetVerified targetFunction targetBodyParent
      sourceIn targetIn sourceRooted targetRooted invariant.sourceReachable invariant.targetReachable
      sourceParent targetParent sourceBlockParent targetBlockParent after sourceOutcome targetOutcome args

end Veir.Puddle.CTree
