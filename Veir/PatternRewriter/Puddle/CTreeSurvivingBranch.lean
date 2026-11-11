module

public import Veir.PatternRewriter.Puddle.CTreeSurvivingStep
public import Veir.PatternRewriter.Puddle.CTreeBranchInvariant
public import Veir.PatternRewriter.Puddle.CTreeInitialInvariant
public import Veir.PatternRewriter.Puddle.DriverFunctionStructure
public import Veir.Interpreter.CTreeControlFlow
import all Veir.PatternRewriter.Puddle.CTreeSurvivingStep
import all Veir.PatternRewriter.Puddle.CTreeRewriteInvariant
import all Veir.PatternRewriter.Puddle.CTreeModuleSoundness
import all Veir.Interpreter.CTreeStateRefinement
import all Veir.Interpreter.Refinement.Basic
import all Veir.Interpreter.VariableState
import all Veir.Verifier
import all Veir.IR.Basic
import all Veir.IRNesting
import all Veir.Rewriter.InsertPoint

namespace Veir.Puddle.CTree
public section

/-- A verified operation with a successor edge ends its containing block. -/
theorem verified_next_none_of_successor {ctx : WfIRContext OpCode} {moduleOp op : OperationPtr}
    (verified : ctx.Verified moduleOp) (opIn : op.InBounds ctx.raw)
    {block dest : BlockPtr} (parent : op.getParent! ctx.raw = some block)
    (edge : dest ∈ op.getSuccessors! ctx.raw) : op.getNextOp! ctx.raw = none := by
  simp only [WfIRContext.Verified, WfIRContext.verify] at verified
  split at verified
  · cases verified
  split at verified
  · cases verified
  obtain ⟨_, ops, _⟩ := Except.bind_eq_ok.mp verified
  have checked := IRContext.forOpsDepM_except_ok ops op opIn
  have checked := Except.eq_ok_of_mapError_eq_ok checked
  obtain ⟨_, _, checked⟩ := Except.bind_eq_ok.mp checked
  have parentEq : op.getParent ctx.raw opIn = some block := by grind
  simp only [parentEq] at checked
  obtain ⟨_, position, _⟩ := Except.bind_eq_ok.mp checked
  simp only [OperationPtr.verifyTerminatorPosition] at position
  split at position
  · cases position
  · split at position
    · cases position
    · rename_i h
      have count : op.getNumSuccessors ctx.raw opIn ≠ 0 := by
        obtain ⟨index, bound, _⟩ := Array.getElem_of_mem edge
        have size := OperationPtr.getSuccessors!.size_eq_getNumSuccessors! (op := op) (ctx := ctx.raw)
        have same := OperationPtr.getNumSuccessors!_eq_getNumSuccessors opIn
        omega
      have nextNone : op.getNextOp ctx.raw opIn = none := by
        cases next : op.getNextOp ctx.raw opIn with
        | none => rfl
        | some nextOp => simp [next, count] at h
      simpa only [OperationPtr.getNextOp!_eq_getNextOp opIn] using nextNone

/-- A successful checked branch action targets an actual successor edge. -/
theorem interpretOpCore_branch_mem {ctx : WfIRContext OpCode} {op : OperationPtr}
    (opIn : op.InBounds ctx.raw) {state final : InterpreterState ctx} {args : Array RuntimeValue} {dest : BlockPtr}
    (outcome : PureOrErr.CanInterpretTo (Veir.CTree.interpretOpCore op state opIn)
      (.ok (final, some (.branch args dest)))) : dest ∈ op.getSuccessors! ctx.raw := by
  obtain ⟨operands, raw, _, rawOutcome, _, _, action⟩ :=
    interpretOpCore_outcome op opIn state (final, some (.branch args dest)) outcome
  rw [interpretCTree_eq_bang op opIn] at rawOutcome
  obtain (⟨deterministic, legacy⟩ | noAction) := Veir.CTree.interpretOp'_controlFlow
    (op.getOpType! ctx.raw) (op.getProperties! ctx.raw (op.getOpType! ctx.raw))
    (op.getResultTypes! ctx.raw) operands (op.getSuccessors! ctx.raw) state.memory raw.2.1 raw.1 raw.2.2 #[] rawOutcome
  · have actionEq : raw.2.2 = some (.branch args dest) := by simpa using action.symm
    rw [actionEq] at legacy
    exact Veir.interpretOp'_branch_dest_mem legacy
  · simp [noAction] at action



private theorem successor_reachable {ctx : WfIRContext OpCode} {block dest : BlockPtr}
    (reachable : block.HierarchicallyReachable ctx)
    (parent : block.getParent! ctx.raw = some region)
    (destParent : dest.getParent! ctx.raw = some region)
    (edge : dest ∈ block.getSuccessors! ctx.raw) : dest.HierarchicallyReachable ctx := by
  have localReach := reachable.locallyReachable parent |>.successor edge destParent
  intro ancestor ancestry localRegion ancestorParent
  by_cases same : ancestor = dest
  · subst ancestor
    have equal : localRegion = region := by grind
    subst localRegion
    exact localReach
  · have proper := ancestry.toProperAncestor (by simpa using same)
    have sourceAncestry := IRNode.Ancestor.of_same_parent_of_properAncestor proper
      (show (IRNode.block dest).parent! ctx = some (.region region) by grind)
      (show (IRNode.block block).parent! ctx = some (.region region) by grind)
    exact reachable ancestor sourceAncestry localRegion ancestorParent

/-- Successful related branch outcomes of a surviving operation establish the actual driver's
pending successor-block invariant. All static entry, argument mapping, and alias obligations are
discharged from the valid concrete rewrite and verified function metadata. -/
theorem Pattern.Valid.surviving_branch
    {rule : Veir.Puddle.Pattern OpCode} (valid : Pattern.Valid rule)
    {rewriter result : PatternRewriter OpCode} {root moduleOp : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (sourceDom : rewriter.ctx.Dom moduleOp)
    (rootRooted : root.RootedAt moduleOp rewriter.ctx)
    (rootRegion : root.getParentRegion! rewriter.ctx.raw = some region)
    (rootSSA : region.hasSSADominance rewriter.ctx)
    (sourceSSA : body.hasSSADominance rewriter.ctx) (targetSSA : body.hasSSADominance result.ctx)
    (rootReachable : root.HierarchicallyReachable rewriter.ctx)
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (notOwn : ∀ value ∈ replacements, ∀ index < root.getNumResults! rewriter.ctx.raw,
      (root.getResult index : ValuePtr) ≠ value)
    {mapping : ValueMapping rewriter.ctx result.ctx}
    (canonical : mapping = rule.fromLocalRewrite_mapping localRun run attached regions notOwn)
    (sourceVerified : rewriter.ctx.Verified moduleOp) (targetVerified : result.ctx.Verified moduleOp)
    {function : OperationPtr} (targetFunction : FunctionOp result.ctx.raw function)
    (bodyOwner : body.getParent! result.ctx.raw = some function)
    {op : OperationPtr} (sourceIn : op.InBounds rewriter.ctx.raw) (targetIn : op.InBounds result.ctx.raw)
    (sourceRooted : op.RootedAt moduleOp rewriter.ctx) (_targetRooted : op.RootedAt moduleOp result.ctx)
    (sourceReachable : op.HierarchicallyReachable rewriter.ctx)
    (targetReachable : op.HierarchicallyReachable result.ctx)
    {sourceBlock targetBlock : BlockPtr}
    (sourceParent : op.getParent! rewriter.ctx.raw = some sourceBlock)
    (targetParent : op.getParent! result.ctx.raw = some targetBlock)
    (sourceBlockParent : sourceBlock.getParent! rewriter.ctx.raw = some body)
    (targetBlockParent : targetBlock.getParent! result.ctx.raw = some body)
    {sourceState sourceFinal : InterpreterState rewriter.ctx}
    {targetState targetFinal : InterpreterState result.ctx} {sourceArgs targetArgs : Array RuntimeValue} {dest : BlockPtr}
    (point : RewritePointInvariant mapping root body
      (.after op rewriter.ctx.raw sourceBlock sourceParent sourceIn)
      (.after op result.ctx.raw targetBlock targetParent targetIn) (by grind) (by grind) sourceFinal targetFinal)
    (sourceOutcome : PureOrErr.CanInterpretTo
      (Veir.CTree.interpretOpCore op sourceState sourceIn) (.ok (sourceFinal, some (.branch sourceArgs dest))))
    (targetOutcome : PureOrErr.CanInterpretTo
      (Veir.CTree.interpretOpCore op targetState targetIn) (.ok (targetFinal, some (.branch targetArgs dest))))
    (args : sourceArgs ⊒ targetArgs) :
    ∃ sourceDestIn : dest.InBounds rewriter.ctx.raw, ∃ targetDestIn : dest.InBounds result.ctx.raw,
      RewriteCFGInvariant mapping root newOps body body
        (.inl (⟨dest, targetDestIn⟩, targetArgs), targetFinal)
        (.inl (⟨dest, sourceDestIn⟩, sourceArgs), sourceFinal) := by
  have sourceOpEdge := interpretOpCore_branch_mem sourceIn sourceOutcome
  have targetOpEdge := interpretOpCore_branch_mem targetIn targetOutcome
  have sourceNone := verified_next_none_of_successor sourceVerified sourceIn sourceParent sourceOpEdge
  have targetNone := verified_next_none_of_successor targetVerified targetIn targetParent targetOpEdge
  have sourceBlockIn : sourceBlock.InBounds rewriter.ctx.raw := by grind
  have targetBlockIn : targetBlock.InBounds result.ctx.raw := by grind
  have sourceLast : sourceBlock.getLastOp! rewriter.ctx.raw = some op := by grind
  have targetLast : targetBlock.getLastOp! result.ctx.raw = some op := by grind
  have sourceEdge : dest ∈ sourceBlock.getSuccessors! rewriter.ctx.raw := by
    simpa [BlockPtr.getSuccessors!, sourceLast] using sourceOpEdge
  have targetEdge : dest ∈ targetBlock.getSuccessors! result.ctx.raw := by
    simpa [BlockPtr.getSuccessors!, targetLast] using targetOpEdge
  have sourceDestParent := sourceVerified.successor_parent sourceBlockIn sourceBlockParent sourceEdge
  have targetDestParent := targetVerified.successor_parent targetBlockIn targetBlockParent targetEdge
  have sourceDestIn : dest.InBounds rewriter.ctx.raw := by grind [BlockPtr.getParent!_of_not_inBounds]
  have targetDestIn : dest.InBounds result.ctx.raw := by grind [BlockPtr.getParent!_of_not_inBounds]
  have sourceBlockRooted : sourceBlock.RootedAt moduleOp rewriter.ctx :=
    sourceRooted.of_ancestor (.of_parent (by grind))
  have sourceDestRooted : dest.RootedAt moduleOp rewriter.ctx :=
    sourceBlockRooted.of_same_parent (parent := .region body)
      (by simp [IRNode.parent!, sourceBlockParent]) (by simp [IRNode.parent!, sourceDestParent])
  have sourceDestReachable := successor_reachable (sourceReachable.parent_block sourceParent)
    sourceBlockParent sourceDestParent sourceEdge
  have targetDestReachable := successor_reachable (targetReachable.parent_block targetParent)
    targetBlockParent targetDestParent targetEdge
  have sourceAfter : InsertPoint.after op rewriter.ctx.raw sourceBlock sourceParent sourceIn = .atEnd sourceBlock :=
    InsertPoint.after_eq_atEnd_iff.mpr sourceNone
  have targetAfter : InsertPoint.after op result.ctx.raw targetBlock targetParent targetIn = .atEnd targetBlock :=
    InsertPoint.after_eq_atEnd_iff.mpr targetNone
  have atEnd : RewritePointInvariant mapping root body (.atEnd sourceBlock) (.atEnd targetBlock)
      (by grind) (by grind) sourceFinal targetFinal := by simpa only [sourceAfter, targetAfter] using point
  have headers := rule.fromLocalRewrite_regionBlockHeaders localRun run attached regions notOwn
  have nonempty := verified_function_entry_nonempty targetVerified targetFunction targetDestIn targetDestParent bodyOwner
  refine ⟨sourceDestIn, targetDestIn, ?_⟩
  apply branch_pending_invariant sourceBlockIn targetBlockIn sourceDestIn targetDestIn
    sourceBlockParent targetBlockParent sourceDestParent targetDestParent sourceSSA targetSSA
    sourceEdge targetEdge sourceDestRooted sourceDestReachable targetDestReachable sourceDom
    (headers.argumentTypes dest) ?_ ?_ ?_ atEnd.states atEnd.sourceDefined atEnd.targetDefined
    atEnd.matcherValues atEnd.matcherDefined atEnd.matcherHistory args
  · rw [canonical, rule.fromLocalRewrite_mapping_arguments localRun run attached regions notOwn sourceDestIn]
    exact headers.arguments dest
  · exact Pattern.fromLocalRewrite_branch_firstFrame rule localRun run attached regions notOwn
      sourceDestIn targetDestIn nonempty
  · intro value valueIn sourceLive _ notArgument
    rw [canonical]
    exact valid.fromLocalRewrite_mapping_noAlias_arguments sourceDom rootRooted rootRegion rootSSA
      rootReachable localRun run attached regions notOwn sourceDestIn sourceDestRooted
      (sourceDestReachable.locallyReachable sourceDestParent) sourceSSA (headers.arguments dest) valueIn sourceLive notArgument

end
end Veir.Puddle.CTree
