module

public import Veir.PatternRewriter.Puddle.CTreeRewriteInvariant
public import Veir.PatternRewriter.Puddle.CTreeBlockScope
public import Veir.PatternRewriter.Puddle.MatcherValueRefinement
public import Veir.Interpreter.CTreeEntryInvariant
import all Veir.PatternRewriter.Puddle.CTreeRewriteInvariant
import all Veir.PatternRewriter.Puddle.MatcherResolverHistory
import all Veir.PatternRewriter.Puddle.MatcherValueRefinement
import all Veir.PatternRewriter.Puddle.CTreeModuleSoundness
import all Veir.Interpreter.Refinement.Basic
import all Veir.Interpreter.VariableState
import all Veir.Rewriter.InsertPoint
import all Veir.IR.Basic

namespace Veir.Puddle.CTree
public section

/-- The actual driver supplies the operation-entry redirection used at every nonempty successor. -/
theorem Pattern.fromLocalRewrite_branch_firstFrame (rule : Veir.Puddle.Pattern OpCode)
    {rewriter result : PatternRewriter OpCode} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (notOwn : ∀ value ∈ replacements, ∀ index < root.getNumResults! rewriter.ctx.raw,
      (root.getResult index : ValuePtr) ≠ value)
    {block : BlockPtr} (blockIn : block.InBounds rewriter.ctx.raw)
    (_targetBlockIn : block.InBounds result.ctx.raw)
    (nonempty : ∃ op, block.getFirstOp! result.ctx.raw = some op) :
    ∀ sourceFirst, sourceFirst.InBounds rewriter.ctx.raw →
      block.getFirstOp! rewriter.ctx.raw = some sourceFirst →
      ∃ targetFirst, targetFirst.InBounds result.ctx.raw ∧
        block.getFirstOp! result.ctx.raw = some targetFirst ∧
        redirectedOperation rewriter.ctx.raw root newOps sourceFirst = some targetFirst := by
  intro first _ firstGet
  obtain ⟨targetFirst, targetFirstGet⟩ := nonempty
  refine ⟨targetFirst, by grind, targetFirstGet, ?_⟩
  by_cases same : first = root
  · subst first
    have entryEq := rule.fromLocalRewrite_block_entry localRun run attached regions notOwn _ blockIn firstGet
    have redir : redirectedOperation rewriter.ctx.raw root newOps root = block.getFirstOp! result.ctx.raw := by
      rw [entryEq]
      unfold redirectedOperation
      simp only [↓reduceIte]
      rw [← Array.getElem?_toList]
      cases newOps.toList <;> rfl
    exact redir.trans targetFirstGet
  · have unchanged := rule.fromLocalRewrite_other_block_entry localRun run attached regions notOwn
      block blockIn (by grind)
    have equal : targetFirst = first := by grind
    simp [redirectedOperation, same, equal]

/-- A related branch outcome establishes the pending block-entry invariant. The premises about
first operations, argument identities, and scope aliasing are structural facts of the actual splice;
all checked argument installation and runtime invariant preservation are derived here. -/
theorem branch_pending_invariant
    {sourceCtx targetCtx : WfIRContext OpCode} {mapping : ValueMapping sourceCtx targetCtx}
    {rewriteRoot : OperationPtr} {newOps : Array OperationPtr} {sourceRegion targetRegion : RegionPtr}
    {sourceBlock targetBlock succ : BlockPtr} {sourceState : InterpreterState sourceCtx}
    {targetState : InterpreterState targetCtx} {sourceArgs targetArgs : Array RuntimeValue}
    (sourceBlockIn : sourceBlock.InBounds sourceCtx.raw) (targetBlockIn : targetBlock.InBounds targetCtx.raw)
    (sourceSuccIn : succ.InBounds sourceCtx.raw) (targetSuccIn : succ.InBounds targetCtx.raw)
    (sourceParent : sourceBlock.getParent! sourceCtx.raw = some sourceRegion)
    (targetParent : targetBlock.getParent! targetCtx.raw = some targetRegion)
    (sourceSuccParent : succ.getParent! sourceCtx.raw = some sourceRegion)
    (targetSuccParent : succ.getParent! targetCtx.raw = some targetRegion)
    (sourceSSA : sourceRegion.hasSSADominance sourceCtx) (targetSSA : targetRegion.hasSSADominance targetCtx)
    (sourceEdge : succ ∈ sourceBlock.getSuccessors! sourceCtx.raw)
    (targetEdge : succ ∈ targetBlock.getSuccessors! targetCtx.raw)
    (sourceSuccRooted : succ.RootedAt sourceIRRoot sourceCtx)
    (sourceSuccReachable : succ.HierarchicallyReachable sourceCtx)
    (targetSuccReachable : succ.HierarchicallyReachable targetCtx)
    (sourceDom : sourceCtx.Dom sourceIRRoot)
    (types : succ.getArgumentTypes! targetCtx.raw = succ.getArgumentTypes! sourceCtx.raw)
    (argumentPointers : succ.getArguments! targetCtx.raw =
      mapping.applyToArray (succ.getArguments! sourceCtx.raw))
    (firstFrame : ∀ sourceFirst, sourceFirst.InBounds sourceCtx.raw →
      succ.getFirstOp! sourceCtx.raw = some sourceFirst →
      ∃ targetFirst, targetFirst.InBounds targetCtx.raw ∧
        succ.getFirstOp! targetCtx.raw = some targetFirst ∧
        redirectedOperation sourceCtx.raw rewriteRoot newOps sourceFirst = some targetFirst)
    (noAlias : ∀ (value : ValuePtr) (valueIn : value.InBounds sourceCtx.raw),
      value.DominatesIp (InsertPoint.atStart! succ sourceCtx.raw) sourceCtx →
      (mapping ⟨value, valueIn⟩).val.DominatesIp (InsertPoint.atStart! succ targetCtx.raw) targetCtx →
      value ∉ succ.getArguments! sourceCtx.raw →
      (mapping ⟨value, valueIn⟩).val ∉ succ.getArguments! targetCtx.raw)
    (states : ScopedStateRefines mapping (.at (.atEnd sourceBlock)) (.at (.atEnd targetBlock))
      (by grind) (by grind) sourceState targetState)
    (sourceDefined : sourceState.DefinesDominatingIn sourceRegion (.atEnd sourceBlock))
    (targetDefined : targetState.DefinesDominatingIn targetRegion (.atEnd targetBlock))
    (matcherValues : ValueResolver.WatchedRefines sourceState.variables.getVar? targetState.variables.getVar?
      sourceCtx sourceRegion rewriteRoot (.atEnd sourceBlock))
    (matcherDefined : ValueResolver.DefinesDominatingIn targetState.variables.getVar?
      sourceCtx sourceRegion rewriteRoot (.atEnd sourceBlock))
    (matcherHistory : ValueResolver.CTreeEquationLemmaIn targetState.variables.getVar?
      sourceCtx sourceRegion rewriteRoot (.atEnd sourceBlock))
    (args : sourceArgs ⊒ targetArgs) :
    RewriteCFGInvariant mapping rewriteRoot newOps sourceRegion targetRegion
      (.inl (⟨succ, targetSuccIn⟩, targetArgs), targetState)
      (.inl (⟨succ, sourceSuccIn⟩, sourceArgs), sourceState) := by
  refine RewriteCFGInvariant.block (sourceBlock := ⟨succ, sourceSuccIn⟩)
    (targetBlock := ⟨succ, targetSuccIn⟩) rfl ?_
  intro sourceVariables sourceSet sourceFirst sourceFirstIn sourceFirstEq
  obtain ⟨targetVariables, targetSet⟩ := exists_setArgumentValues_of_refined targetState.variables
    targetSuccIn types args sourceSet
  obtain ⟨targetFirst, targetFirstIn, targetFirstEq, aligned⟩ :=
    firstFrame sourceFirst sourceFirstIn sourceFirstEq
  refine ⟨targetVariables, targetFirst, targetFirstIn, targetSet, targetFirstEq, ?_⟩
  have count := congrArg Array.size types
  simp only [BlockPtr.getArgumentTypes!.size_eq_getNumArguments!] at count
  have argumentEq : succ.getArguments! targetCtx.raw = succ.getArguments! sourceCtx.raw := by
    simp only [BlockPtr.getArguments!, count]
  have sourceAtStart : InsertPoint.atStart! succ sourceCtx.raw = .before sourceFirst := by
    simp [InsertPoint.atStart!_eq, sourceFirstEq]
  have targetAtStart : InsertPoint.atStart! succ targetCtx.raw = .before targetFirst := by
    simp [InsertPoint.atStart!_eq, targetFirstEq]
  have targetPreserved : ∀ value, value.InBounds sourceCtx.raw → value ∉ succ.getArguments! sourceCtx.raw →
      targetVariables.getVar? value = targetState.variables.getVar? value := by
    intro value _ notArgument
    exact VariableState.getVar?_setArgumentValues?_of_notMem_getArguments!
      (by simpa [argumentEq] using notArgument) targetSet
  have targetInstalled : ∀ value ∈ succ.getArguments! sourceCtx.raw, ∃ runtime,
      targetVariables.getVar? value = some runtime ∧ runtime.Conforms (value.getType! sourceCtx.raw) := by
    intro value member
    obtain ⟨index, bound, rfl⟩ := BlockPtr.getArguments!.mem_iff_exists_index.mp member
    have targetBound : index < succ.getNumArguments! targetCtx.raw := by omega
    have lookup := VariableState.getVar?_getArgument_of_setArgumentValues? targetBound targetSet
    refine ⟨targetArgs[index]!, lookup, ?_⟩
    have conforms := VariableState.getVar?_conforms lookup
    have typeEq := congrArg (fun a : Array TypeAttr => a[index]!) types
    rw [BlockPtr.getArgumentTypes!.getElem!_eq_getArgument bound,
      BlockPtr.getArgumentTypes!.getElem!_eq_getArgument targetBound] at typeEq
    simpa [typeEq] using conforms
  have sourceFirstParent : sourceFirst.getParent! sourceCtx.raw = some succ := by grind
  have targetFirstParent : targetFirst.getParent! targetCtx.raw = some succ := by grind
  refine {
    aligned := aligned
    sourceParent := by grind
    targetParent := by grind
    sourceReachable := .of_parent_block sourceSuccReachable sourceFirstParent
    targetReachable := .of_parent_block targetSuccReachable targetFirstParent
    states := ⟨states.1, ?_⟩
    sourceDefined := ?_
    targetDefined := ?_
    matcherValues := ?_
    matcherDefined := ?_
    matcherHistory := ?_
  }
  · apply scoped_setArgumentValues_refined sourceSuccIn targetSuccIn states.2 argumentPointers
      (sourceValues := sourceArgs) (targetValues := targetArgs) (source := sourceState.variables)
      (targetVars := targetState.variables) (sourcePoint := .at (.atEnd sourceBlock))
      (targetPoint := .at (.atEnd targetBlock))
      (nextSourcePoint := .at (.before sourceFirst)) (nextTargetPoint := .at (.before targetFirst))
      (nextSourceIn := by grind) (nextTargetIn := by grind)
      (noAlias := ?_) (sourceFrame := ?_) (targetFrame := ?_) args sourceSet targetSet
    · intro value valueIn sourceLive targetLive notArgument
      exact noAlias value valueIn (by simpa [sourceAtStart] using sourceLive)
        (by simpa [targetAtStart] using targetLive) notArgument
    · intro value _ notArgument live
      have atEntry : value.DominatesIp (InsertPoint.atStart! succ sourceCtx.raw) sourceCtx :=
        by simpa [sourceAtStart] using live
      exact (ValuePtr.DominatesIp.predecessor_exit_of_successor_entry sourceParent sourceSuccParent
        sourceSSA sourceEdge atEntry).resolve_right notArgument
    · intro value valueIn notArgument sourceLive targetLive
      have sourceEntry : value.DominatesIp (InsertPoint.atStart! succ sourceCtx.raw) sourceCtx :=
        by simpa [sourceAtStart] using sourceLive
      have targetEntry : (mapping ⟨value, valueIn⟩).val.DominatesIp
          (InsertPoint.atStart! succ targetCtx.raw) targetCtx := by simpa [targetAtStart] using targetLive
      exact (ValuePtr.DominatesIp.predecessor_exit_of_successor_entry targetParent targetSuccParent
        targetSSA targetEdge targetEntry).resolve_right (noAlias value valueIn sourceEntry targetEntry notArgument)
  · simpa [sourceAtStart] using InterpreterState.DefinesDominatingIn.setArgumentValues_succ_entry
      sourceParent sourceSuccParent sourceSSA sourceEdge sourceDefined sourceSet
  · simpa [targetAtStart] using InterpreterState.DefinesDominatingIn.setArgumentValues_succ_entry
      targetParent targetSuccParent targetSSA targetEdge targetDefined targetSet
  · change ValueResolver.WatchedRefines sourceVariables.getVar? targetVariables.getVar?
      sourceCtx sourceRegion rewriteRoot (.before sourceFirst)
    simpa [sourceAtStart] using ValueResolver.WatchedRefines.setArgumentValues_successor count
      sourceParent sourceSuccParent sourceSSA sourceEdge matcherValues args sourceSet targetSet
  · simpa [sourceAtStart] using matcherDefined.successor_entry sourceParent sourceSuccParent sourceSSA
      sourceEdge targetPreserved targetInstalled
  · simpa [sourceAtStart] using matcherHistory.successor_entry sourceDom sourceBlockIn sourceParent
      sourceSuccParent sourceSSA sourceEdge sourceSuccRooted sourceSuccReachable targetPreserved

end
end Veir.Puddle.CTree
