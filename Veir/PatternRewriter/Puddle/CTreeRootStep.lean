module
public import Veir.Verifier
public import Veir.PatternRewriter.Puddle.CreationHistoryFrame
public import Veir.PatternRewriter.Puddle.CTreeRewriteInvariant
public import Veir.PatternRewriter.Puddle.CTreeCreatedInvariant
public import Veir.PatternRewriter.Puddle.MatcherIsolation
import all Veir.PatternRewriter.Puddle.CreationCheckedSemantics
import all Veir.PatternRewriter.Puddle.CTreeModuleSoundness
import all Veir.PatternRewriter.Puddle.CTreeRewriteInvariant
import all Veir.PatternRewriter.Puddle.MatcherResolverHistory
import all Veir.Interpreter.CTreeEntryInvariant
import all Veir.Rewriter.InsertPoint
public section
namespace Veir.Puddle.CTree

/-- Actual root replacement preserves the full instruction-entry invariant.
The extra premises are linked-list/interface facts, not runtime simulations. -/
theorem Pattern.Valid.root_checked_invariant
    {rule : Veir.Puddle.Pattern OpCode} (valid : Pattern.Valid rule)
    {rewriter result : PatternRewriter OpCode} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (sourceVerified : rewriter.ctx.Verified moduleOp) (targetVerified : result.ctx.Verified moduleOp)
    (rootRooted : root.RootedAt moduleOp rewriter.ctx)
    (rootRegion : root.getParentRegion! rewriter.ctx.raw = some region)
    (rootSSA : region.hasSSADominance rewriter.ctx)
    (rootReachable : root.HierarchicallyReachable rewriter.ctx)
    (scope : region.nearestIsolatedScope? rewriter.ctx.raw = some region)
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    {mapping : ValueMapping rewriter.ctx result.ctx}
    (resultMapping : replacements = mapping.applyToArray (root.getResults! rewriter.ctx.raw))
    (fixedOther : ∀ value (valueIn : value.InBounds rewriter.ctx.raw),
      value ∉ root.getResults! rewriter.ctx.raw → (mapping ⟨value, valueIn⟩).val = value)
    (first next : OperationPtr) (firstIn : first.InBounds result.ctx.raw)
    (sourceNextIn : next.InBounds rewriter.ctx.raw) (targetNextIn : next.InBounds result.ctx.raw)
    (starts : (newOps.toList.head? <|> some next) = some first)
    (nextEq : root.getNextOp! rewriter.ctx.raw = some next) (nextDifferent : next ≠ root)
    {block : BlockPtr} (rootParent : root.getParent! rewriter.ctx.raw = some block)
    (sourceBlockParent : block.getParent! rewriter.ctx.raw = some region)
    (targetBlockParent : block.getParent! result.ctx.raw = some region)
    (sourceNextParent : next.getParent! rewriter.ctx.raw = some block)
    (targetNextParent : next.getParent! result.ctx.raw = some block)
    (sourceState : InterpreterState rewriter.ctx) (targetState : InterpreterState result.ctx)
    (invariant : RewriteOpInvariant mapping root newOps region region
      ⟨root, rootIn⟩ ⟨first, firstIn⟩ sourceState targetState) :
    _root_.CTree.Sim (fun target source =>
      RewriteOpInvariant mapping root newOps region region
        ⟨next, sourceNextIn⟩ ⟨next, targetNextIn⟩ source.1 target ∧ source.2 = none)
      (interpretCreatedOpsChecked result.ctx newOps.toList targetState)
      (Veir.CTree.interpretOpCore root sourceState rootIn) := by
  have sourceDom : rewriter.ctx.Dom moduleOp := sourceVerified.dominance
  obtain ⟨localRegion, localReachable⟩ := rootReachable.exists_locallyReachable rootRegion
  have sameRegion : localRegion = region := by grind
  subst localRegion
  have localOperands := root.operands_definedInRegion_of_contextVerified sourceVerified rootIn
    sourceDom rootRooted localReachable rootRegion scope
  have operandScopes : ∀ value ∈ root.getOperands! rewriter.ctx.raw,
      value.DominatesIp (.before root) rewriter.ctx := by
    intro value member
    grind [WfIRContext.Dom.operand_dominatesIp_before]
  obtain ⟨sourceValues, targetValues, sourceGet, targetGet, values⟩ :=
    invariant.root_operandValues localOperands operandScopes
  have fields := valid.fromLocalRewrite_created_fields sourceDom rootRooted rootRegion rootSSA rootReachable
    localRun run attached regions
  have structural := valid.fromLocalRewrite_frame_and_splice sourceDom rootRooted rootRegion rootSSA rootReachable
    localRun run attached regions
  have chain : ForwardChain result.ctx.raw newOps.toList (some next) := by simpa only [nextEq] using structural.2.1
  have bounds : ∀ op ∈ newOps.toList, op.InBounds result.ctx.raw := by
    intro op member
    exact (fields op (by simpa using member)).1
  have parents : ∀ op ∈ newOps.toList, op.getParent! result.ctx.raw = some block := by
    intro op member
    exact (structural.2.2 op (by simpa using member)).trans rootParent
  have startsHead (nonempty : newOps.toList ≠ []) : newOps.toList.head? = some first := by
    cases listEq : newOps.toList with
    | nil => exact False.elim (nonempty listEq)
    | cons head tail => simpa [listEq] using starts
  have emptyFirst (empty : newOps.toList = []) : first = next := by simpa [empty] using starts.symm
  have oldValues : ∀ (value : ValuePtr) (valueIn : value.InBounds rewriter.ctx.raw),
      value ∉ root.getResults! rewriter.ctx.raw →
      value.InScopeAt (.at (.before next)) rewriter.ctx →
      (mapping ⟨value, valueIn⟩).val.InScopeAt (.at (.before next)) result.ctx →
      ∀ sourceValue targetValue,
      sourceState.variables.getVar? value = some sourceValue →
      targetState.variables.getVar? (mapping ⟨value, valueIn⟩) = some targetValue →
      RuntimeValue.isRefinedBy sourceValue targetValue := by
    intro value valueIn notResult sourceLive targetLive sourceValue targetValue sourceLookup targetLookup
    have sourceBefore := ValuePtr.inScopeAt_before_of_before_next rootParent rootIn sourceBlockParent
      nextEq sourceLive notResult
    have targetBefore : (mapping ⟨value, valueIn⟩).val.InScopeAt (.at (.before first)) result.ctx := by
      by_cases empty : newOps.toList = []
      · simpa only [emptyFirst empty] using targetLive
      · apply scope_back_through_chain newOps.toList first next block (startsHead empty)
          bounds parents targetBlockParent chain _ ?_ targetLive
        intro op member
        rw [fixedOther value valueIn notResult]
        exact Pattern.interpret_created_results_disjoint_source rule localRun (by simpa using member) valueIn
    exact invariant.states.2 value valueIn sourceBefore targetBefore sourceValue sourceLookup targetValue targetLookup
  have localSimulation := valid.checked_createdOps_rootCore
    (sourcePointIn := by grind) (targetPointIn := by grind) sourceDom rootRooted rootRegion rootSSA
    rootReachable localRun run attached regions
    (OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants sourceVerified rootIn)
    (fun op _ hop => OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants targetVerified hop)
    sourceState targetState (fun matched matchRun =>
      valid.runtimeEquations_of_resolver_history targetState.variables.getVar? sourceDom sourceVerified rootRooted rootRegion
        rootReachable rootIn matchRun
        (valid.regionScope_of_run_verified sourceVerified sourceDom rootRooted rootRegion rootReachable
          rootIn scope matchRun) localOperands invariant.matcherDefined invariant.matcherHistory)
    targetGet sourceValues sourceGet values invariant.states.1 resultMapping fixedOther oldValues
  have observed := sim_with_outcomes (interpretCreatedOpsChecked_pureOrErr newOps.toList targetState)
    (Veir.CTree.interpretOpCore_pureOrErr root sourceState rootIn) _ localSimulation
  apply observed.mono
  rintro target source ⟨⟨states, noAction⟩, targetOutcome, sourceOutcome⟩
  obtain ⟨operands, raw, _, _, sourceSet, sourceMemory, sourceAction⟩ :=
    interpretOpCore_outcome root rootIn sourceState source sourceOutcome
  have frame := Pattern.interpret_checked_preserves_source_lookups rule localRun targetOutcome
  have sourceDefined := invariant.sourceDefined.setResultValues rootParent sourceBlockParent sourceSet
    (after := source.1.memory)
  rw [InsertPoint.after_eq_of_some_next nextEq] at sourceDefined
  have targetDefined : target.DefinesDominatingIn region (.before next) := by
    by_cases empty : newOps.toList = []
    · have targetEqual : targetState = target := by
        have observedPure : PureOrErr.CanInterpretTo (pure targetState : Tree (InterpreterState result.ctx)) (.ok target) := by
          simpa only [empty, interpretCreatedOpsChecked] using targetOutcome
        have equal := (PureOrErr.CanInterpretTo.pure_iff _ _).mp observedPure
        exact (Interp.ok.inj equal).symm
      subst target
      simpa only [emptyFirst empty] using invariant.targetDefined
    · exact interpretCreatedOpsChecked_definesDominatingIn newOps.toList first next (startsHead empty) bounds
        parents targetBlockParent chain invariant.targetDefined targetOutcome
  have targetNextReachable : next.HierarchicallyReachable result.ctx := by
    by_cases empty : newOps.toList = []
    · simpa only [emptyFirst empty] using invariant.targetReachable
    · have firstMember := List.mem_of_head? (startsHead empty)
      exact OperationPtr.HierarchicallyReachable.of_parent_block
        (invariant.targetReachable.parent_block (parents first firstMember)) targetNextParent
  have sourceNextReachable := OperationPtr.HierarchicallyReachable.of_parent_block
    (rootReachable.parent_block rootParent) sourceNextParent
  refine ⟨⟨?_, ?_, ?_, sourceNextReachable, targetNextReachable, states, sourceDefined, targetDefined,
    invariant.matcherValues_after_root rootRooted rootSSA sourceSet frame (.before next),
    (invariant.matcherDefined.of_lookup_eq frame).from_root (.before next),
    (invariant.matcherHistory.of_lookup_eq frame).from_root (.before next)⟩, noAction⟩
  · simp [redirectedOperation, nextDifferent]
  · grind
  · grind

end Veir.Puddle.CTree
