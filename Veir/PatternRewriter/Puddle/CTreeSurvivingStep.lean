module

public import Veir.PatternRewriter.Puddle.CTreeRewriteInvariant
public import Veir.PatternRewriter.Puddle.MatcherHistoryTransport
public import Veir.PatternRewriter.Puddle.MatcherIsolation
public import Veir.Verifier
public import Veir.PatternRewriter.Puddle.CTreeSurvivingHistory
public import Veir.PatternRewriter.Puddle.MatcherValueRefinement
import all Veir.Interpreter.CTreeStateRefinement
import all Veir.Interpreter.Refinement.Basic
import all Veir.Interpreter.VariableState
import all Veir.PatternRewriter.Puddle.CTreeRewriteInvariant
import all Veir.Dominance.Basic
import all Veir.IRNesting
import all Veir.IR.Basic
import all Veir.PatternRewriter.Puddle.DriverStructure
import all Veir.PatternRewriter.Puddle.CTreeModuleSoundness
import all Veir.Rewriter.InsertPoint

public section
namespace Veir.Puddle.CTree

/-- The state portion of the rewrite invariant at arbitrary control-flow points. -/
structure RewritePointInvariant {sourceCtx targetCtx : WfIRContext OpCode}
    (mapping : ValueMapping sourceCtx targetCtx) (rewriteRoot : OperationPtr)
    (body : RegionPtr) (sourcePoint targetPoint : InsertPoint)
    (sourcePointIn : sourcePoint.InBounds sourceCtx.raw)
    (targetPointIn : targetPoint.InBounds targetCtx.raw)
    (sourceState : InterpreterState sourceCtx) (targetState : InterpreterState targetCtx) : Prop where
  states : ScopedStateRefines mapping (.at sourcePoint) (.at targetPoint)
    (by simpa using sourcePointIn) (by simpa using targetPointIn) sourceState targetState
  sourceDefined : sourceState.DefinesDominatingIn body sourcePoint
  targetDefined : targetState.DefinesDominatingIn body targetPoint
  matcherValues : ValueResolver.WatchedRefines sourceState.variables.getVar? targetState.variables.getVar?
    sourceCtx body rewriteRoot sourcePoint
  matcherDefined : ValueResolver.DefinesDominatingIn targetState.variables.getVar?
    sourceCtx body rewriteRoot sourcePoint
  matcherHistory : ValueResolver.CTreeEquationLemmaIn targetState.variables.getVar?
    sourceCtx body rewriteRoot sourcePoint

/-- Committing an unchanged instruction introduces only its own result slots. -/
theorem ScopedStepFrame.of_after
    {sourceCtx targetCtx : WfIRContext OpCode} {mapping : ValueMapping sourceCtx targetCtx}
    (sourceOp targetOp : OperationPtr) (sourceBlock targetBlock : BlockPtr)
    (sourceIn : sourceOp.InBounds sourceCtx.raw) (targetIn : targetOp.InBounds targetCtx.raw)
    (sourceParent : sourceOp.getParent! sourceCtx.raw = some sourceBlock)
    (targetParent : targetOp.getParent! targetCtx.raw = some targetBlock)
    (sourceBlockParent : sourceBlock.getParent! sourceCtx.raw = some sourceRegion)
    (targetBlockParent : targetBlock.getParent! targetCtx.raw = some targetRegion)
    (operands : targetOp.getOperands! targetCtx.raw = mapping.applyToArray (sourceOp.getOperands! sourceCtx.raw))
    (results : targetOp.getResults! targetCtx.raw = mapping.applyToArray (sourceOp.getResults! sourceCtx.raw))
    (sourceOperands : ∀ value ∈ sourceOp.getOperands! sourceCtx.raw,
      value.InScopeAt (.at (.before sourceOp)) sourceCtx)
    (targetOperands : ∀ value (valueIn : value.InBounds sourceCtx.raw),
      value ∈ sourceOp.getOperands! sourceCtx.raw →
      (mapping ⟨value, valueIn⟩).val.InScopeAt (.at (.before targetOp)) targetCtx)
    (noAlias : ∀ value (valueIn : value.InBounds sourceCtx.raw),
      value.InScopeAt (.at (.after sourceOp sourceCtx.raw sourceBlock sourceParent sourceIn)) sourceCtx →
      value ∉ sourceOp.getResults! sourceCtx.raw →
      (mapping ⟨value, valueIn⟩).val ∉ targetOp.getResults! targetCtx.raw) :
    ScopedStepFrame mapping sourceOp targetOp sourceIn targetIn
      (.at (.before sourceOp)) (.at (.before targetOp))
      (.at (.after sourceOp sourceCtx.raw sourceBlock sourceParent sourceIn))
      (.at (.after targetOp targetCtx.raw targetBlock targetParent targetIn)) := by
  refine ⟨operands, results, sourceOperands, targetOperands, ?_, ?_, ?_⟩
  · intro value _ notResult live
    exact (ValuePtr.DominatesIp.after_iff sourceBlockParent).mp live |>.resolve_right notResult
  · intro value valueIn notResult sourceLive live
    exact (ValuePtr.DominatesIp.after_iff targetBlockParent).mp live |>.resolve_right
      (noAlias value valueIn sourceLive notResult)
  · intro value valueIn sourceLive _ notResult
    exact noAlias value valueIn sourceLive notResult

/-- The actual driver and verified scopes discharge the complete unchanged-op frame. -/
theorem Pattern.Valid.surviving_frame
    {rule : Veir.Puddle.Pattern OpCode} (valid : Pattern.Valid rule)
    {rewriter result : PatternRewriter OpCode} {root moduleOp : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (sourceDom : rewriter.ctx.Dom moduleOp) (targetDom : result.ctx.Dom moduleOp)
    (rootRooted : root.RootedAt moduleOp rewriter.ctx)
    (rootRegion : root.getParentRegion! rewriter.ctx.raw = some region)
    (rootSSA : region.hasSSADominance rewriter.ctx)
    (rootReachable : root.HierarchicallyReachable rewriter.ctx)
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    {mapping : ValueMapping rewriter.ctx result.ctx}
    (mappingEq : ∀ value (valueIn : value.InBounds rewriter.ctx.raw),
      (mapping ⟨value, valueIn⟩).val = renameRootResults root replacements.zipIdx.toList value)
    (otherResults : ∀ op, op.InBounds rewriter.ctx.raw → op ≠ root →
      mapping.applyToArray (op.getResults! rewriter.ctx.raw) (by grind) = op.getResults! rewriter.ctx.raw)
    {op : OperationPtr} (sourceIn : op.InBounds rewriter.ctx.raw) (targetIn : op.InBounds result.ctx.raw)
    (different : op ≠ root)
    (sourceRooted : op.RootedAt moduleOp rewriter.ctx)
    (targetRooted : op.RootedAt moduleOp result.ctx)
    (sourceReachable : op.HierarchicallyReachable rewriter.ctx)
    (targetReachable : op.HierarchicallyReachable result.ctx)
    {sourceBlock targetBlock : BlockPtr}
    (sourceParent : op.getParent! rewriter.ctx.raw = some sourceBlock)
    (targetParent : op.getParent! result.ctx.raw = some targetBlock)
    (sourceBlockParent : sourceBlock.getParent! rewriter.ctx.raw = some body)
    (targetBlockParent : targetBlock.getParent! result.ctx.raw = some body) :
    ScopedStepFrame mapping op op sourceIn targetIn
      (.at (.before op)) (.at (.before op))
      (.at (.after op rewriter.ctx.raw sourceBlock sourceParent sourceIn))
      (.at (.after op result.ctx.raw targetBlock targetParent targetIn)) := by
  have fields := valid.fromLocalRewrite_existing_frame sourceDom rootRooted rootRegion rootSSA
    rootReachable localRun run attached regions op sourceIn different
  have sourceRegion : op.getParentRegion! rewriter.ctx.raw = some body := by
    exact OperationPtr.getParentRegion!_eq_some_iff.mpr ⟨sourceBlock, sourceParent, sourceBlockParent⟩
  have targetRegion : op.getParentRegion! result.ctx.raw = some body := by
    exact OperationPtr.getParentRegion!_eq_some_iff.mpr ⟨targetBlock, targetParent, targetBlockParent⟩
  obtain ⟨_, sourceLocal⟩ := sourceReachable.exists_locallyReachable sourceRegion
  obtain ⟨_, targetLocal⟩ := targetReachable.exists_locallyReachable targetRegion
  have operandMapping : op.getOperands! result.ctx.raw = mapping.applyToArray (op.getOperands! rewriter.ctx.raw) := by
    rw [fields.2]
    simp only [ValueMapping.applyToArray]
    apply Array.ext
    · simp
    · intro i hi hj
      simp only [Array.getElem_map, Array.getElem_attach]
      exact (mappingEq _ _).symm
  have resultPointers : op.getResults! result.ctx.raw = op.getResults! rewriter.ctx.raw := by
    have count := congrArg Array.size fields.1.resultTypes
    simp only [OperationPtr.getResultTypes!.size_eq_getNumResults!] at count
    simp [OperationPtr.getResults!, count]
  apply ScopedStepFrame.of_after op op sourceBlock targetBlock sourceIn targetIn
    sourceParent targetParent sourceBlockParent targetBlockParent operandMapping
    (resultPointers.trans (otherResults op sourceIn different).symm)
  · intro value member
    exact sourceDom.operand_dominatesIp_before sourceRooted.1 sourceLocal member
  · intro value valueIn member
    apply targetDom.operand_dominatesIp_before targetRooted.1 targetLocal
    rw [operandMapping]
    simp only [ValueMapping.applyToArray, Array.mem_map]
    exact ⟨⟨value, member⟩, by simp, rfl⟩
  · intro value valueIn live notResult
    rw [mappingEq, resultPointers]
    exact valid.fromLocalRewrite_noAlias_after sourceDom rootRooted rootRegion rootSSA rootReachable
      localRun run sourceIn sourceParent sourceBlockParent live notResult

/-- Verified isolation supplies the target operands required by the scoped primitive theorem. -/
theorem RewriteOpInvariant.surviving_core
    {sourceCtx targetCtx : WfIRContext OpCode} {mapping : ValueMapping sourceCtx targetCtx}
    {root moduleOp op : OperationPtr} {newOps : Array OperationPtr} {body : RegionPtr}
    {sourceState : InterpreterState sourceCtx} {targetState : InterpreterState targetCtx}
    (sourceIn : op.InBounds sourceCtx.raw) (targetIn : op.InBounds targetCtx.raw)
    (sourceVerified : sourceCtx.Verified moduleOp) (targetVerified : targetCtx.Verified moduleOp)
    (targetRooted : op.RootedAt moduleOp targetCtx)
    (targetIsolated : body.nearestIsolatedScope? targetCtx.raw = some body)
    (invariant : RewriteOpInvariant mapping root newOps body body
      ⟨op, sourceIn⟩ ⟨op, targetIn⟩ sourceState targetState)
    (header : OperationHeaderPreserved sourceCtx.raw targetCtx.raw op)
    {sourceBlock targetBlock : BlockPtr}
    (sourceParent : op.getParent! sourceCtx.raw = some sourceBlock)
    (targetParent : op.getParent! targetCtx.raw = some targetBlock)
    (frame : ScopedStepFrame mapping op op sourceIn targetIn
      (.at (.before op)) (.at (.before op))
      (.at (.after op sourceCtx.raw sourceBlock sourceParent sourceIn))
      (.at (.after op targetCtx.raw targetBlock targetParent targetIn))) :
    _root_.CTree.Sim
      (fun t s =>
        (ScopedStateRefines mapping
          (.at (.after op sourceCtx.raw sourceBlock sourceParent sourceIn))
          (.at (.after op targetCtx.raw targetBlock targetParent targetIn)) (by grind) (by grind)
          s.1 t.1 ∧ ControlFlowAction.optionIsRefinedBy s.2 t.2) ∧
        PureOrErr.CanInterpretTo (Veir.CTree.interpretOpCore op targetState targetIn) (.ok t) ∧
        PureOrErr.CanInterpretTo (Veir.CTree.interpretOpCore op sourceState sourceIn) (.ok s))
      (Veir.CTree.interpretOpCore op targetState targetIn)
      (Veir.CTree.interpretOpCore op sourceState sourceIn) := by
  have targetDom : targetCtx.Dom moduleOp := targetVerified.dominance
  obtain ⟨reachableRegion, targetLocal⟩ := invariant.targetReachable.exists_locallyReachable invariant.targetParent
  have sameRegion : reachableRegion = body := by
    have := targetLocal.parentRegion
    simpa only [invariant.targetParent, Option.some.injEq] using this.symm
  subst reachableRegion
  have localOperands := OperationPtr.operands_definedInRegion_of_contextVerified targetVerified
    targetIn targetDom targetRooted targetLocal invariant.targetParent targetIsolated
  obtain ⟨targetValues, targetGet⟩ := exists_operandValues_of_definesDominatingIn op targetIn
    targetState invariant.targetDefined localOperands
    (fun _ member => targetDom.operand_dominatesIp_before targetRooted.1 targetLocal member)
  apply sim_with_outcomes (Veir.CTree.interpretOpCore_pureOrErr op targetState targetIn)
    (Veir.CTree.interpretOpCore_pureOrErr op sourceState sourceIn)
  exact sim_interpretOpCore_scoped_of_verified Veir.OpCode.interpretCTree_monotone_assumed sourceIn targetIn
    (OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants sourceVerified sourceIn)
    frame invariant.states header.opcode header.properties header.resultTypes header.successors targetGet

/-- All just-installed results are in both post-operation scopes, so the scoped
state relation also gives the concrete result-array relation. -/
theorem scoped_installedResults_refined
    {sourceCtx targetCtx : WfIRContext OpCode} {mapping : ValueMapping sourceCtx targetCtx}
    {op : OperationPtr} {sourceBlock targetBlock : BlockPtr}
    (sourceIn : op.InBounds sourceCtx.raw) (targetIn : op.InBounds targetCtx.raw)
    (sourceParent : op.getParent! sourceCtx.raw = some sourceBlock)
    (targetParent : op.getParent! targetCtx.raw = some targetBlock)
    (sourceBlockParent : sourceBlock.getParent! sourceCtx.raw = some sourceRegion)
    (targetBlockParent : targetBlock.getParent! targetCtx.raw = some targetRegion)
    (counts : op.getNumResults! targetCtx.raw = op.getNumResults! sourceCtx.raw)
    (resultPointers : mapping.applyToArray (op.getResults! sourceCtx.raw) = op.getResults! targetCtx.raw)
    {sourceBefore sourceAfter : VariableState sourceCtx} {targetBefore targetAfter : VariableState targetCtx}
    {sourceValues targetValues : Array RuntimeValue}
    (sourceSet : sourceBefore.setResultValues? op sourceValues sourceIn = some sourceAfter)
    (targetSet : targetBefore.setResultValues? op targetValues targetIn = some targetAfter)
    (related : sourceAfter.isRefinedByAt targetAfter mapping
      (.at (.after op sourceCtx.raw sourceBlock sourceParent sourceIn))
      (.at (.after op targetCtx.raw targetBlock targetParent targetIn)) (by grind) (by grind)) :
    RuntimeValue.arrayIsRefinedBy sourceValues targetValues := by
  have sourceSize := VariableState.setResultValues?.getNumRseults!_eq_size sourceSet
  have targetSize := VariableState.setResultValues?.getNumRseults!_eq_size targetSet
  have mapped := ValueMapping.applyToArray_getResults!_ext sourceIn resultPointers
  refine ⟨by omega, ?_⟩
  intro index indexIn
  have sourceBound : index < op.getNumResults! sourceCtx.raw := by omega
  have targetBound : index < op.getNumResults! targetCtx.raw := by omega
  have pointerIn : (op.getResult index : ValuePtr).InBounds sourceCtx.raw := by grind
  have mapPointer := mapped index sourceBound
  apply related (op.getResult index) pointerIn
  · exact (ValuePtr.DominatesIp.after_iff sourceBlockParent).mpr
      (Or.inr (OperationPtr.getResults!.mem_getResult sourceBound))
  · rw [mapPointer]
    exact (ValuePtr.DominatesIp.after_iff targetBlockParent).mpr
      (Or.inr (OperationPtr.getResults!.mem_getResult targetBound))
  · exact VariableState.getVar?_getResult_of_setResultValues? sourceBound sourceSet
  · rw [mapPointer]
    exact VariableState.getVar?_getResult_of_setResultValues? targetBound targetSet

/-- A surviving instruction's next pointer is redirected exactly when it reached the old root. -/
theorem Pattern.fromLocalRewrite_next_redirect
    (rule : Veir.Puddle.Pattern OpCode)
    {rewriter result : PatternRewriter OpCode} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (notOwn : ∀ value ∈ replacements, ∀ index < root.getNumResults! rewriter.ctx.raw,
      (root.getResult index : ValuePtr) ≠ value)
    {op : OperationPtr} (opIn : op.InBounds rewriter.ctx.raw) (different : op ≠ root) :
    op.getNextOp! result.ctx.raw =
      (op.getNextOp! rewriter.ctx.raw).bind (redirectedOperation rewriter.ctx.raw root newOps) := by
  by_cases predecessor : root.getPrevOp! rewriter.ctx.raw = some op
  · have sourceNext : op.getNextOp! rewriter.ctx.raw = some root :=
      IRContext.WellFormed.OperationPtr_next!_eq_some_of_prev!_eq_some rootIn rewriter.ctx.wellFormed predecessor
    have chain := rule.fromLocalRewrite_predecessor_splice localRun run attached regions notOwn predecessor
    rw [sourceNext]
    simp only [Option.bind_some, redirectedOperation, ↓reduceIte]
    cases ops : newOps.toList with
    | nil =>
      have empty : newOps = #[] := by simpa using ops
      simpa [ForwardChain, ops, empty] using chain
    | cons first rest =>
      have firstGet : newOps[0]? = some first := by
        rw [← Array.getElem?_toList, ops]
        rfl
      rw [ops] at chain
      simpa [firstGet] using chain.1
  · have next := rule.fromLocalRewrite_untouched_next localRun run attached regions notOwn op opIn different predecessor
    rw [next]
    cases sourceNext : op.getNextOp! rewriter.ctx.raw with
    | none => rfl
    | some nextOp =>
      have notRoot : nextOp ≠ root := by
        intro equal
        subst nextOp
        apply predecessor
        exact IRContext.WellFormed.OperationPtr_prev!_eq_some_of_next!_eq_some opIn rewriter.ctx.wellFormed sourceNext
      simp only [Option.bind_some, redirectedOperation, if_neg notRoot]

/-- Ordinary original instructions take one step in each batching schedule. -/
theorem Pattern.surviving_batch_counts
    (rule : Veir.Puddle.Pattern OpCode)
    {rewriter : PatternRewriter OpCode} {root : OperationPtr} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    {targetCtx : WfIRContext OpCode} {op : OperationPtr}
    (sourceIn : op.InBounds rewriter.ctx.raw) (targetIn : op.InBounds targetCtx.raw)
    (different : op ≠ root)
    (source : InterpreterState rewriter.ctx) (target : InterpreterState targetCtx) :
    rewriteSourceBatch root newOps (.inr ⟨op, sourceIn⟩, source) = 1 ∧
      rewriteTargetBatch newOps (.inr ⟨op, targetIn⟩, target) = 1 := by
  have fresh := (rule.interpret_structure localRun).1
  have notFirst : newOps[0]? ≠ some op := by
    intro first
    exact ((fresh op).mp (Array.mem_of_getElem? first)).2 sourceIn
  simp [rewriteSourceBatch, rewriteTargetBatch, different, notFirst]

/-- Successful aligned outcomes preserve the entire state invariant after a surviving operation. -/
theorem Pattern.Valid.surviving_after
    {rule : Veir.Puddle.Pattern OpCode} (valid : Pattern.Valid rule)
    {rewriter result : PatternRewriter OpCode} {root moduleOp : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (sourceDom : rewriter.ctx.Dom moduleOp)
    (rootRooted : root.RootedAt moduleOp rewriter.ctx)
    (rootRegion : root.getParentRegion! rewriter.ctx.raw = some region)
    (rootSSA : region.hasSSADominance rewriter.ctx)
    (rootReachable : root.HierarchicallyReachable rewriter.ctx)
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    {mapping : ValueMapping rewriter.ctx result.ctx}
    {op : OperationPtr} (sourceIn : op.InBounds rewriter.ctx.raw) (targetIn : op.InBounds result.ctx.raw)
    (different : op ≠ root) (sourceRooted : op.RootedAt moduleOp rewriter.ctx)
    {sourceBlock targetBlock : BlockPtr}
    (sourceParent : op.getParent! rewriter.ctx.raw = some sourceBlock)
    (targetParent : op.getParent! result.ctx.raw = some targetBlock)
    (sourceBlockParent : sourceBlock.getParent! rewriter.ctx.raw = some body)
    (targetBlockParent : targetBlock.getParent! result.ctx.raw = some body)
    (bodySSA : body.hasSSADominance rewriter.ctx)
    (resultPointers : mapping.applyToArray (op.getResults! rewriter.ctx.raw) = op.getResults! result.ctx.raw)
    {sourceState sourceFinal : InterpreterState rewriter.ctx}
    {targetState targetFinal : InterpreterState result.ctx} {sourceAction targetAction : Option ControlFlowAction}
    (invariant : RewriteOpInvariant mapping root newOps body body
      ⟨op, sourceIn⟩ ⟨op, targetIn⟩ sourceState targetState)
    (related : ScopedStateRefines mapping
      (.at (.after op rewriter.ctx.raw sourceBlock sourceParent sourceIn))
      (.at (.after op result.ctx.raw targetBlock targetParent targetIn)) (by grind) (by grind)
      sourceFinal targetFinal)
    (sourceOutcome : PureOrErr.CanInterpretTo
      (Veir.CTree.interpretOpCore op sourceState sourceIn) (.ok (sourceFinal, sourceAction)))
    (targetOutcome : PureOrErr.CanInterpretTo
      (Veir.CTree.interpretOpCore op targetState targetIn) (.ok (targetFinal, targetAction))) :
    RewritePointInvariant mapping root body
      (.after op rewriter.ctx.raw sourceBlock sourceParent sourceIn)
      (.after op result.ctx.raw targetBlock targetParent targetIn) (by grind) (by grind)
      sourceFinal targetFinal := by
  have header := (valid.fromLocalRewrite_existing_frame sourceDom rootRooted rootRegion rootSSA
    rootReachable localRun run attached regions op sourceIn different).1
  have count : op.getNumResults! result.ctx.raw = op.getNumResults! rewriter.ctx.raw := by
    simpa only [OperationPtr.getResultTypes!.size_eq_getNumResults!] using congrArg Array.size header.resultTypes
  obtain ⟨sourceOperands, sourceRaw, _, _, sourceSet, _, _⟩ :=
    interpretOpCore_outcome op sourceIn sourceState (sourceFinal, sourceAction) sourceOutcome
  obtain ⟨targetOperands, targetRaw, _, _, targetSet, _, _⟩ :=
    interpretOpCore_outcome op targetIn targetState (targetFinal, targetAction) targetOutcome
  have rawRelated := scoped_installedResults_refined sourceIn targetIn sourceParent targetParent
    sourceBlockParent targetBlockParent count resultPointers sourceSet targetSet related.2
  have histories := surviving_matcher_history valid sourceDom rootRooted rootRegion rootSSA rootReachable
    localRun run attached regions sourceIn different sourceRooted sourceParent sourceBlockParent bodySSA
    invariant.sourceReachable invariant.matcherDefined invariant.matcherHistory targetOutcome
  refine ⟨related, ?_, ?_, ?_, histories.1, histories.2⟩
  · exact invariant.sourceDefined.setResultValues sourceParent sourceBlockParent sourceSet
  · exact invariant.targetDefined.setResultValues targetParent targetBlockParent targetSet
  · exact ValueResolver.WatchedRefines.setResultValues_after count sourceParent sourceBlockParent
      invariant.matcherValues rawRelated sourceSet targetSet

end Veir.Puddle.CTree
