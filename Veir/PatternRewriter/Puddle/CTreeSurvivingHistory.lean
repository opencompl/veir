module
public import Veir.PatternRewriter.Puddle.CTreeRewriteInvariant
public import Veir.PatternRewriter.Puddle.MatcherHistoryTransport
public import Veir.Interpreter.CTreeControlFlow
import all Veir.PatternRewriter.Puddle.MatcherResolverHistory
import all Veir.PatternRewriter.Puddle.DriverFunctionStructure
import all Veir.PatternRewriter.Puddle.CTreeModuleSoundness
import all Veir.Interpreter.VariableState
import all Veir.IR.Basic
import all Veir.IRNesting
import all Veir.Dominance.Basic
import all Veir.Interpreter.CTreeInterpreter

namespace Veir.Puddle.CTree
public section

/-- Successful execution of a surviving operation updates the original-model matcher
history and definedness using the target's concrete resolver. No simulation premise is needed. -/
theorem surviving_matcher_history
    {rule : Pattern OpCode} (valid : Pattern.Valid rule)
    {rewriter result : PatternRewriter OpCode} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    {region : RegionPtr} {irRoot : IRNode}
    (ctxDom : rewriter.ctx.Dom irRoot) (rootRooted : root.RootedAt irRoot rewriter.ctx)
    (rootRegion : root.getParentRegion! rewriter.ctx.raw = some region)
    (rootSSA : region.hasSSADominance rewriter.ctx)
    (rootReachable : root.HierarchicallyReachable rewriter.ctx)
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    {op : OperationPtr} (opIn : op.InBounds rewriter.ctx.raw) (different : op ≠ root)
    {opBlock : BlockPtr} {opRegion : RegionPtr}
    (opRooted : op.RootedAt irRoot rewriter.ctx)
    (opParent : op.getParent! rewriter.ctx.raw = some opBlock)
    (opRegionParent : opBlock.getParent! rewriter.ctx.raw = some opRegion)
    (opSSA : opRegion.hasSSADominance rewriter.ctx)
    (opReachable : op.HierarchicallyReachable rewriter.ctx)
    {targetState targetFinal : InterpreterState result.ctx} {action : Option ControlFlowAction}
    (defined : ValueResolver.DefinesDominatingIn targetState.variables.getVar?
      rewriter.ctx opRegion root (.before op))
    (history : ValueResolver.CTreeEquationLemmaIn targetState.variables.getVar?
      rewriter.ctx opRegion root (.before op))
    (outcome : PureOrErr.CanInterpretTo
      (Veir.CTree.interpretOpCore op targetState
        (rule.fromLocalRewrite_existing_inBounds localRun run attached regions
          (valid.replacement_contract_of_interpret ctxDom rootRooted rootRegion rootSSA rootReachable rootIn localRun).1
          op opIn different)) (.ok (targetFinal, action))) :
    ValueResolver.DefinesDominatingIn targetFinal.variables.getVar? rewriter.ctx opRegion root
      (InsertPoint.after op rewriter.ctx.raw opBlock) ∧
    ValueResolver.CTreeEquationLemmaIn targetFinal.variables.getVar? rewriter.ctx opRegion root
      (InsertPoint.after op rewriter.ctx.raw opBlock) := by
  have contract := valid.replacement_contract_of_interpret ctxDom rootRooted rootRegion rootSSA
    rootReachable rootIn localRun
  have targetIn := rule.fromLocalRewrite_existing_inBounds localRun run attached regions contract.1 op opIn different
  have header := (valid.fromLocalRewrite_existing_frame ctxDom rootRooted rootRegion rootSSA rootReachable
    localRun run attached regions op opIn different).1
  have blockHeaders := rule.fromLocalRewrite_regionBlockHeaders localRun run attached regions contract.1
  have counts : op.getNumResults! result.ctx.raw = op.getNumResults! rewriter.ctx.raw := by
    simpa only [OperationPtr.getResultTypes!.size_eq_getNumResults!] using congrArg Array.size header.resultTypes
  have resultPtrs : op.getResults! result.ctx.raw = op.getResults! rewriter.ctx.raw := by
    simp only [OperationPtr.getResults!, counts]
  obtain ⟨operands, raw, collected, rawOutcome, installed, memory, actionEq⟩ :=
    interpretOpCore_outcome op targetIn targetState (targetFinal, action) outcome
  have preserved : ∀ value, value.InBounds rewriter.ctx.raw → value ∉ op.getResults! rewriter.ctx.raw →
      targetFinal.variables.getVar? value = targetState.variables.getVar? value := by
    intro value bounds notResult
    exact VariableState.getVar?_setResultValues?_of_notMem_getResults!
      (by simpa only [resultPtrs] using notResult) installed
  have sourceOpRegion : op.getParentRegion! rewriter.ctx.raw = some opRegion := by grind
  constructor
  · apply defined.after_operation opParent opRegionParent preserved
    intro value member
    have sourceBound : value.InBounds rewriter.ctx.raw := by grind
    have notRoot : value ∉ root.getResults! rewriter.ctx.raw := by
      grind [OperationPtr.getResults!.mem_iff_exists_index, OperationPtr.getResult_def]
    obtain ⟨index, indexIn, equal⟩ := OperationPtr.getResults!.mem_iff_exists_index.mp member
    have got := VariableState.getVar?_getResult_of_setResultValues? (by omega : index < op.getNumResults! result.ctx.raw) installed
    have valueGet : targetFinal.variables.getVar? value = some raw.1[index]! := by simpa only [equal] using got
    refine ⟨_, valueGet, ?_⟩
    have types := value_type_eq_of_driver_headers
      (fun current bounds different => (valid.fromLocalRewrite_existing_frame ctxDom rootRooted rootRegion rootSSA
        rootReachable localRun run attached regions current bounds different).1.resultTypes)
      blockHeaders sourceBound notRoot
    rw [← types]
    exact VariableState.getVar?_conforms valueGet
  · apply history.after_operation ctxDom opRooted sourceOpRegion opSSA opReachable opParent preserved
    intro nonterm watched
    cases watched with
    | Before proper =>
      have operandPtrs := valid.fromLocalRewrite_dominator_operands ctxDom rootRooted rootRegion rootSSA
        rootReachable localRun run attached regions opIn proper
      have sourceCollected : (op.getOperands! rewriter.ctx.raw).mapM targetState.variables.getVar? = some operands := by
        simpa only [VariableState.getOperandValues, operandPtrs] using collected
      obtain ⟨reachableRegion, locallyReachable⟩ := opReachable.exists_locallyReachable sourceOpRegion
      have notSelf : ¬op.ProperlyDominates op rewriter.ctx false :=
        OperationPtr.not_properlyDominates_self opRooted sourceOpRegion opSSA
      have operandsNoResults := ctxDom.not_mem_results_of_mem_operands opRooted.1 locallyReachable notSelf
      have resultsGet : (op.getResults! rewriter.ctx.raw).mapM targetFinal.variables.getVar? = some raw.1 := by
        rw [← resultPtrs]
        exact VariableState.getResults_of_setResultValues installed
      have targetRaw := rawOutcome
      rw [interpretCTree_eq_bang] at targetRaw
      rw [header.properties (op.getOpType! result.ctx.raw)] at targetRaw
      rw [header.opcode] at targetRaw
      have sourceRaw : PureOrErr.CanInterpretTo
          (Veir.CTree.interpretOp' (op.getOpType! rewriter.ctx.raw)
            (op.getProperties! rewriter.ctx.raw (op.getOpType! rewriter.ctx.raw))
            (op.getResultTypes! rewriter.ctx.raw) operands (op.getSuccessors! rewriter.ctx.raw)
            targetState.memory (op.getRegions! rewriter.ctx.raw)) (.ok raw) := by
        simpa only [header.resultTypes, header.successors,
          Veir.CTree.interpretOp'] using targetRaw
      have rawAction := Veir.CTree.interpretOp'_no_action_of_nonterm _ _ _ _ _ _ _ _ _ _ nonterm sourceRaw
      apply ValueResolver.ctreeEquationHolds_of_outcome sourceCollected ?_ resultsGet
      · simpa only [← rawAction] using sourceRaw
      · intro value member
        exact preserved value (by grind) (operandsNoResults value member)

end
end Veir.Puddle.CTree
