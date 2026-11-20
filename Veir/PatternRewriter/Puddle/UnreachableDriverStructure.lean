module
public import Veir.PatternRewriter.Puddle.DriverFunctionStructure
public import Veir.PatternRewriter.Puddle.MatcherHistoryTransport
public import Veir.Interpreter.CTreeUnreachableRefinement
import all Veir.PatternRewriter.Puddle.DriverStructure
import all Veir.PatternRewriter.Puddle.DriverScope
import all Veir.PatternRewriter.Puddle.Execution
import all Veir.IR.Basic
import all Veir.IRNesting
import all Veir.Dominance.Basic

namespace Veir.Puddle
public section

/-- A successful guarded driver rewrite supplies its structural safety contract without
requiring semantic matcher scope or reachability of the rewritten operation. -/
theorem Pattern.fromLocalRewrite_runtime_notOwn (rule : Pattern OpCode)
    {rewriter result : PatternRewriter OpCode} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result) :
    ∀ value ∈ replacements, ∀ index < root.getNumResults! rewriter.ctx.raw,
      (root.getResult index : ValuePtr) ≠ value :=
  fromLocalRewrite_result_notOwn_indexed localRun run

/-- Rewriting an unreachable operation does not change the operands or semantic header
of any reachable operation rooted in the dominance tree. -/
theorem Pattern.fromLocalRewrite_unreachable_operation_frame (rule : Pattern OpCode)
    {rewriter result : PatternRewriter OpCode} {root moduleOp : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (dom : rewriter.ctx.Dom moduleOp) (unreachable : ¬root.HierarchicallyReachable rewriter.ctx)
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (op : OperationPtr) (opIn : op.InBounds rewriter.ctx.raw)
    (rooted : op.RootedAt moduleOp rewriter.ctx)
    (reachable : op.HierarchicallyReachable rewriter.ctx)
    (parentRegion : op.getParentRegion! rewriter.ctx.raw = some region) :
    op.InBounds result.ctx.raw ∧
      Veir.CTree.PointerOperationFrame (sourceCtx := rewriter.ctx) (targetCtx := result.ctx) op := by
  have different : op ≠ root := by intro equal; subst op; exact unreachable reachable
  have notOwn := rule.fromLocalRewrite_runtime_notOwn localRun run
  obtain ⟨header, operands⟩ := rule.fromLocalRewrite_existing_frame localRun run attached regions notOwn op opIn different
  have disjoint := dom.not_mem_results_of_not_hierarchicallyReachable rooted.1 parentRegion reachable unreachable
  have sourceArity : replacements.size = root.getNumResults! rewriter.ctx.raw := by
    have types := (rule.interpret_preserves_existing_fields localRun root rootIn).1.resultTypes
    have counts : root.getNumResults! created.raw = root.getNumResults! rewriter.ctx.raw := by
      simpa only [OperationPtr.getResultTypes!.size_eq_getNumResults!] using congrArg Array.size types
    exact (fromLocalRewrite_result_arity localRun run).trans counts
  have operandsSame : op.getOperands! result.ctx.raw = op.getOperands! rewriter.ctx.raw := by
    rw [operands]
    calc
      _ = (op.getOperands! rewriter.ctx.raw).map id := by
        apply Array.map_congr_left
        intro pointer member
        apply renameRootResults_eq_self
        intro pair pairMember equal
        have index := Array.mem_zipIdx' (xs := replacements) (x := pair.1) (i := pair.2)
          (by simpa only [Array.mem_toList_iff] using pairMember)
        apply disjoint pointer member
        rw [equal]
        exact OperationPtr.getResults!.mem_getResult (by omega)
      _ = _ := by simp
  have notPredecessor : root.getPrevOp! rewriter.ctx.raw ≠ some op := by
    intro previous
    have next := IRContext.WellFormed.OperationPtr_next!_eq_some_of_prev!_eq_some
      rootIn rewriter.ctx.wellFormed previous
    obtain ⟨block, opParent, blockParent⟩ := OperationPtr.getParentRegion!_eq_some_iff.mp parentRegion
    have rootParent : root.getParent! rewriter.ctx.raw = some block := by grind
    exact unreachable (OperationPtr.HierarchicallyReachable.of_parent_block
      (reachable.parent_block opParent) rootParent)
  have nextSame := rule.fromLocalRewrite_untouched_next localRun run attached regions notOwn
    op opIn different notPredecessor
  refine ⟨rule.fromLocalRewrite_existing_inBounds localRun run attached regions notOwn op opIn different, ?_⟩
  exact ⟨header.opcode, fun code => header.properties code, header.resultTypes, operandsSame,
    header.successors, nextSame, header.parent⟩

/-- An unreachable rewrite cannot occur at the entry of a reachable block. Its first
operation and argument interface therefore remain exactly the same. -/
theorem Pattern.fromLocalRewrite_unreachable_block_frame (rule : Pattern OpCode)
    {rewriter result : PatternRewriter OpCode} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (unreachable : ¬root.HierarchicallyReachable rewriter.ctx)
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (block : BlockPtr) (blockIn : block.InBounds rewriter.ctx.raw)
    (reachable : block.HierarchicallyReachable rewriter.ctx) :
    block.InBounds result.ctx.raw ∧
      block.getArgumentTypes! result.ctx.raw = block.getArgumentTypes! rewriter.ctx.raw ∧
      block.getFirstOp! result.ctx.raw = block.getFirstOp! rewriter.ctx.raw := by
  have notOwn := rule.fromLocalRewrite_runtime_notOwn localRun run
  have notFirst : block.getFirstOp! rewriter.ctx.raw ≠ some root := by
    intro first
    exact unreachable (OperationPtr.HierarchicallyReachable.of_parent_block reachable (by grind))
  exact ⟨(rule.fromLocalRewrite_region_block_inBounds localRun run attached regions notOwn).2 block blockIn,
    (rule.fromLocalRewrite_regionBlockHeaders localRun run attached regions notOwn).argumentTypes block,
    rule.fromLocalRewrite_other_block_entry localRun run attached regions notOwn block blockIn notFirst⟩

/-- The actual guarded local driver is an exact structural frame on the source module's
reachable instructions and blocks when the rewritten root is unreachable. -/
theorem Pattern.fromLocalRewrite_unreachable_context_frame (rule : Pattern OpCode)
    {rewriter result : PatternRewriter OpCode} {root moduleOp : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (dom : rewriter.ctx.Dom moduleOp) (unreachable : ¬root.HierarchicallyReachable rewriter.ctx)
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0) :
    Veir.CTree.ReachableContextFrame rewriter.ctx result.ctx moduleOp := by
  constructor
  · intro op region opIn parent rooted reachable
    exact rule.fromLocalRewrite_unreachable_operation_frame dom unreachable localRun run attached regions
      op opIn rooted reachable parent
  · intro block blockIn rooted reachable
    exact rule.fromLocalRewrite_unreachable_block_frame unreachable localRun run attached regions
      block blockIn reachable

end
end Veir.Puddle
