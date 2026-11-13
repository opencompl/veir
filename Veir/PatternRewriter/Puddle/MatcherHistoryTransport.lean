module

public import Veir.PatternRewriter.Puddle.DriverScope
public import Veir.PatternRewriter.Puddle.MatcherResolverHistory
public import Veir.PatternRewriter.Puddle.DriverFunctionStructure
import all Veir.Dominance.Basic
import all Veir.IR.Basic

public section
namespace Veir.Puddle

/-- Surviving original SSA pointers retain their declared types under the driver's header frame. -/
theorem value_type_eq_of_driver_headers
    {source target : WfIRContext OpCode} {root : OperationPtr}
    (operations : ∀ op, op.InBounds source.raw → op ≠ root →
      op.getResultTypes! target.raw = op.getResultTypes! source.raw)
    (blocks : RegionBlockHeadersPreserved source.raw target.raw)
    {value : ValuePtr} (bounds : value.InBounds source.raw)
    (survives : value ∉ root.getResults! source.raw) :
    value.getType! target.raw = value.getType! source.raw := by
  cases value with
  | opResult result =>
    rcases result with ⟨op, index⟩
    have bound : index < op.getNumResults! source.raw := by
      grind [OpResultPtr.InBounds, OperationPtr.getNumResults!]
    have different : op ≠ root := by
      intro equal
      subst op
      exact survives (OperationPtr.getResults!.mem_getResult bound)
    have types := operations op (by grind [ValuePtr.InBounds, OpResultPtr.InBounds]) different
    have targetBound : index < op.getNumResults! target.raw := by
      have size := congrArg Array.size types
      simp only [OperationPtr.getResultTypes!.size_eq_getNumResults!] at size
      omega
    change (op.getResult index).getType! target.raw = (op.getResult index).getType! source.raw
    rw [← OperationPtr.getResultTypes!.getElem!_eq targetBound,
      ← OperationPtr.getResultTypes!.getElem!_eq bound, types]
  | blockArgument argument =>
    rcases argument with ⟨block, index⟩
    have bound : index < block.getNumArguments! source.raw := by
      grind [BlockArgumentPtr.InBounds, BlockPtr.getNumArguments!]
    have types := blocks.argumentTypes block
    have targetBound : index < block.getNumArguments! target.raw := by
      have size := congrArg Array.size types
      simp only [BlockPtr.getArgumentTypes!.size_eq_getNumArguments!] at size
      omega
    change (block.getArgument index).getType! target.raw = (block.getArgument index).getType! source.raw
    rw [← BlockPtr.getArgumentTypes!.getElem!_eq_getArgument targetBound,
      ← BlockPtr.getArgumentTypes!.getElem!_eq_getArgument bound, types]

/-- Renaming a root's results leaves the operands of its dominators unchanged. -/
theorem renameRootResults_operands_of_dominates
    {ctx : WfIRContext OpCode} {op root : OperationPtr} {region : RegionPtr} {irRoot : IRNode}
    (ctxDom : ctx.Dom irRoot) (rootRooted : root.RootedAt irRoot ctx)
    (rootRegion : root.getParentRegion! ctx.raw = some region) (ssa : region.hasSSADominance ctx)
    (rootReachable : root.HierarchicallyReachable ctx)
    (dominates : op.Dominates root ctx false) (replacements : Array ValuePtr)
    (arity : replacements.size = root.getNumResults! ctx.raw) :
    (op.getOperands! ctx.raw).map (renameRootResults root replacements.zipIdx.toList) =
      op.getOperands! ctx.raw := by
  have opRooted : op.RootedAt irRoot ctx := by grind
  obtain ⟨opRegion, opParent⟩ := dominates.exists_parentRegion rootRegion
  have opReachable : op.HierarchicallyReachable ctx := by grind
  obtain ⟨reachableRegion, reachable⟩ := opReachable.exists_locallyReachable opParent
  have disjoint := ctxDom.not_mem_results_of_mem_operands_of_dominates
    opRooted reachable rootRegion ssa rootReachable dominates
  calc
    _ = (op.getOperands! ctx.raw).map id := by
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

/-- The actual driver leaves a statically watched producer's operand pointers unchanged. -/
theorem CTree.Pattern.Valid.fromLocalRewrite_dominator_operands
    {rule : Pattern OpCode} (valid : CTree.Pattern.Valid rule)
    {rewriter result : PatternRewriter OpCode} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    {region : RegionPtr} {irRoot : IRNode}
    (ctxDom : rewriter.ctx.Dom irRoot) (rootRooted : root.RootedAt irRoot rewriter.ctx)
    (rootRegion : root.getParentRegion! rewriter.ctx.raw = some region)
    (ssa : region.hasSSADominance rewriter.ctx)
    (rootReachable : root.HierarchicallyReachable rewriter.ctx)
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    {op : OperationPtr} (opIn : op.InBounds rewriter.ctx.raw)
    (dominates : op.ProperlyDominates root rewriter.ctx false) :
    op.getOperands! result.ctx.raw = op.getOperands! rewriter.ctx.raw := by
  have different : op ≠ root := by
    intro equal
    subst op
    exact OperationPtr.not_properlyDominates_self rootRooted rootRegion ssa dominates
  have fields := valid.fromLocalRewrite_existing_frame ctxDom rootRooted rootRegion ssa rootReachable
    localRun run attached regions op opIn different
  have rootHeader := (rule.interpret_preserves_existing_fields localRun root rootIn).1
  have counts : root.getNumResults! created.raw = root.getNumResults! rewriter.ctx.raw := by
    simpa only [OperationPtr.getResultTypes!.size_eq_getNumResults!] using
      congrArg Array.size rootHeader.resultTypes
  exact fields.2.trans (renameRootResults_operands_of_dominates ctxDom rootRooted rootRegion ssa
    rootReachable (Or.inr dominates) replacements ((fromLocalRewrite_result_arity localRun run).trans counts))

end Veir.Puddle
