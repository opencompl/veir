module

public import Veir.Interpreter.Refinement.Basic
public import Veir.Dominance.Lemmas.Block
public import Veir.Dominance.Lemmas.Operation
import all Veir.Interpreter.Refinement.Basic
import all Veir.Rewriter.InsertPoint
import all Veir.IR.Basic

namespace Veir
public section
variable {OpInfo : Type} [HasOpInfo OpInfo]

/-- The post-operation refinement point is precisely the next operation's entry. -/
theorem ValuePtr.inScopeAt_after_iff_before_next {ctx : WfIRContext OpInfo}
    {op next : OperationPtr} {block : BlockPtr} {value : ValuePtr}
    (parent : op.getParent! ctx.raw = some block) (opIn : op.InBounds ctx.raw)
    (nextEq : op.getNextOp! ctx.raw = some next) :
    value.InScopeAt (.at (.after op ctx.raw block parent opIn)) ctx ↔
      value.InScopeAt (.at (.before next)) ctx := by
  rw [InsertPoint.after_eq_of_some_next nextEq]

/-- Only the operation's freshly installed result slots can enter scope on a straight-line step. -/
theorem ValuePtr.inScopeAt_before_of_before_next {ctx : WfIRContext OpInfo}
    {op next : OperationPtr} {block : BlockPtr} {value : ValuePtr}
    (parent : op.getParent! ctx.raw = some block) (opIn : op.InBounds ctx.raw)
    (blockParent : block.getParent! ctx.raw = some region)
    (nextEq : op.getNextOp! ctx.raw = some next)
    (live : value.InScopeAt (.at (.before next)) ctx)
    (notResult : value ∉ op.getResults! ctx.raw) :
    value.InScopeAt (.at (.before op)) ctx := by
  have after := (ValuePtr.inScopeAt_after_iff_before_next parent opIn nextEq).mpr live
  exact (ValuePtr.DominatesIp.after_iff blockParent).mp after |>.resolve_right notResult

/-- Installing a block's arguments adds exactly those argument slots to its entry scope. -/
theorem ValuePtr.inScopeAt_blockEntry_of_before_first {ctx : WfIRContext OpInfo}
    {block : BlockPtr} {first : OperationPtr} {value : ValuePtr}
    (firstEq : block.getFirstOp! ctx.raw = some first)
    (live : value.InScopeAt (.at (.before first)) ctx)
    (notArgument : value ∉ block.getArguments! ctx.raw) :
    value.InScopeAt (.blockEntry block) ctx := by
  exact ⟨by simpa [InsertPoint.atStart!_eq, firstEq] using live, notArgument⟩

/-- A branch transports all nonincoming SSA slots backwards from its successor's block-entry
scope. Branch terminators have no result slots of their own. -/
theorem ValuePtr.inScopeAt_before_terminator_of_successor_entry {ctx : WfIRContext OpInfo}
    {term : OperationPtr} {block dest : BlockPtr} {value : ValuePtr}
    (parent : term.getParent! ctx.raw = some block) (termIn : term.InBounds ctx.raw)
    (last : block.getLastOp! ctx.raw = some term)
    (blockParent : block.getParent! ctx.raw = some region)
    (destParent : dest.getParent! ctx.raw = some region)
    (regionSSA : region.hasSSADominance ctx)
    (edge : dest ∈ term.getSuccessors! ctx.raw)
    (noResults : term.getNumResults! ctx.raw = 0)
    (live : value.InScopeAt (.blockEntry dest) ctx) :
    value.InScopeAt (.at (.before term)) ctx := by
  obtain ⟨entryLive, notArguments⟩ := live
  have blockEdge : dest ∈ block.getSuccessors! ctx.raw := by
    simpa [BlockPtr.getSuccessors!, last] using edge
  have exitLive := (ValuePtr.DominatesIp.predecessor_exit_of_successor_entry
    blockParent destParent regionSSA blockEdge entryLive).resolve_right notArguments
  have nextEq : term.getNextOp! ctx.raw = none := by grind
  have afterLive : value.DominatesIp (.after term ctx.raw block parent termIn) ctx := by
    rwa [InsertPoint.after_eq_atEnd_iff.mpr nextEq]
  have notResults : value ∉ term.getResults! ctx.raw := by
    intro member
    obtain ⟨index, bound, _⟩ := OperationPtr.getResults!.mem_iff_exists_index.mp member
    omega
  exact (ValuePtr.DominatesIp.after_iff blockParent).mp afterLive |>.resolve_right notResults

end
end Veir
