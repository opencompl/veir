module

public import Veir.Dominance.Lemmas.Path
public import Veir.Interfaces.RegionKindInterfaces

import all Veir.Dominance.Basic

/-!
# Block Dominance Lemmas

Lemmas about block dominance, block reachability, and dominance at block entries and exits.
-/

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : WfIRContext OpInfo}

namespace BlockPtr.ProperlyDominatesInRegion

variable {dominator dominated source predecessor successor : BlockPtr} {region : RegionPtr}

@[grind →]
theorem parent_dominator :
    dominator.ProperlyDominatesInRegion dominated region ctx →
    dominator.getParent! ctx.raw = region := by
  rintro (_|_)
  · grind [ProperlyDominatesInSSACFGRegion]
  · grind [ProperlyDominatesInGraphRegion]

@[grind →]
theorem parent_dominated :
    dominator.ProperlyDominatesInRegion dominated region ctx →
    dominated.getParent! ctx.raw = region := by
  rintro (_|_)
  · grind [ProperlyDominatesInSSACFGRegion]
  · grind [ProperlyDominatesInGraphRegion]

/--
If a `source` block properly dominates a distinct `target`, then it properly dominates
a distinct predecessor of that successor edge.
-/
theorem predecessor_of_dominates_successor
    (sourceNeTarget : source ≠ target)
    (successorEdge : successor ∈ target.getSuccessors! ctx.raw)
    (targetParent : target.getParent! ctx.raw = some region)
    (sourceDominatesSuccessor : source.ProperlyDominatesInRegion successor region ctx) :
    source.ProperlyDominatesInRegion target region ctx := by
  have sourceParent : source.getParent! ctx.raw = some region := by grind
  cases sourceDominatesSuccessor with
  | Graph graphDominance =>
    apply Graph
    grind [ProperlyDominatesInGraphRegion]
  | Ssa ssaDominance =>
    apply Ssa
    obtain ⟨_, _, _, _, h⟩ := ssaDominance
    unfold ProperlyDominatesInSSACFGRegion
    refine ⟨by grind, by grind, by grind [ProperlyDominatesInSSACFGRegion], by grind, ?_⟩
    intro entry blocks hfirstBlock hPath
    grind [hPath.append (RegionPtr.Path.of_successor successorEdge targetParent (by grind))]

end BlockPtr.ProperlyDominatesInRegion

namespace BlockPtr.Dominates

variable {source predecessor successor : BlockPtr} {region : RegionPtr}

/--
If a distinct block dominates a successor, it also dominates the predecessor
of that successor edge.
-/
theorem predecessor_of_dominates_successor
    (predecessorParent :
      predecessor.getParent! ctx.raw = some region)
    (successorParent : successor.getParent! ctx.raw = some region)
    (sourceNeSuccessor : source ≠ successor)
    (successorEdge : successor ∈ predecessor.getSuccessors! ctx.raw)
    (sourceDominatesSuccessor : source.Dominates successor ctx) :
    source.Dominates predecessor ctx := by
  unfold Dominates at sourceDominatesSuccessor ⊢
  rcases sourceDominatesSuccessor with (heq|sourceDominatesSuccessor); grind
  by_cases source = predecessor; grind
  right
  cases sourceDominatesSuccessor with
  | Ancestor ancestry _ =>
    apply ProperlyDominates.Ancestor (hNe := by grind)
    have properAncestry := ancestry.proper_of_ne (by simpa)
    exact IRNode.Ancestor.of_same_parent_of_properAncestor properAncestry
      (parent := .region region) (by grind) (by grind)
  | AncestorDominatedInRegion ancestor localRegion ancestry localDominance =>
    by_cases ancestor = successor
    · subst ancestor
      apply ProperlyDominates.AncestorDominatedInRegion predecessor region .refl
      grind [ProperlyDominatesInRegion.predecessor_of_dominates_successor]
    · have properAncestry := ancestry.proper_of_ne (by grind)
      apply ProperlyDominates.AncestorDominatedInRegion ancestor (h := localDominance)
      exact IRNode.Ancestor.of_same_parent_of_properAncestor (parent := .region region)
        properAncestry (by grind) (by grind)

end BlockPtr.Dominates

/-! ## Block reachability -/

variable {region : RegionPtr} {block succ : BlockPtr} {op : OperationPtr}
variable {root : IRNode} {value : ValuePtr}

/-- A hierarchically reachable block is locally reachable in some parent region. -/
@[grind .]
axiom BlockPtr.HierarchicallyReachable.exists_locallyReachable {block : BlockPtr} :
  block.HierarchicallyReachable ctx →
  block.getParent! ctx.raw = some region →
  ∃ region, block.LocallyReachable region ctx

/-- A locally reachable block in the same region as a hierarchically reachable block
is hierarchically reachable, since their enclosing blocks coincide. -/
axiom BlockPtr.HierarchicallyReachable.of_same_region {source target : BlockPtr}
    (reachable : target.HierarchicallyReachable ctx)
    (localReachable : source.LocallyReachable region ctx)
    (targetParent : target.getParent! ctx.raw = some region) :
    source.HierarchicallyReachable ctx

/-! ## Dominance at block insertion points -/

/-- In an SSA region, a value dominating a successor block's entry dominates the
predecessor's exit or is an argument of the successor. -/
axiom ValuePtr.DominatesIp.predecessor_exit_of_successor_entry {value : ValuePtr}
    (blockParent : block.getParent! ctx.raw = some region)
    (succParent : succ.getParent! ctx.raw = some region)
    (regionSSA : region.hasSSADominance ctx)
    (hsucc : succ ∈ block.getSuccessors! ctx.raw) :
    value.DominatesIp (InsertPoint.atStart! succ ctx.raw) ctx →
    value.DominatesIp (.atEnd block) ctx ∨ value ∈ succ.getArguments! ctx.raw

/-- In an SSA region, an operation dominating a successor block's entry also dominates
the predecessor's exit. No CFG reachability is required. -/
axiom OperationPtr.DominatesIp.predecessor_exit_of_successor_entry
    (blockParent : block.getParent! ctx.raw = some region)
    (succParent : succ.getParent! ctx.raw = some region)
    (regionSSA : region.hasSSADominance ctx)
    (hsucc : succ ∈ block.getSuccessors! ctx.raw) :
    op.DominatesIp (InsertPoint.atStart! succ ctx.raw) ctx →
    op.DominatesIp (.atEnd block) ctx

/-- An argument of an in-bounds block dominates the entry of that block. -/
axiom BlockPtr.argument_dominatesIp_atStart
    (blockInBounds : block.InBounds ctx.raw)
    (hMem : value ∈ block.getArguments! ctx.raw) :
    value.DominatesIp (InsertPoint.atStart! block ctx.raw) ctx
/-- An argument of a rooted, locally reachable block in an SSA region cannot dominate
the point before an operation that dominates the block entry. Reachability in enclosing
regions is not required. -/
@[grind →]
axiom BlockPtr.argument_not_dominatesIp_before_of_dominatesIp_atStart
    (regionSSA : region.hasSSADominance ctx)
    (blockRooted : block.RootedAt root ctx)
    (blockReachable : block.LocallyReachable region ctx)
    (opDom : op.DominatesIp (InsertPoint.atStart! block ctx.raw) ctx)
    (hMem : value ∈ block.getArguments! ctx.raw) :
    ¬ value.DominatesIp (.before op) ctx

end Veir
