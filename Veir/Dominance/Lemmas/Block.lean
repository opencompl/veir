module

public import Veir.Dominance.Lemmas.Path

import all Veir.Dominance.Basic

/-!
# Block Dominance Lemmas

Lemmas connecting region-local proper dominance with ordinary block dominance.
-/

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : WfIRContext OpInfo}

/--
A proper block ancestor of one block is an ancestor of every block in the
same region.
-/
private theorem IRNode.ProperAncestor.block_of_same_region
    {ancestor left right : BlockPtr} {region : RegionPtr}
    (ancestry :
      IRNode.ProperAncestor (.block ancestor) (.block left) ctx)
    (leftParent : (left.get! ctx.raw).parent = some region)
    (rightParent : (right.get! ctx.raw).parent = some region) :
    IRNode.Ancestor (.block ancestor) (.block right) ctx := by
  have leftParent₂ : (IRNode.block left).parent! ctx = some (.region region) := by grind
  have rightParent₂ : (IRNode.block right).parent! ctx = some (.region region) := by grind
  exact Ancestor.of_same_parent_of_properAncestor ancestry leftParent₂ rightParent₂

namespace BlockPtr.ProperlyDominatesInRegion

variable {dominator dominated source predecessor successor : BlockPtr} {region : RegionPtr}

@[grind →]
theorem parent_dominator :
    dominator.ProperlyDominatesInRegion dominated region ctx →
    (dominator.get! ctx.raw).parent = region := by
  rintro (_|_)
  · grind [ProperlyDominatesInSSACFGRegion]
  · grind [ProperlyDominatesInGraphRegion]

@[grind →]
theorem parent_dominated :
    dominator.ProperlyDominatesInRegion dominated region ctx →
    (dominated.get! ctx.raw).parent = region := by
  rintro (_|_)
  · grind [ProperlyDominatesInSSACFGRegion]
  · grind [ProperlyDominatesInGraphRegion]

/--
If a `source` block properly dominates a distinct `target`, then it properly dominates
a distinct predecessor of that successor edge.
-/
private theorem predecessor_of_dominates_successor
    (sourceNeTarget : source ≠ target)
    (successorEdge : successor ∈ target.getSuccessors! ctx.raw)
    (targetParent : (target.get! ctx.raw).parent = some region)
    (sourceDominatesSuccessor : source.ProperlyDominatesInRegion successor region ctx) :
    source.ProperlyDominatesInRegion target region ctx := by
  have sourceParent : (source.get! ctx.raw).parent = some region := by grind
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
    grind [hPath.append (RegionPtr.Path.of_parent successorEdge targetParent (by grind))]

end BlockPtr.ProperlyDominatesInRegion

namespace BlockPtr.Dominates

variable {source predecessor successor : BlockPtr} {region : RegionPtr}

/--
If a distinct block dominates a successor, it also dominates the predecessor
of that successor edge.
-/
theorem predecessor_of_dominates_successor
    (predecessorParent :
      (predecessor.get! ctx.raw).parent = some region)
    (successorParent : (successor.get! ctx.raw).parent = some region)
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

end Veir
