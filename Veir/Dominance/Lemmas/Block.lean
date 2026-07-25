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
  obtain ⟨nodes, path⟩ := ancestry.toAncestor.exists_parentPath
  cases path with
  | single => exact False.elim (ancestry.ne rfl)
  | @cons _ parent nodes immediate tail =>
      cases parent with
      | operation parent => simp [IRNode.parent!] at immediate
      | block parent => simp [IRNode.parent!] at immediate
      | region parentRegion =>
          have recordedParent :
              (left.get! ctx.raw).parent = some parentRegion := by
            simpa [IRNode.parent!] using immediate
          have regionEq : parentRegion = region :=
            Option.some.inj (recordedParent.symm.trans leftParent)
          subst parentRegion
          exact .of_parentPath
            (.cons (by simpa [IRNode.parent!] using rightParent) tail)

namespace BlockPtr.ProperlyDominatesInRegion

variable {source predecessor successor : BlockPtr} {region : RegionPtr}

/--
If a block properly dominates a distinct successor, then it properly dominates
a distinct predecessor of that successor edge.
-/
theorem predecessor_of_dominates_successor
    (predecessorParent :
      (predecessor.get! ctx.raw).parent = some region)
    (sourceNePredecessor : source ≠ predecessor)
    (sourceNeSuccessor : source ≠ successor)
    (successorEdge : successor ∈ predecessor.getSuccessors! ctx.raw)
    (sourceDominatesSuccessor :
      source.ProperlyDominatesInRegion successor region ctx) :
    source.ProperlyDominatesInRegion predecessor region ctx := by
  cases sourceDominatesSuccessor with
  | Graph graphDominance =>
      change
        (source.get! ctx.raw).parent = some region ∧
        (successor.get! ctx.raw).parent = some region ∧
        region.hasSSADominance ctx = false at graphDominance
      apply BlockPtr.ProperlyDominatesInRegion.Graph
      change
        (source.get! ctx.raw).parent = some region ∧
        (predecessor.get! ctx.raw).parent = some region ∧
        region.hasSSADominance ctx = false
      exact ⟨graphDominance.1, predecessorParent, graphDominance.2.2⟩
  | Ssa ssaDominance =>
      change
        (source.get! ctx.raw).parent = some region ∧
        (successor.get! ctx.raw).parent = some region ∧
        region.hasSSADominance ctx = true ∧
        source ≠ successor ∧
        ∀ entry blocks,
          (region.get! ctx.raw).firstBlock = some entry →
          region.Path ctx entry successor blocks →
          source ∈ blocks at ssaDominance
      apply BlockPtr.ProperlyDominatesInRegion.Ssa
      change
        (source.get! ctx.raw).parent = some region ∧
        (predecessor.get! ctx.raw).parent = some region ∧
        region.hasSSADominance ctx = true ∧
        source ≠ predecessor ∧
        ∀ entry blocks,
          (region.get! ctx.raw).firstBlock = some entry →
          region.Path ctx entry predecessor blocks →
          source ∈ blocks
      refine ⟨ssaDominance.1, predecessorParent, ssaDominance.2.2.1,
        sourceNePredecessor, ?_⟩
      intro entry blocks entryBlock predecessorPath
      have edgePath :
          region.Path ctx predecessor successor [predecessor, successor] :=
        .Cons predecessorParent successorEdge (.Single ssaDominance.2.1)
      have sourceMem := ssaDominance.2.2.2.2 entry (blocks ++ [successor])
        entryBlock (predecessorPath.append edgePath)
      simp only [List.mem_append, List.mem_singleton] at sourceMem
      exact sourceMem.resolve_right sourceNeSuccessor

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
  change source = successor ∨
    source.ProperlyDominates successor ctx true at sourceDominatesSuccessor
  change source = predecessor ∨
    source.ProperlyDominates predecessor ctx true
  rcases sourceDominatesSuccessor with sourceEqSuccessor | properDominance
  · exact False.elim (sourceNeSuccessor sourceEqSuccessor)
  · by_cases sourceEqPredecessor : source = predecessor
    · exact Or.inl sourceEqPredecessor
    · right
      cases properDominance with
      | Ancestor ancestry _ _ =>
          exact .Ancestor
            ((IRNode.ProperAncestor.of_ancestor_ne ancestry
              (by simpa using sourceNeSuccessor)).block_of_same_region
                successorParent predecessorParent)
            sourceEqPredecessor rfl
      | AncestorDominatedInRegion ancestor localRegion ancestry localDominance =>
          by_cases ancestorEqSuccessor : ancestor = successor
          · subst ancestor
            have localRegionEq : localRegion = region := by
              cases localDominance with
              | Ssa dominance =>
                  change
                    _ ∧
                    (successor.get! ctx.raw).parent = some localRegion ∧
                    _ at dominance
                  exact Option.some.inj
                    (dominance.2.1.symm.trans successorParent)
              | Graph dominance =>
                  change
                    _ ∧
                    (successor.get! ctx.raw).parent = some localRegion ∧
                    _ at dominance
                  exact Option.some.inj
                    (dominance.2.1.symm.trans successorParent)
            subst localRegion
            exact .AncestorDominatedInRegion predecessor region .refl
              (localDominance.predecessor_of_dominates_successor
                predecessorParent sourceEqPredecessor sourceNeSuccessor
                successorEdge)
          · exact .AncestorDominatedInRegion ancestor localRegion
              ((IRNode.ProperAncestor.of_ancestor_ne ancestry
                (by simpa using ancestorEqSuccessor)).block_of_same_region
                  successorParent predecessorParent)
              localDominance

end BlockPtr.Dominates

end Veir
