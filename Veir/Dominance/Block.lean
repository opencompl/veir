module

public import Veir.Dominance.Path

/-!
# Block Dominance Lemmas

This file proves lemmas about block dominance inside a region. The definition
lives in `Veir.Dominance.Basic`.

Dominance is defined as the following:
* Block `a` dominates block `b` if `a` is on every path from the region's entry block to `b`.
  In particular, if `b` is unreachable, then every block dominates `b`.
* The same definition applies to graph regions. Valid graph regions contain at most one block,
  so block dominance there reduces to reflexivity.
-/

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : WfIRContext OpInfo}

namespace BlockPtr.Dominates

variable {source middle target : BlockPtr} {region : RegionPtr}

/-- Establish dominance from common parents and path membership. -/
theorem of_mem_of_path
    (sourceParent : (source.get! ctx.raw).parent = some region)
    (targetParent : (target.get! ctx.raw).parent = some region)
    (entryBlock : (region.get! ctx.raw).firstBlock = some entry)
    (sourceMem : ∀ blocks,
      region.Path ctx entry target blocks →
      source ∈ blocks) :
    source.Dominates target ctx := by
  grind [Dominates]

/-- Dominating blocks are attached to a common region. -/
theorem parents (dominates : source.Dominates target ctx) :
    ∃ region,
      (source.get! ctx.raw).parent = some region ∧
      (target.get! ctx.raw).parent = some region := by
  grind [Dominates]

/-- Dominating blocks have the same parent. -/
@[grind →]
theorem parent_eq (dominates : source.Dominates target ctx) :
    (source.get! ctx.raw).parent = (target.get! ctx.raw).parent := by
  grind [Dominates]

/-- A dominator occurs on every entry-to-target path. -/
theorem mem_of_path
    (dominates : source.Dominates target ctx)
    (entryBlock : (region.get! ctx.raw).firstBlock = some entry)
    (path : region.Path ctx entry target blocks) :
    source ∈ blocks := by
  grind [Dominates]

/-- Block dominance is reflexive for a block attached to a region. -/
@[grind .]
theorem refl
    (sourceParent : (source.get! ctx.raw).parent = some region) :
    source.Dominates source ctx := by
  grind [Dominates]

/-- Block dominance is transitive. -/
theorem trans
    (sourceMiddle : source.Dominates middle ctx)
    (middleTarget : middle.Dominates target ctx) :
    source.Dominates target ctx := by
  have ⟨leftRegion, sourceParent, middleParent⟩ := sourceMiddle.parents
  have ⟨rightRegion, middleParent', targetParent⟩ := middleTarget.parents
  obtain rfl : leftRegion = rightRegion := by grind
  have ⟨entry, entryBlock⟩ :=
    ctx.wellFormed.exists_entry_of_parent sourceParent
  apply of_mem_of_path sourceParent targetParent entryBlock
  intro blocks path
  have middleMem := mem_of_path middleTarget entryBlock path
  have ⟨pre, post, blocksEq, prefixPath⟩ := path.prefix_of_mem middleMem
  grind [mem_of_path sourceMiddle entryBlock prefixPath]

/-- Every block in a region dominates an unreachable target in that region. -/
theorem of_target_unreachable
    (sourceParent : (source.get! ctx.raw).parent = some region)
    (targetParent : (target.get! ctx.raw).parent = some region)
    (targetUnreachable : ¬ target.ReachableFromEntry region ctx) :
    source.Dominates target ctx := by
  grind [BlockPtr.ReachableFromEntry.of_path, of_mem_of_path, ctx.wellFormed.exists_entry_of_parent]

/-- An unreachable source cannot dominate a reachable target. -/
theorem not_of_source_unreachable_of_target_reachable
    (sourceUnreachable : ¬ source.ReachableFromEntry region ctx)
    (targetReachable : target.ReachableFromEntry region ctx) :
    ¬ source.Dominates target ctx := by
  intro dominates
  have ⟨entry, blocks, entryBlock, path⟩ := targetReachable.exists_path
  have sourceMem := mem_of_path dominates entryBlock path
  grind [BlockPtr.ReachableFromEntry.of_path, path.prefix_of_mem]

/-- Dominance is antisymmetric for reachable blocks. -/
theorem antisymm_of_reachable
    (sourceReachable : source.ReachableFromEntry region ctx)
    (sourceTarget : source.Dominates target ctx)
    (targetSource : target.Dominates source ctx) :
    source = target := by
  obtain ⟨entry, blocks, entryBlock, path⟩ := sourceReachable.exists_path
  obtain ⟨pathPrefix, shortened, sourceNotMem⟩ :=
    path.truncate_at_first_target
  have targetMem := targetSource.mem_of_path entryBlock shortened
  simp only [List.mem_append, List.mem_singleton] at targetMem
  rcases targetMem with targetMem | targetEq
  · obtain ⟨targetBlocks, targetPath, sourceNotMemTarget⟩ :=
      shortened.prefix_avoiding_last_of_not_mem rfl sourceNotMem targetMem
    exact False.elim
      (sourceNotMemTarget (sourceTarget.mem_of_path entryBlock targetPath))
  · exact targetEq.symm

/--
If a distinct block dominates a successor, it also dominates the predecessor
of that successor edge.
-/
theorem predecessor_of_dominates_successor
    (sourceParent : (source.get! ctx.raw).parent = some region)
    (predecessorParent : (middle.get! ctx.raw).parent = some region)
    (successorParent : (target.get! ctx.raw).parent = some region)
    (sourceNeSuccessor : source ≠ target)
    (successorEdge : target ∈ middle.getSuccessors! ctx.raw)
    (sourceDominatesSuccessor : source.Dominates target ctx) :
    source.Dominates middle ctx := by
  have ⟨entry, hentry⟩ :=
    ctx.wellFormed.exists_entry_of_parent sourceParent
  apply of_mem_of_path sourceParent predecessorParent hentry
  intro blocks predecessorPath
  have edgePath : region.Path ctx middle target [middle, target] :=
    by grind [RegionPtr.Path]
  grind [mem_of_path sourceDominatesSuccessor hentry (predecessorPath.append edgePath)]

end BlockPtr.Dominates

end Veir
