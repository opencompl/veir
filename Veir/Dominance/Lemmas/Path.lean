module

public import Veir.Dominance.Basic

import all Veir.Dominance.Basic

/-!
# CFG Path and Reachability Lemmas

This file proves lemmas about paths through a region's CFG (`RegionPtr.Path`)
and block reachability (`BlockPtr.ReachableFromEntry`).
-/

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : WfIRContext OpInfo}

/-! ## CFG Path Lemmas -/

namespace RegionPtr.Path

variable {region : RegionPtr} {source middle target block : BlockPtr}
variable {blocks blocks₁ blocks₂ : List BlockPtr}

/-- A path's block list is nonempty. -/
@[simp, grind .]
theorem not_isEmpty (path : region.Path ctx source target blocks) :
    !blocks.isEmpty := by
  cases path <;> grind

/-- A path's block list is not nil. -/
@[simp]
theorem ne_nil (path : region.Path ctx source target blocks) :
    blocks ≠ [] := by
  cases path <;> grind

/-- The first block in a path is its source. -/
@[simp]
theorem head?_eq (path : region.Path ctx source target blocks) :
    blocks.head? = some source := by
  cases path <;> grind

grind_pattern head?_eq => region.Path ctx source target blocks, blocks.head?

/-- The last block in a path is its target. -/
@[simp]
theorem getLast?_eq (path : region.Path ctx source target blocks) :
    blocks.getLast? = some target := by
  induction path <;> grind

grind_pattern getLast?_eq => region.Path ctx source target blocks, blocks.getLast?

/-- The target block belongs to a path's block list. -/
@[grind →]
theorem target_mem (path : region.Path ctx source target blocks) :
    target ∈ blocks := by
  induction path <;> grind

/-- The source block belongs to a path's block list. -/
@[grind →]
theorem source_mem (path : region.Path ctx source target blocks) :
    source ∈ blocks := by
  induction path <;> grind

/-- Every block listed by a path belongs to the path's region. -/
@[grind →]
theorem parent_of_mem (path : region.Path ctx source target blocks)
    (hmem : block ∈ blocks) :
    (block.get! ctx.raw).parent = some region := by
  induction path <;> grind

/-- The source block of a path belongs to the path's region. -/
@[grind →]
theorem source_parent (path : region.Path ctx source target blocks) :
    (source.get! ctx.raw).parent = some region := by
  grind

/-- The target block of a path belongs to the path's region. -/
@[grind →]
theorem target_parent (path : region.Path ctx source target blocks) :
    (target.get! ctx.raw).parent = some region := by
  grind

/-- The source block of a path is in bounds of the path's region. -/
@[grind →]
theorem source_inBounds (path : region.Path ctx source target blocks) :
    source.InBounds ctx.raw := by
  grind [BlockPtr.get!_of_not_inBounds, Block.default_parent_eq]

/-- The target block of a path is in bounds of the path's region. -/
@[grind →]
theorem target_inBounds (path : region.Path ctx source target blocks) :
    target.InBounds ctx.raw := by
  grind [BlockPtr.get!_of_not_inBounds, Block.default_parent_eq]

/-- Every block listed by a path is in bounds of the path's region. -/
@[grind →]
theorem inBounds_of_mem (path : region.Path ctx source target blocks)
    (hmem : block ∈ blocks) :
    block.InBounds ctx.raw := by
  grind [BlockPtr.get!_of_not_inBounds, Block.default_parent_eq]

/-- Every adjacent pair in a path is a CFG successor edge. -/
theorem successor_of_adjacent
    (path : region.Path ctx source target blocks)
    {i : Nat} (h₁ : blocks[i]? = some adjacentSource)
    (h₂ : blocks[i + 1]? = some adjacentTarget) :
    adjacentTarget ∈ adjacentSource.getSuccessors! ctx.raw := by
  induction path generalizing i <;> grind [cases RegionPtr.Path]

/-- Concatenate two paths that meet at `middle`. -/
theorem append
    (left : region.Path ctx source middle blocks₁)
    (right : region.Path ctx middle target blocks₂) :
    region.Path ctx source target (blocks₁ ++ blocks₂.tail) := by
  induction left <;> grind [RegionPtr.Path]

/-- Split a path at any block in its witness list, producing two paths meeting at `block`. -/
theorem split_of_mem
    (path : region.Path ctx source target blocks)
    (hmem : block ∈ blocks) :
    ∃ pre post,
      blocks = pre ++ block :: post ∧
      region.Path ctx source block (pre ++ [block]) ∧
      region.Path ctx block target (block :: post) := by
  induction path with
  | Single parent =>
      exists [], []
      grind [.Single]
  | @Cons source next target blocks parent successor tail ih =>
      simp only [List.mem_cons] at hmem
      rcases hmem with _ | hmem
      · exists [], blocks
        grind [.Single, .Cons]
      · obtain ⟨pre, post, heq, prefixPath, suffixPath⟩ := ih hmem
        exists source :: pre, post
        grind [.Cons]

end RegionPtr.Path

namespace BlockPtr.ReachableFromEntry

variable {region : RegionPtr} {source successorBlock entryBlock : BlockPtr}

/-- Establish reachability from a path beginning at the region's entry block. -/
theorem of_path
    (entryBlock : (region.get! ctx.raw).firstBlock = some entry)
    (path : region.Path ctx entry source blocks) :
    source.ReachableFromEntry region ctx := by
  grind [BlockPtr.ReachableFromEntry]

/-- A reachable block has a witnessing path from the region's entry block. -/
theorem exists_path (reachable : source.ReachableFromEntry region ctx) :
    ∃ entry blocks,
      (region.get! ctx.raw).firstBlock = some entry ∧
      region.Path ctx entry source blocks := by
  grind [BlockPtr.ReachableFromEntry]

/-- A reachable block belongs to the region whose entry reaches it. -/
@[grind →]
theorem parent (reachable : source.ReachableFromEntry region ctx) :
    (source.get! ctx.raw).parent = some region := by
  grind [BlockPtr.ReachableFromEntry]

/-- A region's entry block is reachable from itself. -/
@[grind →]
theorem entry
    (regionInBounds : region.InBounds ctx.raw)
    (hentry : (region.get! ctx.raw).firstBlock = some entryBlock) :
    entryBlock.ReachableFromEntry region ctx := by
  apply of_path hentry
  apply RegionPtr.Path.Single
  grind

/-- Reachability propagates across a CFG successor edge in the region. -/
theorem successor
    {ctx : WfIRContext OpCode}
    (reachable : source.ReachableFromEntry region ctx)
    (hsuccessor : successorBlock ∈ source.getSuccessors! ctx.raw)
    (hsuccParent : (successorBlock.get! ctx.raw).parent = some region) :
    successorBlock.ReachableFromEntry region ctx := by
  obtain ⟨entry, blocks, hentry, path⟩ := reachable.exists_path
  have edgePath : region.Path ctx source successorBlock [source, successorBlock] :=
    .Cons path.target_parent hsuccessor (.Single hsuccParent)
  apply BlockPtr.ReachableFromEntry.of_path hentry (blocks := blocks ++ [successorBlock])
  exact RegionPtr.Path.append path edgePath

end BlockPtr.ReachableFromEntry

end Veir
