module

public import Veir.Dominance.Basic

/-!
# CFG Path and Reachability Lemmas

This file proves lemmas about paths through a region's CFG (`RegionPtr.Path`)
and block reachability (`BlockPtr.ReachableFromEntry`). Their definitions live
in `Veir.Dominance.Basic`.

These two definitions are central to the definition of dominance, as dominance
inside a region is defined in terms of paths from the region's entry block.
-/

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : WfIRContext OpInfo}

namespace RegionPtr.Path

variable {region : RegionPtr} {source middle target block : BlockPtr}
variable {blocks blocks₁ blocks₂ : List BlockPtr}

/-- A path's block list is nonempty. -/
@[simp]
theorem not_isEmpty (path : region.Path ctx source target blocks) :
    !blocks.isEmpty := by
  cases path <;> simp

/-- A path's block list is not nil. -/
@[simp]
theorem ne_nil (path : region.Path ctx source target blocks) :
    blocks ≠ [] := by
  cases path <;> simp

/-- The first block in a path is its source. -/
@[simp]
theorem head?_eq (path : region.Path ctx source target blocks) :
    blocks.head? = some source := by
  cases path <;> rfl

/-- The last block in a path is its target. -/
@[simp]
theorem getLast?_eq (path : region.Path ctx source target blocks) :
    blocks.getLast? = some target := by
  induction path <;> grind

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
  cases path <;> grind

/-- The target block of a path belongs to the path's region. -/
@[grind →]
theorem target_parent (path : region.Path ctx source target blocks) :
    (target.get! ctx.raw).parent = some region := by
  induction path <;> grind

/-- Every adjacent pair in a path is a CFG successor edge. -/
theorem successor_of_adjacent
    (path : region.Path ctx source target blocks)
    (heq : blocks = pre ++ adjacentSource :: adjacentTarget :: post) :
    adjacentTarget ∈ adjacentSource.getSuccessors! ctx.raw := by
  induction path generalizing pre with
  | single => cases pre <;> simp_all
  | cons _ _ tail _ =>
    cases pre <;> grind [tail.head?_eq]

/-- Concatenate two paths that meet at `middle`. -/
theorem append
    (left : region.Path ctx source middle blocks₁)
    (right : region.Path ctx middle target blocks₂) :
    region.Path ctx source target (blocks₁ ++ blocks₂.tail) := by
  induction left with
  | single =>
    cases right with
    | single parent => exact .single parent
    | cons parent successor tail => exact .cons parent successor tail
  | cons parent successor tail ih =>
    exact RegionPtr.Path.cons parent successor (ih right)

/-- Split a path at any block in its witness list, producing two paths meeting at `block`. -/
theorem split_of_mem
    (path : region.Path ctx source target blocks)
    (hmem : block ∈ blocks) :
    ∃ pre post,
      blocks = pre ++ block :: post ∧
      region.Path ctx source block (pre ++ [block]) ∧
      region.Path ctx block target (block :: post) := by
  induction path with
  | single parent =>
      exists [], []
      grind [.single]
  | @cons source next target blocks parent successor tail ih =>
      simp only [List.mem_cons] at hmem
      rcases hmem with _ | hmem
      · exists [], blocks
        grind [.single, .cons]
      · obtain ⟨pre, post, heq, prefixPath, suffixPath⟩ := ih hmem
        exists source :: pre, post
        grind [.cons]

/-- Extract the path prefix ending at a listed block. -/
theorem prefix_of_mem
    (path : region.Path ctx source target blocks)
    (hmem : block ∈ blocks) :
    ∃ pre post,
      blocks = pre ++ block :: post ∧
      region.Path ctx source block (pre ++ [block]) := by
  grind [path.split_of_mem hmem]

/-- Extract the path suffix starting at a listed block. -/
theorem suffix_of_mem
    (path : region.Path ctx source target blocks)
    (hmem : block ∈ blocks) :
    ∃ pre post,
      blocks = pre ++ block :: post ∧
      region.Path ctx block target (block :: post) := by
  grind [path.split_of_mem hmem]

/-- Shorten a path at its first occurrence of the target block. -/
theorem truncate_at_first_target
    (path : region.Path ctx source target blocks) :
    ∃ pathPrefix,
      region.Path ctx source target (pathPrefix ++ [target]) ∧
      target ∉ pathPrefix := by
  induction path
  case single parent =>
    grind [RegionPtr.Path.single parent]
  case cons source next target blocks parent successor tail ih =>
    by_cases targetEq : source = target
    · exists []
      grind [RegionPtr.Path.single]
    · obtain ⟨pathPrefix, shortened, targetNotMem⟩ := ih
      exists source :: pathPrefix
      grind [RegionPtr.Path.cons]

/--
If `target` occurs before the final `avoided` block on a path whose prefix does
not contain `avoided`, extract an entry-to-target path avoiding `avoided`.
-/
theorem prefix_avoiding_last_of_not_mem
    (path : region.Path ctx source avoided blocks)
    (blocksEq : blocks = pathPrefix ++ [avoided])
    (avoidedNotMem : avoided ∉ pathPrefix)
    (targetMem : target ∈ pathPrefix) :
    ∃ targetBlocks,
      region.Path ctx source target targetBlocks ∧
      avoided ∉ targetBlocks := by
  induction path generalizing pathPrefix
  case single parent =>
    grind [List.self_eq_append_left]
  case cons source next avoided blocks parent successor tail ih =>
    cases pathPrefix
    case nil => grind
    case cons head rest =>
      simp only [List.cons_append, List.cons.injEq] at blocksEq
      obtain ⟨rfl, headEq⟩ := blocksEq
      simp only [List.mem_cons, not_or] at avoidedNotMem
      simp only [List.mem_cons] at targetMem
      rcases targetMem with rfl | targetMem
      · exists [target]
        grind [.single]
      · have ⟨targetBlocks, targetPath, avoidedNotTargetBlocks⟩ :=
          ih headEq (by grind) (by grind)
        exists source :: targetBlocks
        grind [.cons]

end RegionPtr.Path

namespace BlockPtr.ReachableFromEntry

variable {region : RegionPtr} {source successorBlock entryBlock : BlockPtr}

/-- Establish reachability from a path beginning at the region's entry block. -/
theorem of_path
    (entryBlock : (region.get! ctx.raw).firstBlock = some entry)
    (path : region.Path ctx entry source blocks) :
    source.ReachableFromEntry region ctx := by
  grind [ReachableFromEntry]

/-- A reachable block has a witnessing path from the region's entry block. -/
theorem exists_path (reachable : source.ReachableFromEntry region ctx) :
    ∃ entry blocks,
      (region.get! ctx.raw).firstBlock = some entry ∧
      region.Path ctx entry source blocks := by
  grind [ReachableFromEntry]

/-- A reachable block belongs to the region whose entry reaches it. -/
@[grind →]
theorem parent (reachable : source.ReachableFromEntry region ctx) :
    (source.get! ctx.raw).parent = some region := by
  grind [ReachableFromEntry]

/-- A region's entry block is reachable from itself. -/
@[grind →]
theorem entry
    (regionInBounds : region.InBounds ctx.raw)
    (hentry : (region.get! ctx.raw).firstBlock = some entryBlock) :
    entryBlock.ReachableFromEntry region ctx := by
  exists entryBlock, [entryBlock]
  grind [RegionPtr.Path.single]

/-- Reachability propagates across a verified CFG successor edge. -/
theorem successor
    {ctx : WfIRContext OpCode}
    (reachable : source.ReachableFromEntry region ctx)
    (ctxVerified : ctx.Verified)
    (hsuccessor : successorBlock ∈ source.getSuccessors! ctx.raw) :
    successorBlock.ReachableFromEntry region ctx := by
  obtain ⟨entry, blocks, hentry, path⟩ := reachable
  have sourceIn : source.InBounds ctx.raw := by
    grind [BlockPtr.get!_of_not_inBounds, Block.default_parent_eq]
  have successorParent :=
    ctxVerified.successor_parent sourceIn path.target_parent hsuccessor
  have edgePath : region.Path ctx source successorBlock [source, successorBlock] :=
    .cons path.target_parent hsuccessor (.single successorParent)
  exists entry, blocks ++ [successorBlock]
  grind [path.append edgePath]

end BlockPtr.ReachableFromEntry

end Veir
