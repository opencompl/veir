module

public import Veir.Verifier

/-!
# CFG Paths and Reachability

This file defines a propositional definition of paths through a region's CFG (`RegionPtr.Path`),
and the propositional definition of reachability for blocks inside a region
(`BlockPtr.ReachableFromEntry`).

These two definitions are central to the definition of dominance, as dominance
inside a region is defined in terms of paths from the region's entry block.
-/

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : WfIRContext OpInfo}

/-! ## CFG Paths -/

/--
A nonempty CFG path between two (possibly equal) blocks in `region`.

The path is witnessed by a list of blocks, which is nonempty, and contains the
source and target blocks as its first and last elements, respectively. Every block
in the path has `region` as its parent, and every consecutive pair is related by
a CFG edge.
-/
inductive RegionPtr.Path (region : RegionPtr) (ctx : WfIRContext OpInfo) :
    BlockPtr → BlockPtr → List BlockPtr → Prop where
  | single {block : BlockPtr}
      (parent : (block.get! ctx.raw).parent = some region) :
      region.Path ctx block block [block]
  | cons {source next target : BlockPtr} {blocks : List BlockPtr}
      (parent : (source.get! ctx.raw).parent = some region)
      (successor : next ∈ source.getSuccessors! ctx.raw)
      (tail : region.Path ctx next target blocks) :
      region.Path ctx source target (source :: blocks)

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

end RegionPtr.Path

/-! ## Reachability -/

/-- A block is reachable when an entry-to-block path exists in its region. -/
def BlockPtr.ReachableFromEntry (block : BlockPtr) (region : RegionPtr)
    (ctx : WfIRContext OpInfo) : Prop :=
  ∃ entry blocks,
    (region.get! ctx.raw).firstBlock = some entry ∧
    region.Path ctx entry block blocks

namespace BlockPtr.ReachableFromEntry

variable {region : RegionPtr} {source successorBlock entryBlock : BlockPtr}

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
