module

public import Veir.Interfaces.RegionKindInterfaces

import Veir.Rewriter.InsertPoint
import Veir.IRNesting

/-!
# Dominance Definitions

Core propositional definitions for control-flow paths, reachability, and dominance.

The implementation of dominance in a region is based on CompcertSSA's definition
(https://compcertssa.gitlabpages.inria.fr/html/compcert.midend.Dom.html). It is extended
to support dominance between operations in different regions, following MLIR's informal
definition.
-/

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]

/-!
## CFG paths and block dominance

Block dominance is defined in terms of CFG paths between blocks of the same region.
A CFG path (`RegionPtr.Path`) is a nonempty list of blocks that traverse the CFG edges
inside a region. Dominance (`BlockPtr.Dominates`) is then defined as the property that
every CFG path from the region's entry to a dominated block must contain the dominator
block.
-/

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

/--
Block dominance within the blocks' common region.

`dominator` and `dominated` must both belong to the same region. A block is dominated
when every entry-to-dominated path contains the dominator. In particular, every block
in the region dominates an unreachable dominated block, since there are no such paths.
This definition works for both SSACFG and Graph regions, as valid graph regions contain
at most one block, so block dominance there reduces to reflexivity.
-/
def BlockPtr.Dominates (dominator dominated : BlockPtr)
    (ctx : WfIRContext OpInfo) : Prop :=
  ∃ region,
    (dominator.get! ctx.raw).parent = some region ∧
    (dominated.get! ctx.raw).parent = some region ∧
    ∀ entry blocks,
      (region.get! ctx.raw).firstBlock = some entry →
      region.Path ctx entry dominated blocks →
      dominator ∈ blocks

/-- Strict dominance between blocks. It is defined as dominance plus inequality. -/
def BlockPtr.ProperlyDominates (dominator dominated : BlockPtr)
    (ctx : WfIRContext OpInfo) : Prop :=
  dominator.Dominates dominated ctx ∧ dominator ≠ dominated

/-!
## Operation dominance

Operation dominance depends on the parent region of the operations.
* In graph regions, all operations dominate each other.
* In SSACFG regions, operations in the same block are ordered by their index in the block,
  and operations in different blocks dominate each other according to the dominance of their
  containing blocks.
-/

/--
Lexical dominance between `dominator` and `dominated` in a `block` of an SSACFG `region`.

Operations in the same block are ordered by their index in the block's operation list.
-/
def OperationPtr.DominatesInSSACFGBlock
    (dominator dominated : OperationPtr) (block : BlockPtr) (region : RegionPtr)
    (ctx : WfIRContext OpInfo) : Prop :=
  ∃ dominatorParent : (dominator.get! ctx.raw).parent = some block,
  ∃ dominatedParent : (dominated.get! ctx.raw).parent = some block,
  (block.get! ctx.raw).parent = some region ∧
  region.hasSSADominance ctx = true ∧
  dominator.idxInParent ctx.raw ≤ dominated.idxInParent ctx.raw

/--
Dominance between `dominator` and `dominated` directly contained in an SSACFG `region`.

`dominator` dominates `dominated` in the region if either:
* they are in the same block, and `dominator` dominates `dominated` in that block, or
* the block of `dominator` properly dominates the block of `dominated` in the region
  (meaning they are in different blocks).
-/
inductive OperationPtr.DominatesInSSACFGRegion
    (dominator dominated : OperationPtr) (region : RegionPtr)
    (ctx : WfIRContext OpInfo) : Prop where
  | block {block : BlockPtr}
      (dominance : dominator.DominatesInSSACFGBlock dominated block region ctx) :
      DominatesInSSACFGRegion dominator dominated region ctx
  | blocks {dominatorBlock dominatedBlock : BlockPtr}
      (dominatorParent : (dominator.get! ctx.raw).parent = some dominatorBlock)
      (dominatedParent : (dominated.get! ctx.raw).parent = some dominatedBlock)
      (dominatorRegion : dominator.getParentRegion! ctx.raw = some region)
      (dominatedRegion : dominated.getParentRegion! ctx.raw = some region)
      (regionSSA : region.hasSSADominance ctx = true)
      (blockDominance : dominatorBlock.ProperlyDominates dominatedBlock ctx) :
      DominatesInSSACFGRegion dominator dominated region ctx

/--
`dominator` dominates `dominated` in a graph `region`.

All operations in a graph region dominate each other, so this is simply the property
that both operations are directly contained in the same graph region.
-/
def OperationPtr.DominatesInGraphRegion (dominator dominated : OperationPtr)
    (region : RegionPtr) (ctx : WfIRContext OpInfo) : Prop :=
  dominator.getParentRegion! ctx.raw = some region ∧
  dominated.getParentRegion! ctx.raw = some region ∧
  region.hasSSADominance ctx = false

/--
`dominator` dominates `dominated` in `region`.

This is true if either:
* `region` is an SSACFG region, and `dominator` dominates `dominated` in that region, or
* `region` is a graph region, and both operations are directly contained in that region.
-/
inductive OperationPtr.DominatesInRegion (dominator dominated : OperationPtr)
    (region : RegionPtr) (ctx : WfIRContext OpInfo) : Prop where
  | ssa (dominance : dominator.DominatesInSSACFGRegion dominated region ctx) :
      DominatesInRegion dominator dominated region ctx
  | graph (dominance : dominator.DominatesInGraphRegion dominated region ctx) :
      DominatesInRegion dominator dominated region ctx

/--
`dominator` dominates `dominated`.

This is true if either:
* `dominator` and `dominated` are the same operation, or
* there exists a region and an ancestor operation of `dominated` such that
  `dominator` dominates the ancestor operation in that region.

Note that this definition has a special case for `dominator = dominated`, which is necessary
for the case where the operation has no parent region.
-/
def OperationPtr.Dominates (dominator dominated : OperationPtr)
    (ctx : WfIRContext OpInfo) : Prop :=
  dominator = dominated ∨
  ∃ region ancestor,
    (IRNode.operation ancestor).Ancestor (.operation dominated) ctx ∧
    dominator.DominatesInRegion ancestor region ctx

/-- Strict dominance between operations. It is defined as dominance plus inequality. -/
def OperationPtr.ProperlyDominates (dominator dominated : OperationPtr)
    (ctx : WfIRContext OpInfo) : Prop :=
  dominator ≠ dominated ∧
  OperationPtr.Dominates dominator dominated ctx

end Veir
