module

import Veir.Interfaces.RegionKindInterfaces
public import Veir.IR.OpInfo
public import Veir.IRNesting

import Veir.IR.InBounds

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
## CFG Paths and Block Dominance

Block dominance is defined in terms of CFG paths between blocks of the same region.
A CFG path (`RegionPtr.Path`) is a nonempty list of blocks that traverse the CFG edges
inside a region.

From the definition of CFG paths, we define a dominance relation between blocks in a region
(`BlockPtr.ProperlyDominatesInRegion`). In SSACFG regions, a block `A` properly dominates a block
`B` (`BlockPtr.ProperlyDominatesInSSACFGRegion`) if every CFG path from the region's entry block to
`B` contains `A`. In graph regions, all blocks properly dominate
(`BlockPtr.ProperlyDominatesInGraphRegion`) each others. Proper dominance
(`BlockPtr.ProperlyDominates`) is then defined as the
property that every CFG path from the region's entry to a dominated block must contain the
(distinct) dominator block.

Proper dominance (`BlockPtr.ProperlyDominates`) in a region is then extended across regions by
considering ancestors of the dominated block. If an ancestor of the dominated block is properly
dominated in a region by the dominator block, then the dominator block properly dominates the
dominated block. Optionally, a flag can allow the dominator block to be an ancestor of the dominated
block.

Dominance is then defined as the reflexive closure of proper dominance, allowing a block to dominate
itself.
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
  | Single {block : BlockPtr}
      (parent : (block.get! ctx.raw).parent = some region) :
      region.Path ctx block block [block]
  | Cons {source next target : BlockPtr} {blocks : List BlockPtr}
      (parent : (source.get! ctx.raw).parent = some region)
      (successor : next ∈ source.getSuccessors! ctx.raw)
      (tail : region.Path ctx next target blocks) :
      region.Path ctx source target (source :: blocks)

/--
Proper dominance between `dominator` and `dominated` in a graph `region`.

This is defined as the property that both blocks are in the same region, and that the region is a
graph region. In practice, if the context is verified, this means that both blocks are also equal.
-/
def BlockPtr.ProperlyDominatesInGraphRegion (dominator dominated : BlockPtr) (region : RegionPtr)
    (ctx : WfIRContext OpInfo) : Prop :=
  (dominator.get! ctx.raw).parent = some region ∧
  (dominated.get! ctx.raw).parent = some region ∧
  region.hasSSADominance ctx = false

/--
Proper dominance between `dominator` and `dominated` in an SSACFG `region`.

This is defined as the property that both blocks are in the same region, the region is an SSACFG
region, and that every CFG path from the region's entry block to the dominated block contains the
dominator block.

In particular, unreachable blocks in the region are considered to be dominated by all other blocks
in the region, since there are no CFG paths from the entry block to the unreachable block.
-/
def BlockPtr.ProperlyDominatesInSSACFGRegion (dominator dominated : BlockPtr) (region : RegionPtr)
    (ctx : WfIRContext OpInfo) : Prop :=
  (dominator.get! ctx.raw).parent = some region ∧
  (dominated.get! ctx.raw).parent = some region ∧
  region.hasSSADominance ctx = true ∧
  dominator ≠ dominated ∧
  ∀ entry blocks,
    (region.get! ctx.raw).firstBlock = some entry →
    region.Path ctx entry dominated blocks →
    dominator ∈ blocks

/--
Proper dominance between `dominator` and `dominated` in `region`.

It is the combination of `BlockPtr.ProperlyDominatesInSSACFGRegion` and
`BlockPtr.ProperlyDominatesInGraphRegion`.
-/
inductive BlockPtr.ProperlyDominatesInRegion (dominator dominated : BlockPtr) (region : RegionPtr)
    (ctx : WfIRContext OpInfo) : Prop where
  | Ssa (dominance : dominator.ProperlyDominatesInSSACFGRegion dominated region ctx)
  | Graph (dominance : dominator.ProperlyDominatesInGraphRegion dominated region ctx)

/--
Proper dominance between `dominator` and `dominated` across regions, optionally allowing
the `dominator` block to be an ancestor of the `dominated` block depending on the boolean flag
`enclosingOk`.

This property is defined as the union of the following two cases:
* The `dominator` block is an ancestor of the `dominated` block, and the boolean flag `enclosingOk`
  is true.
* There exists an ancestor of the `dominated` block that is properly dominated by the `dominator`
  block in a region.
-/
inductive BlockPtr.ProperlyDominates (dominator dominated : BlockPtr) (ctx : WfIRContext OpInfo)
    : (enclosingOk : Bool) → Prop where
  | Ancestor
      (ancestor : (IRNode.block dominator).Ancestor (.block dominated) ctx)
      (hNe : dominator ≠ dominated)
      : ProperlyDominates dominator dominated ctx true
  | AncestorDominatedInRegion (ancestor : BlockPtr) (region : RegionPtr)
      (hAncestor : (IRNode.block ancestor).Ancestor (.block dominated) ctx)
      (h : dominator.ProperlyDominatesInRegion ancestor region ctx)
      (enclosingOk : Bool)
      : ProperlyDominates dominator dominated ctx enclosingOk

/--
Dominance relation between `dominator` and `dominated` across regions.
It is defined as the reflexive closure of `BlockPtr.ProperlyDominates`.
-/
def BlockPtr.Dominates (dominator dominated : BlockPtr) (ctx : WfIRContext OpInfo) : Prop :=
  dominator = dominated ∨ dominator.ProperlyDominates dominated ctx true

/-!
## Operation Dominance

Operation dominance is mostly defined in terms of block dominance.
We first define the notion of proper dominance in a block (`OperationPtr.ProperlyDominatesInBlock`),
which we extend to dominance in a region (`OperationPtr.ProperlyDominatesInRegion`) and finally
across regions (`OperationPtr.ProperlyDominates`). Dominance is then defined as the reflexive
closure of proper dominance, allowing all operations to dominate themselves.
-/

/--
Proper dominance between `dominator` and `dominated` in a `block` of an SSACFG `region`.

Operations in the same block are ordered by their index in the block's operation list.
-/
def OperationPtr.ProperlyDominatesInSSACFGBlock
    (dominator dominated : OperationPtr) (block : BlockPtr) (region : RegionPtr)
    (ctx : WfIRContext OpInfo) : Prop :=
  ∃ dominatorParent : (dominator.get! ctx.raw).parent = some block,
  ∃ dominatedParent : (dominated.get! ctx.raw).parent = some block,
  (block.get! ctx.raw).parent = some region ∧
  region.hasSSADominance ctx = true ∧
  dominator.idxInParent ctx.raw < dominated.idxInParent ctx.raw

/--
Proper dominance between `dominator` and `dominated` in a `block` of a graph `region`.

Operations in the same graph block properly dominate each other independently of their order.
-/
def OperationPtr.ProperlyDominatesInGraphBlock
    (dominator dominated : OperationPtr) (block : BlockPtr) (region : RegionPtr)
    (ctx : WfIRContext OpInfo) : Prop :=
  (dominator.get! ctx.raw).parent = some block ∧
  (dominated.get! ctx.raw).parent = some block ∧
  (block.get! ctx.raw).parent = some region ∧
  region.hasSSADominance ctx = false

/--
Proper dominance between `dominator` and `dominated` in the same `block`.

It combines ordered dominance in SSACFG regions with order-independent dominance in graph regions.
-/
inductive OperationPtr.ProperlyDominatesInBlock
    (dominator dominated : OperationPtr) (block : BlockPtr) (region : RegionPtr)
    (ctx : WfIRContext OpInfo) : Prop where
  | Ssa
      (dominance :
        dominator.ProperlyDominatesInSSACFGBlock dominated block region ctx)
  | Graph
      (dominance :
        dominator.ProperlyDominatesInGraphBlock dominated block region ctx)

/--
Proper dominance between `dominator` and `dominated` operations in `region`.

Operations in the same block use the region-kind-specific operation ordering. Operations in
different blocks use block dominance in the containing region.
-/
inductive OperationPtr.ProperlyDominatesInRegion
    (dominator dominated : OperationPtr) (region : RegionPtr)
    (ctx : WfIRContext OpInfo) : Prop where
  | SameBlock {block : BlockPtr}
      (dominance :
        dominator.ProperlyDominatesInBlock dominated block region ctx)
  | BlockDominance {dominatorBlock dominatedBlock : BlockPtr}
      (hDominatorBlock :
        (dominator.get! ctx.raw).parent = some dominatorBlock)
      (hDominatedBlock :
        (dominated.get! ctx.raw).parent = some dominatedBlock)
      (dominance :
        dominatorBlock.ProperlyDominatesInRegion dominatedBlock region ctx)

/--
Proper dominance between `dominator` and `dominated` across regions, optionally allowing the
`dominator` operation to be an ancestor of the `dominated` operation depending on the boolean flag
`enclosingOk`.

The property is defined as the union of the following two cases:
* The `dominator` operation is an ancestor of the `dominated` operation, and the boolean flag
  `enclosingOk` is true.
* There exists an ancestor of the `dominated` operation that is properly dominated by the
  `dominator` operation in a block.
-/
inductive OperationPtr.ProperlyDominates (dominator dominated : OperationPtr)
    (ctx : WfIRContext OpInfo) : (enclosingOk : Bool) → Prop where
  | Ancestor
      (ancestor : (IRNode.operation dominator).Ancestor (.operation dominated) ctx)
      (hNe : dominator ≠ dominated)
      : ProperlyDominates dominator dominated ctx true
  | AncestorDominatedInRegion {ancestor : OperationPtr} {region : RegionPtr}
      (hAncestor : (IRNode.operation ancestor).Ancestor (.operation dominated) ctx)
      (dominance : dominator.ProperlyDominatesInRegion ancestor region ctx)
      (enclosingOk : Bool)
      : ProperlyDominates dominator dominated ctx enclosingOk

/--
Dominance relation between `dominator` and `dominated` across regions.
It is defined as the reflexive closure of `OperationPtr.ProperlyDominates`.
-/
def OperationPtr.Dominates (dominator dominated : OperationPtr) (ctx : WfIRContext OpInfo) : Prop :=
  dominator = dominated ∨ dominator.ProperlyDominates dominated ctx true

end Veir
