module

import Veir.Interfaces.RegionKindInterfaces
public import Veir.IRNesting
public import Veir.Rewriter.InsertPoint
public import Veir.Verifier

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

/-- Reachability of `block` from the entry of `region`. -/
def BlockPtr.ReachableFromEntry (block : BlockPtr) (region : RegionPtr)
    (ctx : WfIRContext OpInfo) : Prop :=
  ∃ entry blocks,
    (region.get! ctx.raw).firstBlock = some entry ∧
    region.Path ctx entry block blocks

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
An operation is reachable from a region entry when its containing block is reachable
from the entry of its containing region.
-/
def OperationPtr.ReachableFromEntry (op : OperationPtr)
    (ctx : WfIRContext OpInfo) : Prop :=
  ∃ block region,
    (op.get! ctx.raw).parent = some block ∧
    block.ReachableFromEntry region ctx

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

/-- Structural evidence that an operation dominates a block entry. -/
inductive OperationPtr.BlockEntryDominance
    (source : OperationPtr) (target : BlockPtr) (ctx : WfIRContext OpInfo) : Prop where
  | ssa {sourceBlock : BlockPtr} {region : RegionPtr}
      (sourceParent : (source.get! ctx.raw).parent = some sourceBlock)
      (sourceBlockParent : (sourceBlock.get! ctx.raw).parent = some region)
      (targetParent : (target.get! ctx.raw).parent = some region)
      (regionSSA : region.hasSSADominance ctx = true)
      (blocksNe : sourceBlock ≠ target)
      (blockDominance :
        sourceBlock.ProperlyDominatesInRegion target region ctx) :
      source.BlockEntryDominance target ctx
  | graph {sourceBlock : BlockPtr} {region : RegionPtr}
      (sourceParent : (source.get! ctx.raw).parent = some sourceBlock)
      (sourceBlockParent : (sourceBlock.get! ctx.raw).parent = some region)
      (targetParent : (target.get! ctx.raw).parent = some region)
      (regionGraph : region.hasSSADominance ctx = false) :
      source.BlockEntryDominance target ctx
  | ancestor {ancestor : OperationPtr} {region : RegionPtr}
      (localDominance : source.ProperlyDominatesInRegion ancestor region ctx)
      (ancestry : IRNode.Ancestor (.operation ancestor) (.block target) ctx) :
      source.BlockEntryDominance target ctx
  | enclosing
      (ancestry : IRNode.Ancestor (.operation source) (.block target) ctx) :
      source.BlockEntryDominance target ctx

/-- Structural evidence that an operation dominates a block end. -/
inductive OperationPtr.BlockEndDominance
    (source : OperationPtr) (target : BlockPtr) (ctx : WfIRContext OpInfo) : Prop where
  | same
      (sourceParent : (source.get! ctx.raw).parent = some target) :
      source.BlockEndDominance target ctx
  | ssa {sourceBlock : BlockPtr} {region : RegionPtr}
      (sourceParent : (source.get! ctx.raw).parent = some sourceBlock)
      (sourceBlockParent : (sourceBlock.get! ctx.raw).parent = some region)
      (targetParent : (target.get! ctx.raw).parent = some region)
      (regionSSA : region.hasSSADominance ctx = true)
      (blocksNe : sourceBlock ≠ target)
      (blockDominance :
        sourceBlock.ProperlyDominatesInRegion target region ctx) :
      source.BlockEndDominance target ctx
  | graph {sourceBlock : BlockPtr} {region : RegionPtr}
      (sourceParent : (source.get! ctx.raw).parent = some sourceBlock)
      (sourceBlockParent : (sourceBlock.get! ctx.raw).parent = some region)
      (targetParent : (target.get! ctx.raw).parent = some region)
      (regionGraph : region.hasSSADominance ctx = false) :
      source.BlockEndDominance target ctx
  | ancestor {ancestor : OperationPtr} {region : RegionPtr}
      (localDominance : source.ProperlyDominatesInRegion ancestor region ctx)
      (ancestry : IRNode.Ancestor (.operation ancestor) (.block target) ctx) :
      source.BlockEndDominance target ctx
  | enclosing
      (ancestry : IRNode.Ancestor (.operation source) (.block target) ctx) :
      source.BlockEndDominance target ctx

/-! ## Projection into ancestor regions -/

/--
An operation ancestor of `op` that is directly contained in `region`.
The ancestry relation is reflexive, so `op` itself is such an ancestor when it
is directly contained in `region`.
-/
def OperationPtr.AncestorOpInRegion
    (op ancestor : OperationPtr) (region : RegionPtr)
    (ctx : WfIRContext OpInfo) : Prop :=
  (IRNode.operation ancestor).Ancestor (.operation op) ctx ∧
  ancestor.getParentRegion! ctx.raw = some region

/--
An operation is hierarchically reachable when it is reachable at every
enclosing region level and every operation dominating it is reachable from
entry. The latter condition is needed when execution follows an operand
to its defining operation: `WfIRContext.Dom` intentionally imposes no operand
dominance obligations on unreachable operations.
-/
def OperationPtr.HierarchicallyReachable (op : OperationPtr)
    (ctx : WfIRContext OpInfo) : Prop :=
  op.ReachableFromEntry ctx ∧
  (∀ region projection,
    op.AncestorOpInRegion projection region ctx →
    projection.ReachableFromEntry ctx) ∧
  ∀ source : OperationPtr,
    source.Dominates op ctx → source.ReachableFromEntry ctx

/-- Strict operation dominance excludes pointer equality. -/
def OperationPtr.StrictlyDominates (source target : OperationPtr)
    (ctx : WfIRContext OpInfo) : Prop :=
  source.Dominates target ctx ∧ source ≠ target

/-! ## Insertion-point and value dominance -/

/--
A witness that follows operation parents and stops at the first operation in
`region`. This stronger relation is used where projection must be deterministic.
-/
inductive OperationPtr.FirstAncestorOpInRegion :
    OperationPtr → RegionPtr → OperationPtr → WfIRContext OpInfo → Prop where
  | here {op : OperationPtr} {region : RegionPtr}
      {block : BlockPtr} {ctx : WfIRContext OpInfo}
      (opParent : (op.get! ctx.raw).parent = some block)
      (blockParent : (block.get! ctx.raw).parent = some region) :
      FirstAncestorOpInRegion op region op ctx
  | step {op : OperationPtr} {region : RegionPtr}
      {block : BlockPtr} {currentRegion : RegionPtr}
      {parent projection : OperationPtr} {ctx : WfIRContext OpInfo}
      (opParent : (op.get! ctx.raw).parent = some block)
      (blockParent : (block.get! ctx.raw).parent = some currentRegion)
      (regionNe : currentRegion ≠ region)
      (regionParent : (currentRegion.get! ctx.raw).parent = some parent)
      (tail : parent.FirstAncestorOpInRegion region projection ctx) :
      FirstAncestorOpInRegion op region projection ctx

/--
Lift an insertion point into an ancestor region.

The relation exposes raw block and region parents. A first-ancestor witness is
used only after crossing the region that directly contains an `atEnd` point.
-/
inductive InsertPoint.LiftToRegion :
    InsertPoint → RegionPtr → InsertPoint → WfIRContext OpInfo → Prop where
  | before {op projection : OperationPtr} {region : RegionPtr}
      {ctx : WfIRContext OpInfo}
      (projectionPath : op.FirstAncestorOpInRegion region projection ctx) :
      LiftToRegion (.before op) region (.before projection) ctx
  | atEndHere {block : BlockPtr} {region : RegionPtr}
      {ctx : WfIRContext OpInfo}
      (blockParent : (block.get! ctx.raw).parent = some region) :
      LiftToRegion (.atEnd block) region (.atEnd block) ctx
  | atEndNested {block : BlockPtr} {currentRegion region : RegionPtr}
      {parent projection : OperationPtr} {ctx : WfIRContext OpInfo}
      (blockParent : (block.get! ctx.raw).parent = some currentRegion)
      (regionNe : currentRegion ≠ region)
      (regionParent : (currentRegion.get! ctx.raw).parent = some parent)
      (projectionPath : parent.FirstAncestorOpInRegion region projection ctx) :
      LiftToRegion (.atEnd block) region (.before projection) ctx

/--
Operation dominance at an insertion point.

Away from block entry, the point is dominated exactly when its immediately
preceding operation is dominated. At an operation that starts a block, SSA
regions use strict operation dominance while graph regions also allow the
operation itself. An empty block's start and end use block-entry dominance.
-/
def OperationPtr.DominatesIp (source : OperationPtr) (point : InsertPoint)
    (ctx : WfIRContext OpInfo) : Prop :=
  match point.prev! ctx.raw with
  | some previous => source.Dominates previous ctx
  | none =>
      match point with
      | .before target =>
          source.StrictlyDominates target ctx ∨
          (source = target ∧
            ∃ block region,
              (target.get! ctx.raw).parent = some block ∧
              (block.get! ctx.raw).parent = some region ∧
              region.hasSSADominance ctx = false)
      | .atEnd block => source.BlockEndDominance block ctx

/-- A block entry dominates a point after lifting that point into the block's region. -/
def BlockPtr.DominatesIp (source : BlockPtr) (point : InsertPoint)
    (ctx : WfIRContext OpInfo) : Prop :=
  ∃ region lifted target,
    (source.get! ctx.raw).parent = some region ∧
    point.LiftToRegion region lifted ctx ∧
    lifted.block! ctx.raw = some target ∧
    source.Dominates target ctx

/--
An operation result dominates a point after lifting the point into the
defining operation's region. The final disjunction excludes a genuinely nested
point that projects to immediately before its own defining operation.
-/
def OpResultPtr.DominatesIp (result : OpResultPtr) (point : InsertPoint)
    (ctx : WfIRContext OpInfo) : Prop :=
  result.InBounds ctx.raw ∧
  let owner := (result.get! ctx.raw).owner
  ∃ block region lifted,
      (owner.get! ctx.raw).parent = some block ∧
      (block.get! ctx.raw).parent = some region ∧
      point.LiftToRegion region lifted ctx ∧
      owner.DominatesIp lifted ctx ∧
      (point = .before owner ∨ lifted ≠ .before owner)

/-- A block argument is available wherever its owning block's entry dominates. -/
def BlockArgumentPtr.DominatesIp (argument : BlockArgumentPtr)
    (point : InsertPoint) (ctx : WfIRContext OpInfo) : Prop :=
  argument.InBounds ctx.raw ∧
  (argument.get! ctx.raw).owner.DominatesIp point ctx

/-- Propositional dominance of an insertion point by an SSA value. -/
def ValuePtr.DominatesIp (value : ValuePtr) (point : InsertPoint)
    (ctx : WfIRContext OpInfo) : Prop :=
  match value with
  | .opResult result => result.DominatesIp point ctx
  | .blockArgument argument => argument.DominatesIp point ctx

end Veir
