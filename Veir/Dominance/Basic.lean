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

/-- Reachability of `block` from the entry of `region`. -/
def BlockPtr.ReachableFromEntry (block : BlockPtr) (region : RegionPtr)
    (ctx : WfIRContext OpInfo) : Prop :=
  ∃ entry blocks,
    (region.get! ctx.raw).firstBlock = some entry ∧
    region.Path ctx entry block blocks

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
An operation is reachable from a region entry when its containing block is reachable
from the entry of its containing region.
-/
def OperationPtr.ReachableFromEntry (op : OperationPtr)
    (ctx : WfIRContext OpInfo) : Prop :=
  ∃ block region,
    (op.get! ctx.raw).parent = some block ∧
    block.ReachableFromEntry region ctx

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

/-- Structural evidence that an operation dominates a block entry. -/
inductive OperationPtr.BlockEntryDominance
    (source : OperationPtr) (target : BlockPtr) (ctx : WfIRContext OpInfo) : Prop where
  | ssa {sourceBlock : BlockPtr} {region : RegionPtr}
      (sourceParent : (source.get! ctx.raw).parent = some sourceBlock)
      (sourceBlockParent : (sourceBlock.get! ctx.raw).parent = some region)
      (targetParent : (target.get! ctx.raw).parent = some region)
      (regionSSA : region.hasSSADominance ctx = true)
      (blocksNe : sourceBlock ≠ target)
      (blockDominance : sourceBlock.Dominates target ctx) :
      source.BlockEntryDominance target ctx
  | graph {sourceBlock : BlockPtr} {region : RegionPtr}
      (sourceParent : (source.get! ctx.raw).parent = some sourceBlock)
      (sourceBlockParent : (sourceBlock.get! ctx.raw).parent = some region)
      (targetParent : (target.get! ctx.raw).parent = some region)
      (regionGraph : region.hasSSADominance ctx = false) :
      source.BlockEntryDominance target ctx
  | ancestor {ancestor : OperationPtr} {region : RegionPtr}
      (localDominance : source.DominatesInRegion ancestor region ctx)
      (ancestry : IRNode.Ancestor (.operation ancestor) (.block target) ctx) :
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
      (blockDominance : sourceBlock.Dominates target ctx) :
      source.BlockEndDominance target ctx
  | graph {sourceBlock : BlockPtr} {region : RegionPtr}
      (sourceParent : (source.get! ctx.raw).parent = some sourceBlock)
      (sourceBlockParent : (sourceBlock.get! ctx.raw).parent = some region)
      (targetParent : (target.get! ctx.raw).parent = some region)
      (regionGraph : region.hasSSADominance ctx = false) :
      source.BlockEndDominance target ctx
  | ancestor {ancestor : OperationPtr} {region : RegionPtr}
      (localDominance : source.DominatesInRegion ancestor region ctx)
      (ancestry : IRNode.Ancestor (.operation ancestor) (.block target) ctx) :
      source.BlockEndDominance target ctx

/-! ## Projection into ancestor regions -/

/--
An operation ancestor of `op` that is directly contained in `region`.
The ancestry relation is reflexive, so `op` itself is such an ancestor when it
is directly contained in `region`.
-/
@[expose]
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
@[expose]
def OperationPtr.HierarchicallyReachable (op : OperationPtr)
    (ctx : WfIRContext OpInfo) : Prop :=
  op.ReachableFromEntry ctx ∧
  (∀ region projection,
    op.AncestorOpInRegion projection region ctx →
    projection.ReachableFromEntry ctx) ∧
  ∀ source : OperationPtr,
    source.Dominates op ctx → source.ReachableFromEntry ctx

/-- Strict operation dominance excludes pointer equality. -/
@[expose]
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
@[expose]
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
@[expose]
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
@[expose]
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
@[expose]
def BlockArgumentPtr.DominatesIp (argument : BlockArgumentPtr)
    (point : InsertPoint) (ctx : WfIRContext OpInfo) : Prop :=
  argument.InBounds ctx.raw ∧
  (argument.get! ctx.raw).owner.DominatesIp point ctx

/-- Propositional dominance of an insertion point by an SSA value. -/
@[expose]
def ValuePtr.DominatesIp (value : ValuePtr) (point : InsertPoint)
    (ctx : WfIRContext OpInfo) : Prop :=
  match value with
  | .opResult result => result.DominatesIp point ctx
  | .blockArgument argument => argument.DominatesIp point ctx

end Veir
