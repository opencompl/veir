module

public import Veir.Analysis.DataFlow.DominanceAnalysis

public section

namespace Veir

open Std (HashSet)

/--
Normalize an insertion point into `region` by walking outward through enclosing
operations until the point lies in a block directly contained in `region`.

If `point` already lies in `region`, it is returned unchanged. If the walk
escapes the IR hierarchy before reaching `region`, return `none`.
-/
private partial def normalizeInsertPoint
    (region : RegionPtr)
    (point : InsertPoint)
    (irCtx : WfIRContext OpCode) : Option InsertPoint := do
  let block ← point.block! irCtx.raw
  if (block.get! irCtx.raw).parent = some region then
    return point
  let parentRegion ← (block.get! irCtx.raw).parent
  let parentOp ← (parentRegion.get! irCtx.raw).parent
  normalizeInsertPoint region (.before parentOp) irCtx

/--
Whether dominance queries in this region enforce SSA dominance. Multi-block
regions always do, no matter what operation owns them: as in MLIR (see
`getDominanceInfo` in `mlir/lib/IR/Dominance.cpp`), graph-region leniency is
only granted to single-block regions, where operations may use each other
without respecting source order. Values defined outside a graph region must
still dominate the operation that owns the graph region.

This is deliberately stronger than `RegionPtr.hasSSADominance`
(`Veir/Interfaces/RegionKindInterfaces.lean`), which only reports the region
kind declared by the owning operation and ignores the block count.
-/
private def RegionPtr.enforcesSSADominance
    (region : RegionPtr) (irCtx : WfIRContext OpCode) : Bool :=
  -- Multi-block regions always have SSA dominance, whatever their kind.
  (match (region.get! irCtx.raw).firstBlock with
   | some first => (first.get! irCtx.raw).next.isSome
   | none => false) ||
  match (region.get! irCtx.raw).parent with
  | some parentOp =>
    let parent := parentOp.get! irCtx.raw
    parent.opType.getRegionKind (parent.regions.idxOf region) = .SSACFG
  | none => true

/--
Check dominance between two blocks that are already known
to lie in the same region.

This follows the immediate dominator chain from `block` 
upward until it either reaches `dominator` or the chain ends.
-/
private partial def BlockPtr.dominatesWithinRegion
    (dominator block : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : Bool := Id.run do
  if dominator = block then
    true
  else
    let some idom := block.getIDom? dfCtx | return false
    idom ≠ block && dominatesWithinRegion dominator idom dfCtx irCtx


/--
Check dominance between two operations that are already known 
to lie in the same block.

Iterates from `dominator` down the block until it either reaches 
`op` or reaches the end of the block.
-/
private def OperationPtr.dominatesWithinBlock
    (dominator op : OperationPtr)
    (irCtx : WfIRContext OpCode) : Bool := Id.run do
  let mut current := some dominator
  while let some operation := current do
    if operation = op then
      return true
    current := (operation.get! irCtx.raw).next
  false

namespace InsertPoint

/--
Check dominance between two points that are already known
to lie in the same block.
-/
private def dominatesWithinBlock
    (dominator point : InsertPoint)
    (irCtx : WfIRContext OpCode) : Bool := Id.run do
  let some block := dominator.block! irCtx.raw | return false
  let some region := (block.get! irCtx.raw).parent | return false
  if !region.enforcesSSADominance irCtx then
    return true
  if dominator = point then
    return true
  match dominator, point with
    | .before dominatorOp, .before op =>
        dominatorOp.dominatesWithinBlock op irCtx
    | .before _, .atEnd _ =>
        true
    | .atEnd _, _ =>
        false

/--
Dominance query between two insertion points.

If `point` lies in a nested region outside the region containing `dominator`, it
is normalized into the dominator's region by replacing it with the enclosing
operation position. Once both insertion points lie in the same region,
dominance is decided by same block insertion point order or by block
dominance.

`enclosingOk` decides the case where normalization lands exactly on `dominator`,
i.e. `point` lies inside a region owned by the operation at `dominator`. Such a
dominator *encloses* the point rather than preceding it, so the two are not
ordered by source position and the answer cannot be read off the block. It
mirrors the flag of the same name in MLIR's `properlyDominatesImpl`
(`mlir/lib/IR/Dominance.cpp`): reflexive queries pass `true`, while the value
uses checked by the verifier pass `false`, because an operation's results are
not available inside its own regions.
-/
private def dominates
    (dominator : InsertPoint)
    (point : InsertPoint)
    (enclosingOk : Bool)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : Bool := Id.run do
  let some dominatorBlock := dominator.block! irCtx.raw
    | return false
  let some dominatorRegion := (dominatorBlock.get! irCtx.raw).parent
    | return false

  -- If the point does not lie in the same region as `dominator`, scoot up
  -- the point's region tree until we find a location in the dominator's
  -- region that encloses it. If this fails, then we know `dominator`
  -- doesn't properly dominate the point.
  let some normalized := normalizeInsertPoint dominatorRegion point irCtx
    | return false
  -- Normalization moved the point out of a region owned by the operation at
  -- `dominator`: the dominator encloses the point. `dominatesWithinBlock` must
  -- not see these two as the same point and answer reflexively -- they are
  -- distinct program points that source order does not relate.
  if normalized ≠ point && normalized = dominator then
    if enclosingOk then
      return true
    -- As in MLIR, an enclosing dominator that is not `enclosingOk` still wins in
    -- a graph region, where every operation of a block dominates every other one
    -- regardless of order.
    return !dominatorRegion.enforcesSSADominance irCtx

  let some pointBlock := normalized.block! irCtx.raw
    | return false

  if dominatorBlock = pointBlock then
    dominator.dominatesWithinBlock normalized irCtx
  else
    return dominatorBlock.dominatesWithinRegion pointBlock dfCtx irCtx

/--
Proper dominance query between two insertion points.

From the MLIR documentation: "If A and B are in the same block and A
properly dominates B within the block, or if the block that contains A
properly dominates the block that contains B. In an SSACFG region,
Operation A dominates Operation B in the same block if A preceeds
B. In a Graph region, all operations in a block properly dominate all
operations in the same block."

An insertion point does not properly dominate itself. Otherwise this is the same query as `InsertPoint.dominates`.

See `InsertPoint.dominates` for `enclosingOk`, which decides whether a dominator
that *encloses* the point in one of its own regions counts.
-/
private def properlyDominates
    (dominator : InsertPoint)
    (point : InsertPoint)
    (enclosingOk : Bool)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : Bool :=
  if dominator = point then
    match dominator.block! irCtx.raw with
    | some block =>
      match (block.get! irCtx.raw).parent with
      | some region => !region.enforcesSSADominance irCtx
      | none => false
    | none => false
  else
    dominator.dominates point enclosingOk dfCtx irCtx


end InsertPoint

namespace BlockPtr

/--
Immediate dominator for the block entry, if the dominance analysis has
initialized this block.
-/
def immediateDominator?
    [FactSpec .dominator]
    (block : BlockPtr)
    (dfCtx : DataFlowContext) : Option BlockPtr :=
  block.getIDom? dfCtx

/--
Dominance query between two blocks, where a block dominates itself.
-/
def dominates
    [FactSpec .dominator]
    (dominator block : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : Bool :=
  (InsertPoint.atStart! dominator irCtx.raw).dominates
    (InsertPoint.atStart! block irCtx.raw) (enclosingOk := true) dfCtx irCtx

/--
Dominance query between two blocks, where a block does not dominate itself.
-/
def properlyDominates
    [FactSpec .dominator]
    (dominator block : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : Bool :=
  (InsertPoint.atStart! dominator irCtx.raw).properlyDominates
    (InsertPoint.atStart! block irCtx.raw) (enclosingOk := true) dfCtx irCtx

end BlockPtr

namespace OperationPtr

/--
Dominance query between two operations, where an operation dominates itself.

`enclosingOk` says whether `dominator` counts as dominating the operations nested
in its own regions; see `InsertPoint.dominates`.
-/
def dominates
    (dominator op : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode)
    (enclosingOk : Bool := true) : Bool :=
  (InsertPoint.before dominator).dominates (InsertPoint.before op) enclosingOk dfCtx irCtx

/--
Dominance query between two operations, where an operation does not dominate itself.

`enclosingOk` says whether `dominator` counts as properly dominating the operations
nested in its own regions; see `InsertPoint.dominates`. Checking the use of a value
passes `false`, mirroring `DominanceInfo::properlyDominates(Value, Operation *)` in
`mlir/lib/IR/Dominance.cpp`.
-/
def properlyDominates
    (dominator op : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode)
    (enclosingOk : Bool := true) : Bool :=
  (InsertPoint.before dominator).properlyDominates (InsertPoint.before op) enclosingOk dfCtx irCtx

end OperationPtr

end Veir
