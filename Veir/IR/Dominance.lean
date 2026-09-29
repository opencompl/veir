module

public import Veir.Analysis.DataFlow.DominanceAnalysis
public import Veir.Interfaces.RegionKindInterfaces

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
    let some idom := block.getIDom? dfCtx | return true
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

/--
The position of every operation within its block.

Comparing two positions orders two operations of the same block without walking
the block between them. The positions are only valid as long as the IR is not
modified.
-/
def WfIRContext.opPositions (irCtx : WfIRContext OpCode) :
    Std.HashMap OperationPtr Nat := Id.run do
  let mut positions := Std.HashMap.emptyWithCapacity irCtx.raw.operations.size
  for (_, block) in irCtx.raw.blocks do
    let mut position := 0
    let mut current := block.firstOp
    while let some op := current do
      positions := positions.insert op position
      position := position + 1
      current := (op.get! irCtx.raw).next
  return positions

namespace InsertPoint

/--
Check dominance between two points that are already known
to lie in the same block.

Two operations are ordered by `positions` if it is given (see
`WfIRContext.opPositions`), and by walking the block otherwise.
-/
private def dominatesWithinBlock
    (dominator point : InsertPoint)
    (irCtx : WfIRContext OpCode)
    (positions : Option (Std.HashMap OperationPtr Nat)) : Bool := Id.run do
  if dominator = point then
    return true
  match dominator, point with
    | .before dominatorOp, .before op =>
        match positions with
        | some positions => decide (positions[dominatorOp]! ≤ positions[op]!)
        | none => dominatorOp.dominatesWithinBlock op irCtx
    | .before _, .atEnd _ =>
        true
    | .atEnd _, _ =>
        false

/--
Proper dominance query between two insertion points.

If `point` lies in a nested region outside the region containing `dominator`, it
is normalized into the dominator's region by replacing it with the enclosing
operation position. Once both insertion points lie in the same region,
dominance is decided by same block insertion point order or by block
dominance.

In a graph region there is no ordering between points, so every point in the
region properly dominates every other, including itself.

If `enclosingOk` is set, `dominator` properly dominates `point` when it encloses
it. Callers checking that a definition dominates a use pass `false`, since an
operation's results are not available inside its own regions.

`positions`, if given, orders operations of the same block, as in
`InsertPoint.dominatesWithinBlock`.
-/
private def properlyDominates
    (dominator : InsertPoint)
    (point : InsertPoint)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode)
    (enclosingOk : Bool := true)
    (positions : Option (Std.HashMap OperationPtr Nat) := none) : Bool := Id.run do
  let some dominatorBlock := dominator.block! irCtx.raw
    | return false
  let some dominatorRegion := (dominatorBlock.get! irCtx.raw).parent
    | return false
  let hasSSADominance := dominatorRegion.hasSSADominance irCtx

  if dominator = point then
    return !hasSSADominance

  -- If the point does not lie in the same region as `dominator`, scoot up
  -- the point's region tree until we find a location in the dominator's
  -- region that encloses it. If this fails, then we know `dominator`
  -- doesn't properly dominate the point.
  let some point := normalizeInsertPoint dominatorRegion point irCtx
    | return false 
  let some pointBlock := point.block! irCtx.raw
    | return false

  if dominator = point then
    return enclosingOk || !hasSSADominance

  if dominatorBlock = pointBlock then
    return !hasSSADominance || dominator.dominatesWithinBlock point irCtx positions
  else
    return dominatorBlock.dominatesWithinRegion pointBlock dfCtx irCtx

/--
Dominance query between two insertion points.

A point always dominates itself. Otherwise this is the same query as
`InsertPoint.properlyDominates`.
-/
private def dominates
    (dominator : InsertPoint)
    (point : InsertPoint)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode)
    (positions : Option (Std.HashMap OperationPtr Nat) := none) : Bool :=
  dominator = point || dominator.properlyDominates point dfCtx irCtx (positions := positions)


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
  (InsertPoint.atStart! dominator irCtx.raw).dominates (InsertPoint.atStart! block irCtx.raw) dfCtx irCtx

/--
Proper dominance query between two blocks. A block does not properly dominate
itself in an SSACFG region, while the sole block of a graph region properly
dominates itself.
-/
def properlyDominates
    [FactSpec .dominator]
    (dominator block : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : Bool :=
  (InsertPoint.atStart! dominator irCtx.raw).properlyDominates
    (InsertPoint.atStart! block irCtx.raw) dfCtx irCtx

end BlockPtr

namespace OperationPtr

/--
Dominance query between two operations, where an operation dominates itself.
-/
def dominates
    (dominator op : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : Bool :=
  (InsertPoint.before dominator).dominates (InsertPoint.before op) dfCtx irCtx

/--
Proper dominance query between two operations. An operation does not properly
dominate itself in an SSACFG region, while operations in a graph region properly
dominate every operation in the same block, including themselves.

`positions`, if given, orders operations of the same block, as in
`InsertPoint.dominatesWithinBlock`.
-/
def properlyDominates
    (dominator op : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode)
    (enclosingOk : Bool := true)
    (positions : Option (Std.HashMap OperationPtr Nat) := none) : Bool :=
  (InsertPoint.before dominator).properlyDominates (InsertPoint.before op) dfCtx irCtx
    enclosingOk positions

/-- Collect nested operations in reverse postorder. Unreachable blocks
are omitted.  A region with no dominance metadata (including an empty
region, or one the analysis never reached) contributes no operations.
TODO: Replace this with an iterator, which should be more efficient.
-/
partial def opsInDominanceOrder
    (op : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : Array OperationPtr := Id.run do
  let mut ops := #[]
  for region in (op.get! irCtx.raw).regions do
    let mut blocks := #[]
    if let some metadata := region.getRegionMetadataFact? dfCtx irCtx then
      blocks := (metadata.postOrderIndex.toArray.qsort (·.2 > ·.2)).map (·.1)
    for block in blocks do
      let mut currentOp := (block.get! irCtx.raw).firstOp
      while let some innerOp := currentOp do
        ops := ops.push innerOp
        ops := ops ++ innerOp.opsInDominanceOrder dfCtx irCtx
        currentOp := (innerOp.get! irCtx.raw).next
  return ops

end OperationPtr

namespace ValuePtr

/--
Does the definition of `value` properly dominate the use of it by `op`?

`positions` must be `irCtx.opPositions`, so that operations of the same block
are ordered without walking the block.
-/
def properlyDominatesUse
    (value : ValuePtr)
    (op : OperationPtr)
    (dfCtx : DataFlowContext)
    (positions : Std.HashMap OperationPtr Nat)
    (irCtx : WfIRContext OpCode) : Bool :=
  match value with
  | .opResult result =>
      result.op.properlyDominates op dfCtx irCtx (enclosingOk := false)
        (positions := some positions)
  | .blockArgument argument =>
      (InsertPoint.atStart! argument.block irCtx.raw).dominates (.before op) dfCtx irCtx
        (positions := some positions)

end ValuePtr

end Veir
