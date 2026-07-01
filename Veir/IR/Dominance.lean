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
    (irCtx : IRContext OpCode) : Option InsertPoint := do
  let block ← point.block! irCtx
  if (block.get! irCtx).parent = some region then
    return point
  let parentRegion ← (block.get! irCtx).parent
  let parentOp ← (parentRegion.get! irCtx).parent
  normalizeInsertPoint region (.before parentOp) irCtx

/--
Whether this region has MLIR-style SSA dominance. In graph regions, operations
in the same block may use each other without respecting source order, but values
defined outside the graph region must still dominate the operation that owns the
graph region.
-/
private def RegionPtr.hasSSADominanceByKind
    (region : RegionPtr) (irCtx : IRContext OpCode) : Bool :=
  match (region.get! irCtx).parent with
  | some parentOp =>
    let parent := parentOp.get! irCtx
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
    (irCtx : IRContext OpCode) : Bool := Id.run do
  if dominator = block then
    return true
  -- In a graph region there is no block ordering, so every block dominates every
  -- other block in the region.
  if let some region := (block.get! irCtx).parent then
    if !region.hasSSADominanceByKind irCtx then
      return true
  let some idom := block.getIDom? dfCtx irCtx | return false
  return idom ≠ block && dominatesWithinRegion dominator idom dfCtx irCtx


/--
Check dominance between two operations that are already known 
to lie in the same block.

Iterates from `dominator` down the block until it either reaches 
`op` or reaches the end of the block.
-/
private def OperationPtr.dominatesWithinBlock
    (dominator op : OperationPtr)
    (irCtx : IRContext OpCode) : Bool := Id.run do
  let mut current := some dominator
  while let some operation := current do
    if operation = op then
      return true
    current := (operation.get! irCtx).next
  false

namespace InsertPoint

/--
Check dominance between two points that are already known
to lie in the same block.
-/
private def dominatesWithinBlock
    (dominator point : InsertPoint)
    (irCtx : IRContext OpCode) : Bool := Id.run do
  let some block := dominator.block! irCtx | return false
  let some region := (block.get! irCtx).parent | return false
  if !region.hasSSADominanceByKind irCtx then
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
-/
private def dominates
    (dominator : InsertPoint)
    (point : InsertPoint)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Bool := Id.run do
  let some dominatorBlock := dominator.block! irCtx
    | return false
  let some dominatorRegion := (dominatorBlock.get! irCtx).parent
    | return false

  -- If the point does not lie in the same region as `dominator`, scoot up
  -- the point's region tree until we find a location in the dominator's
  -- region that encloses it. If this fails, then we know `dominator`
  -- doesn't properly dominate the point.
  let some point := normalizeInsertPoint dominatorRegion point irCtx
    | return false 
  let some pointBlock := point.block! irCtx
    | return false

  if dominatorBlock = pointBlock then
    dominator.dominatesWithinBlock point irCtx
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
-/
private def properlyDominates
    (dominator : InsertPoint)
    (point : InsertPoint)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Bool :=
  if dominator = point then
    match dominator.block! irCtx with
    | some block =>
      match (block.get! irCtx).parent with
      | some region => !region.hasSSADominanceByKind irCtx
      | none => false
    | none => false
  else
    dominator.dominates point dfCtx irCtx


end InsertPoint

namespace BlockPtr

/--
Immediate dominator for the block entry, if the dominance analysis has
initialized this block.
-/
def immediateDominator?
    [FactSpec .dominator]
    (block : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Option BlockPtr :=
  block.getIDom? dfCtx irCtx

/--
Dominance query between two blocks, where a block dominates itself.
-/
def dominatesByAnalysis
    [FactSpec .dominator]
    (dominator block : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Bool :=
  (InsertPoint.atStart! dominator irCtx).dominates (InsertPoint.atStart! block irCtx) dfCtx irCtx

/--
Dominance query between two blocks, where a block does not dominate itself.
-/
def properlyDominatesByAnalysis
    [FactSpec .dominator]
    (dominator block : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Bool :=
  (InsertPoint.atStart! dominator irCtx).properlyDominates
    (InsertPoint.atStart! block irCtx) dfCtx irCtx

end BlockPtr

namespace OperationPtr

/--
Dominance query between two operations, where an operation dominates itself.
-/
def dominatesByAnalysis
    (dominator op : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Bool :=
  (InsertPoint.before dominator).dominates (InsertPoint.before op) dfCtx irCtx

/--
Dominance query between two operations, where an operation does not dominate itself.
-/
def properlyDominatesByAnalysis
    (dominator op : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Bool :=
  (InsertPoint.before dominator).properlyDominates (InsertPoint.before op) dfCtx irCtx

end OperationPtr

end Veir
