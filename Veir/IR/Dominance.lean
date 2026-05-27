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
private partial def normalizeInsertPoint?
    (region : RegionPtr)
    (point : InsertPoint)
    (irCtx : IRContext OpCode) : Option InsertPoint := do
  let block ← point.block! irCtx
  if (block.get! irCtx).parent = some region then
    return point
  let parentRegion ← (block.get! irCtx).parent
  let parentOp ← (parentRegion.get! irCtx).parent
  normalizeInsertPoint? region (.before parentOp) irCtx

/--
Check dominance between two blocks that are already known
to lie in the same region.

This follows the immediate dominator chain from `block` 
upward until it either reaches `dominator` or the chain ends.
-/
private partial def dominatesWithinRegion
    (dominator block : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Bool :=
  if dominator = block then
    true
  else
    match block.getIDom? dfCtx irCtx with
    | some idom => idom ≠ block && dominatesWithinRegion dominator idom dfCtx irCtx
    | none => false

/--
Check dominance between two operations that are already known 
to lie in the same block.

Iterates from `dominator` down the block until it either reaches 
`op` or reaches the end of the block.
-/
private def dominatesWithinBlock
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
Proper dominance query between two insertion points.

If `point` lies in a nested region outside the region containing `dominator`, it
is normalized into the dominator's region by replacing it with the enclosing
operation position. Once both insertion points lie in the same region,
dominance is decided by same block insertion point order or by block
dominance.
-/
private def properlyDominates
    (dominator : InsertPoint)
    (point : InsertPoint)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Bool := Id.run do
  if dominator = point then
    return false

  let some dominatorBlock := dominator.block! irCtx
    | return false
  let some dominatorRegion := (dominatorBlock.get! irCtx).parent
    | return false
  let pointInRegion? :=
    match point.block! irCtx with
    | none => none
    | some pointBlock =>
        if (pointBlock.get! irCtx).parent = dominatorRegion then
          point
        else
          -- Scoot up the point's region tree until we find a location in the
          -- dominator's region that encloses it.  If this fails, then we know 
          -- there is no dominance relation.
          normalizeInsertPoint? dominatorRegion point irCtx
  let some point := pointInRegion?
    | return false
  let some pointBlock := point.block! irCtx
    | return false

  if dominator = point then
    return true
  if dominatorBlock = pointBlock then
    match dominator, point with
    | .before dominatorOp, .before op =>
        return dominatesWithinBlock dominatorOp op irCtx
    | .before _, .atEnd _ =>
        return true
    | .atEnd _, _ =>
        return false
  return dominatesWithinRegion dominatorBlock pointBlock dfCtx irCtx

/--
Dominance query between two insertion points.

An insertion point dominates itself. Otherwise this is the same query as
`InsertPoint.properlyDominates`.
-/
private def dominates
    (dominator : InsertPoint)
    (point : InsertPoint)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Bool :=
  dominator = point || dominator.properlyDominates point dfCtx irCtx

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
Dominance query between two blocks.
-/
def dominates
    [FactSpec .dominator]
    (dominator block : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Bool :=
  (InsertPoint.atStart! dominator irCtx).dominates (InsertPoint.atStart! block irCtx) dfCtx irCtx

/--
Proper version of `BlockPtr.dominates`.
-/
def properlyDominates
    [FactSpec .dominator]
    (dominator block : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Bool :=
  (InsertPoint.atStart! dominator irCtx).properlyDominates
    (InsertPoint.atStart! block irCtx) dfCtx irCtx

end BlockPtr

end Veir
