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
Check dominance between two blocks that are already known to lie in the same
region.

This follows the immediate dominator chain from `block` upward until it either
reaches `dominator` or the chain ends.
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
Check dominance between two operations that are already known to lie in the same block.

Iterates from `dominator` down the block until it either reaches `op` or reaches the
end of the block.
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


/--
Collect the dominators in `block`'s own region.

The returned set contains `block` together with the blocks on its local
immediate dominator chain. Enclosing region dominators are intentionally not
included here; `BlockPtr.dominators?` adds those separately.
-/
private partial def localDominators?
    (block : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Option (HashSet BlockPtr) := do
  let _ ← block.getDominatorFact? dfCtx irCtx
  match block.getIDom? dfCtx irCtx with
  | some idom =>
      if idom = block then
        return (∅ : HashSet BlockPtr).insert block
      else
        return (← localDominators? idom dfCtx irCtx).insert block
  | none =>
      return (∅ : HashSet BlockPtr).insert block

/--
Immediate dominator of a block start insertion point, if the block has
initialized dominance information.

For an entry block of a nested region, this is the insertion point immediately
before the enclosing operation. For any other reachable block, this is the end
of the immediate dominator block.
-/
private def blockStartImmediateDominator?
    (block : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Option InsertPoint := do
  let _ ← block.getDominatorFact? dfCtx irCtx
  let parentRegion ← (block.get! irCtx).parent
  if (parentRegion.get! irCtx).firstBlock = some block then
    let parentOp ← (parentRegion.get! irCtx).parent
    let _ ← (parentOp.get! irCtx).parent
    return .before parentOp
  let iDomBlock ← block.getIDom? dfCtx irCtx
  return .atEnd iDomBlock

namespace InsertPoint

/--
Immediate dominator of an insertion point, if the enclosing block has
dominance information.

Within a block, the immediate dominator is the preceding insertion point. At a
block start, the immediate dominator is inherited from control flow or, for a
nested region entry, from the enclosing operation.
-/
def immediateDominator?
    (point : InsertPoint)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Option InsertPoint := do
  let block ← point.block! irCtx
  match point with
  | .before op =>
      match (op.get! irCtx).prev with
      | some prev =>
          return .before prev
      | none =>
          blockStartImmediateDominator? block dfCtx irCtx
  | .atEnd block =>
      match (block.get! irCtx).lastOp with
      | some lastOp =>
          return .before lastOp
      | none =>
          blockStartImmediateDominator? block dfCtx irCtx

/--
All dominators of an insertion point, including the point itself.

Returns `none` when the enclosing block has no dominance information.
-/
partial def dominators?
    (point : InsertPoint)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Option (HashSet InsertPoint) := do
  let block ← point.block! irCtx
  let _ ← block.getDominatorFact? dfCtx irCtx
  match point.immediateDominator? dfCtx irCtx with
  | some idom =>
      return (← idom.dominators? dfCtx irCtx).insert point
  | none =>
      return (∅ : HashSet InsertPoint).insert point

/--
Proper dominance query between two insertion points.

If `point` lies in a nested region outside the region containing `dominator`, it
is normalized into the dominator's region by replacing it with the enclosing
operation position. Once both insertion points lie in the same region,
dominance is decided by same block insertion point order or by block
dominance.
-/
def properlyDominates
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
def dominates
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
Dominance query between two insertion points.
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

/--
All dominators of this block, including the block itself.

Returns `none` when the block has no initialized dominator fact, which is how
the dominance analysis represents unreachable blocks.

Note that this returns enclosing blocks that dominate the block through
nested regions as well.
-/
partial def dominators?
    [FactSpec .dominator]
    (block : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Option (HashSet BlockPtr) := do
  let mut doms ← localDominators? block dfCtx irCtx
  let some parentRegion := (block.get! irCtx).parent
    | return doms
  let some parentOp := (parentRegion.get! irCtx).parent
    | return doms
  let some parentBlock := (parentOp.get! irCtx).parent
    | return doms
  if let some parentDoms := parentBlock.dominators? dfCtx irCtx then
    doms := doms ∪ parentDoms
  return doms

end BlockPtr

namespace OperationPtr

/--
Analysis-backed dominance query for operations.

This follows MLIR's region-dominance behavior: if `op₂` is nested inside a
region enclosed by `op₁`, the query normalizes `op₂` to the enclosing operation
in `op₁`'s region before comparing block dominance or same-block order.
-/
def dominates
    [FactSpec .dominator]
    (dominator op : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Bool :=
  if dominator = op then
    true
  else
    (InsertPoint.before dominator).properlyDominates (InsertPoint.before op) dfCtx irCtx

/--
Proper version of `OperationPtr.dominates`.
-/
def properlyDominates
    [FactSpec .dominator]
    (dominator op : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Bool :=
  dominator ≠ op && dominator.dominates op dfCtx irCtx

end OperationPtr

end Veir
