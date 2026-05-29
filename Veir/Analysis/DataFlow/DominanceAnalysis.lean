module

public import Veir.Analysis.DataFlowFramework
public import Std.Data.HashSet
public import Std.Data.HashMap

public section

namespace Veir

open Std (HashMap HashSet)

/-!
# Dominance analysis

This module implements immediate dominator analysis using the Cooper Harvey
Kennedy algorithm described in their paper "A Simple, Fast Dominance Algorithm."

Like the algorithm in that paper, we initialize the entry block to dominate
itself, process reachable blocks in reverse postorder, and iteratively refine
each block's immediate dominator by intersecting the dominator chains of its
already processed predecessors. The `intersect` helper uses cached postorder
indices of two blocks as pointers into their dominator chains. The lower
ranked pointer is moved upward until both pointers meet at their nearest
common dominator. `computeImmediateDominator` implements the
paper's update step by choosing the first predecessor whose immediate
dominator is already known as an initial candidate, then repeatedly
intersects that candidate with the other predecessors whose immediate
dominator is already known. The resulting candidate is the current
immediate dominator estimate for the block. As more predecessor dominator
facts become available, the worklist revisits the block and recomputes that
estimate. Each recomputation either preserves the estimate or moves it upward
in the dominator tree (note that this is monotonic!), and the process repeats
until the facts reach a fixpoint.

In VeIR, dominator facts are attached to block entry `InsertPoint`s. A separate
region metadata fact stores the postorder numbering needed by `intersect`, and
the ordinary dataflow worklist is used to revisit dependent successors until the
immediate dominator facts reach a fixpoint.
-/

namespace BlockPtr

/--
Look up the dominator fact stored at the entry insertion point of `block`.

Returns `none` when dominance analysis has not attached a dominator fact to that
block entry.
-/
def getDominatorFact? [FactSpec .dominator] (block : BlockPtr) (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Option DominatorFact :=
  dfCtx.getFact? .dominator (.InsertPoint (InsertPoint.atStart! block irCtx))

/--
Return the immediate dominator currently recorded for `block`.

This is just `block.getDominatorFact?` projected to its `iDom` field, so it
returns `none` when the fact is missing or when the fact has no immediate
dominator yet.
-/
def getIDom? [FactSpec .dominator] (block : BlockPtr) (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Option BlockPtr :=
  block.getDominatorFact? dfCtx irCtx >>= (·.iDom)

/--
Collect the dominators currently reachable from `block` by following the `iDom`
chain.

The returned set always includes `block` itself. If `block` has no dominator
fact, returns `none`. Otherwise, this walks the currently known immediate
dominator chain until it reaches a root or a self-loop, so during analysis it
may return only the known prefix of the full dominator set.
-/
def getDoms? [FactSpec .dominator] (block : BlockPtr) (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Option (HashSet BlockPtr) := do
  let fact ← block.getDominatorFact? dfCtx irCtx
  let mut doms := (∅ : HashSet BlockPtr).insert block
  let mut current := fact.iDom
  while let some dom := current do
    doms := doms.insert dom
    let next := dom.getIDom? dfCtx irCtx
    if next = some dom then
      return doms
    current := next
  doms

end BlockPtr

namespace RegionPtr

/--
Look up the region metadata fact stored at the entry block of `region`.

Returns `none` when the region has no entry block or when region metadata has
not been attached to that entry block.
-/
def getRegionMetadataFact? [FactSpec .regionMetadata] (region : RegionPtr) (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Option RegionMetadataFact :=
  (region.get! irCtx).firstBlock >>= 
    dfCtx.getFact? .regionMetadata ∘ (InsertPoint.atStart! · irCtx)

end RegionPtr

namespace DominatorFact

def mkDefault (anchor : LatticeAnchor) : DominatorFact :=
  { anchor := anchor
    dependents := #[]
    payload := { iDom := none } }

def propagate (fact : DominatorFact) (dfCtx : DataFlowContext)
    (_irCtx : IRContext OpCode) : DataFlowContext :=
  { dfCtx with workList := fact.enqueueDependents dfCtx.workList }

instance : FactSpec .dominator where
  mkDefault := DominatorFact.mkDefault
  propagate := DominatorFact.propagate

end DominatorFact

namespace RegionMetadataFact

def mkDefault (anchor : LatticeAnchor) : RegionMetadataFact :=
  { anchor := anchor
    dependents := #[]
    payload := { postOrderIndex := {} } }

def propagate (_fact : RegionMetadataFact) (dfCtx : DataFlowContext)
    (_irCtx : IRContext OpCode) : DataFlowContext :=
  dfCtx

instance : FactSpec .regionMetadata where
  mkDefault := RegionMetadataFact.mkDefault
  propagate := RegionMetadataFact.propagate

end RegionMetadataFact

namespace DominanceAnalysis

def kind : AnalysisKind :=
  .dominance

/--
The returned array is CFG in postorder, and the map assigns each block a
postorder index used by `intersect`.
-/
private def collectPostOrder
    (region : RegionPtr)
    (irCtx : IRContext OpCode) : Array BlockPtr × HashMap BlockPtr Nat := Id.run do
  let mut postOrder : Array BlockPtr := #[]
  let mut postOrderIndex : HashMap BlockPtr Nat := {}
  let some entry := (region.get! irCtx).firstBlock
    | return (postOrder, postOrderIndex)
  let mut stack : Array (BlockPtr × Bool) := #[(entry, false)]
  let mut seen : HashSet BlockPtr := ∅

  while !stack.isEmpty do
    let (block, visited) := stack.back!
    stack := stack.pop

    if visited then
      postOrder := postOrder.push block
      postOrderIndex := postOrderIndex.insert block postOrder.size
    else if seen.contains block then
      continue
    else
      seen := seen.insert block
      stack := stack.push (block, true)

      if let some terminator := (block.get! irCtx).lastOp then
        for succ in terminator.getSuccessors! irCtx do
          if !seen.contains succ then
            stack := stack.push (succ, false)
  (postOrder, postOrderIndex)

/-- Initialize the dominators and enqueue them in reverse post order. -/
private def initializeRegion
    (region : RegionPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  let mut dfCtx := dfCtx
  let some entry := (region.get! irCtx).firstBlock
    | return dfCtx
  let (postOrder, postOrderIndex) := collectPostOrder region irCtx
  let reversePostOrder := postOrder.reverse
  dfCtx :=
    dfCtx.modifyFact .regionMetadata (InsertPoint.atStart! entry irCtx) fun fact =>
      fact.setPostOrderIndex postOrderIndex

  for block in reversePostOrder do
    let mut dependents := #[]
    if let some terminator := (block.get! irCtx).lastOp then
      for succ in terminator.getSuccessors! irCtx do
        dependents := dependents.push (InsertPoint.atStart! succ irCtx, kind)
    dfCtx := dfCtx.modifyFact .dominator (InsertPoint.atStart! block irCtx) fun fact =>
      (fact.setDependents dependents).setIDom
        (if block = entry then some entry else none)
    dfCtx := dfCtx.enqueue (InsertPoint.atStart! block irCtx, kind)
  dfCtx

/-- Recursively initialize the analysis on nested regions. -/
partial def initializeRecursively
    (op : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  let mut dfCtx := dfCtx

  for region in (op.get! irCtx).regions do
    dfCtx := initializeRegion region dfCtx irCtx

    let mut currentBlock := (region.get! irCtx).firstBlock
    while let some block := currentBlock do
      let mut currentOp := (block.get! irCtx).firstOp
      while let some nestedOp := currentOp do
        dfCtx := initializeRecursively nestedOp dfCtx irCtx
        currentOp := (nestedOp.get! irCtx).next
      currentBlock := (block.get! irCtx).next

  dfCtx

def init
    (top : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext :=
  initializeRecursively top dfCtx irCtx

/--
Find the nearest common dominator of `block1` and `block2`.

On each step, the cursor with the smaller postorder index is moved upward until
both cursors coincide.
-/
private def intersect
    (block1 block2 : BlockPtr)
    (postOrderIndex : HashMap BlockPtr Nat)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : BlockPtr := Id.run do
  let mut finger1 := block1
  let mut finger2 := block2
  while finger1 ≠ finger2 do
    while postOrderIndex[finger1]! < postOrderIndex[finger2]! do
      finger1 := (finger1.getIDom? dfCtx irCtx).get!
    while postOrderIndex[finger2]! < postOrderIndex[finger1]! do
      finger2 := (finger2.getIDom? dfCtx irCtx).get!
  finger1

/--
Compute the next immediate dominator candidate for `block`.

The entry block dominates itself. For every other block, we scan its predecessors,
pick the first one whose dominator fact has already been computed, and then
repeatedly `intersect` that candidate with each other processed predecessor.
-/
private def computeImmediateDominator
    (block : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Option BlockPtr := do
  let region := ((block.get! irCtx).parent).get!
  let entry := ((region.get! irCtx).firstBlock).get!
  let metadata ← region.getRegionMetadataFact? dfCtx irCtx
  if block = entry then 
    return entry

  let mut currentPredUse := (block.get! irCtx).firstUse
  let mut newIDom : Option BlockPtr := none

  while let some predUse := currentPredUse do
    let predUseStruct := predUse.get! irCtx
    currentPredUse := predUseStruct.nextUse
    let predOp := predUseStruct.owner
    let some predBlock := (predOp.get! irCtx).parent
      | continue
    let some _ := predBlock.getIDom? dfCtx irCtx
      | continue
    newIDom :=
      match newIDom with
      | none => predBlock
      | some idom =>
          intersect predBlock idom metadata.postOrderIndex dfCtx irCtx

  newIDom

/--
Visit one dominator work item.

Only block entry insertion points carry dominator facts. Non-entry insertion points
are ignored. For a block entry, recompute the block's current immediate dominator
candidate and update the fact stored at that entry when the candidate changes.
-/
def visit
    (point : InsertPoint)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext :=
  if point.prev! irCtx ≠ none then
    -- Dominance facts are attached only to block-entry insertion points.
    dfCtx
  else
    let block := (point.block! irCtx).get!
    match computeImmediateDominator block dfCtx irCtx with
    | none => dfCtx
    | some newIDom => 
      let anchor := InsertPoint.atStart! block irCtx
      dfCtx.modifyFactAndPropagate .dominator anchor (fun fact =>
       (fact.setIDom (some newIDom), some newIDom ≠ fact.iDom)) irCtx

/-- Recurse up the dominator tree to see if `dominator` dominates `block`. -/
def dominates
    (dominator block : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Bool := Id.run do
  let some fact ← block.getDominatorFact? dfCtx irCtx | false
  if dominator = block then 
    return true
  let mut current := fact.iDom
  while let some candidate := current do
    if candidate = dominator then
      return true
    let next := candidate.getIDom? dfCtx irCtx
    if next = some candidate then
      return false
    current := next
  false

/-- Same thing as `dominates` except a block dominating itself doesn't count. -/
def properlyDominates
    (dominator block : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Bool :=
  dominator ≠ block && dominates dominator block dfCtx irCtx

end DominanceAnalysis

def DominanceAnalysis : DataFlowAnalysis :=
  { kind := DominanceAnalysis.kind
    init := DominanceAnalysis.init
    visit := DominanceAnalysis.visit }

end Veir
