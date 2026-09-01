module

public import Veir.Analysis.DataFlowFramework

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

In VeIR, dominator facts are attached to `BlockPtr`s. A separate
region metadata fact stores the postorder numbering needed by `intersect`, and
the ordinary dataflow worklist is used to revisit dependent successors until the
immediate dominator facts reach a fixpoint.
-/

namespace BlockPtr

/--
Look up the dominator fact stored on `block`.

Returns `none` when dominance analysis has not attached a dominator fact to the block.
-/
def getDominatorFact? [FactSpec .dominator]
    (block : BlockPtr) (dfCtx : DataFlowContext) : Option DominatorFact :=
  dfCtx.getFact? .dominator (.BlockPtr block)

/--
Return the immediate dominator currently recorded for `block`.

This is just `block.getDominatorFact?` projected to its `iDom` field, so it
returns `none` when the fact is missing or when the fact has no immediate
dominator yet.
-/
def getIDom? [FactSpec .dominator]
    (block : BlockPtr) (dfCtx : DataFlowContext) : Option BlockPtr :=
  block.getDominatorFact? dfCtx >>= (·.iDom)

/--
Did the dominance analysis reach `block` from the entry of its enclosing region?
-/
def isReachable [FactSpec .dominator]
    (block : BlockPtr) (dfCtx : DataFlowContext) : Bool :=
  (block.getDominatorFact? dfCtx).isSome

end BlockPtr

namespace RegionPtr

/--
Look up the region metadata fact stored at the entry block of `region`.

Returns `none` when the region has no entry block or when region metadata has
not been attached to that entry block.
-/
def getRegionMetadataFact? [FactSpec .regionMetadata] (region : RegionPtr) (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : Option RegionMetadataFact :=
  (region.get! irCtx.raw).firstBlock >>= dfCtx.getFact? .regionMetadata ∘ .BlockPtr

end RegionPtr

namespace DominatorFact

def mkDefault : DominatorFact :=
  { dependents := #[]
    payload := { iDom := none } }

def propagate (fact : DominatorFact) (_anchor : LatticeAnchor) 
    (dfCtx : DataFlowContext) (_irCtx : WfIRContext OpCode) : DataFlowContext :=
  { dfCtx with workList := fact.enqueueDependents dfCtx.workList }

instance : FactSpec .dominator where
  mkDefault := DominatorFact.mkDefault
  propagate := DominatorFact.propagate

end DominatorFact

namespace RegionMetadataFact

def mkDefault : RegionMetadataFact :=
  { dependents := #[]
    payload := { postOrderIndex := {} } }

def propagate (_fact : RegionMetadataFact) (_anchor : LatticeAnchor) 
    (dfCtx : DataFlowContext) (_irCtx : WfIRContext OpCode) : DataFlowContext :=
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
    (irCtx : WfIRContext OpCode) : Array BlockPtr × HashMap BlockPtr Nat := Id.run do
  let mut postOrder : Array BlockPtr := #[]
  let mut postOrderIndex : HashMap BlockPtr Nat := {}
  let some entry := (region.get! irCtx.raw).firstBlock
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

      if let some terminator := (block.get! irCtx.raw).lastOp then
        for succ in terminator.getSuccessors! irCtx.raw do
          if !seen.contains succ then
            stack := stack.push (succ, false)
  (postOrder, postOrderIndex)

/-- Initialize the dominators and enqueue them in reverse post order. -/
private def initializeRegion
    (region : RegionPtr)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : DataFlowContext := Id.run do
  let mut dfCtx := dfCtx
  let some entry := (region.get! irCtx.raw).firstBlock
    | return dfCtx
  let (postOrder, postOrderIndex) := collectPostOrder region irCtx
  let reversePostOrder := postOrder.reverse
  dfCtx :=
    dfCtx.modifyFact .regionMetadata (.BlockPtr entry) fun fact =>
      fact.setPostOrderIndex postOrderIndex

  for block in reversePostOrder do
    let mut dependents := #[]
    if let some terminator := (block.get! irCtx.raw).lastOp then
      for succ in terminator.getSuccessors! irCtx.raw do
        dependents := dependents.push (InsertPoint.atStart! succ irCtx.raw, kind)
    dfCtx := dfCtx.modifyFact .dominator (.BlockPtr block) fun fact =>
      (fact.setDependents dependents).setIDom
        (if block = entry then some entry else none)
    dfCtx := dfCtx.enqueue (InsertPoint.atStart! block irCtx.raw, kind)
  dfCtx

/-- Recursively initialize the analysis on nested regions. -/
partial def initializeRecursively
    (op : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : DataFlowContext := Id.run do
  let mut dfCtx := dfCtx

  for region in op.getRegions! irCtx.raw do
    dfCtx := initializeRegion region dfCtx irCtx

    let mut currentBlock := (region.get! irCtx.raw).firstBlock
    while let some block := currentBlock do
      let mut currentOp := (block.get! irCtx.raw).firstOp
      while let some nestedOp := currentOp do
        dfCtx := initializeRecursively nestedOp dfCtx irCtx
        currentOp := (nestedOp.get! irCtx.raw).next
      currentBlock := (block.get! irCtx.raw).next

  dfCtx

def init
    (top : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : DataFlowContext :=
  initializeRecursively top dfCtx irCtx

/--
Find the nearest common dominator of `block1` and `block2`.

On each step, the cursor with the smaller postorder index is moved upward until
both cursors coincide.
-/
private def intersect
    (block1 block2 : BlockPtr)
    (postOrderIndex : HashMap BlockPtr Nat)
    (dfCtx : DataFlowContext) : BlockPtr := Id.run do
  let mut finger1 := block1
  let mut finger2 := block2
  while finger1 ≠ finger2 do
    while postOrderIndex[finger1]! < postOrderIndex[finger2]! do
      finger1 := (finger1.getIDom? dfCtx).get!
    while postOrderIndex[finger2]! < postOrderIndex[finger1]! do
      finger2 := (finger2.getIDom? dfCtx).get!
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
    (irCtx : WfIRContext OpCode) : Option BlockPtr := do
  let region := ((block.get! irCtx.raw).parent).get!
  let entry := ((region.get! irCtx.raw).firstBlock).get!
  let metadata ← region.getRegionMetadataFact? dfCtx irCtx
  if block = entry then 
    return entry

  let mut currentPredUse := (block.get! irCtx.raw).firstUse
  let mut newIDom : Option BlockPtr := none

  while let some predUse := currentPredUse do
    let predUseStruct := predUse.get! irCtx.raw
    currentPredUse := predUseStruct.nextUse
    let predOp := predUseStruct.owner
    let some predBlock := (predOp.get! irCtx.raw).parent
      | continue
    let some _ := predBlock.getIDom? dfCtx
      | continue
    newIDom :=
      match newIDom with
      | none => predBlock
      | some idom =>
          intersect predBlock idom metadata.postOrderIndex dfCtx

  newIDom

/--
Visit one dominator work item.

Only block entry insertion points schedule dominance work. Non-entry insertion points are ignored.
For a block entry, recompute the block's current immediate dominator candidate and update the fact
stored on that block when the candidate changes.
-/
def visit
    (point : InsertPoint)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : DataFlowContext :=
  if point.prev! irCtx.raw ≠ none then
    -- Dominance facts are attached only to block-entry insertion points.
    dfCtx
  else
    let block := (point.block! irCtx.raw).get!
    match computeImmediateDominator block dfCtx irCtx with
    | none => dfCtx
    | some newIDom => 
      dfCtx.modifyFactAndPropagate .dominator (.BlockPtr block) (fun fact =>
       (fact.setIDom (some newIDom), some newIDom ≠ fact.iDom)) irCtx

end DominanceAnalysis

def DominanceAnalysis : DataFlowAnalysis :=
  { kind := DominanceAnalysis.kind
    init := DominanceAnalysis.init
    visit := DominanceAnalysis.visit }

end Veir
