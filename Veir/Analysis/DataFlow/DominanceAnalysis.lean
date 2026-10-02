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
immediate dominator estimate for the block. Each reverse postorder sweep either
preserves the estimates or moves them upward in the dominator tree (note that
this is monotonic!), and the process repeats until the facts reach a fixpoint.

In VeIR, dominator facts are attached to `BlockPtr`s. A separate region metadata
fact stores the postorder numbering needed by `intersect`. Each region is one
dataflow work item; visiting it performs reverse postorder sweeps until no
immediate dominator changes.
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

Reachability is represented by a computed immediate dominator, rather than the
mere presence of a possibly uninitialized dominator fact.
-/
def isReachable [FactSpec .dominator]
    (block : BlockPtr) (dfCtx : DataFlowContext) : Bool :=
  (block.getIDom? dfCtx).isSome

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

/-- Initialize the reachable dominator facts and enqueue one work item for the region. -/
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
    dfCtx := dfCtx.modifyFact .dominator (.BlockPtr block) fun fact =>
      fact.setIDom (if block = entry then some entry else none)
  dfCtx.enqueue (InsertPoint.atStart! entry irCtx.raw, kind)

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

The boolean result reports whether a reachable predecessor is still waiting for
its first immediate dominator value, in which case the region needs another sweep.
-/
private def computeImmediateDominator
    (block : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : Option BlockPtr × Bool := Id.run do
  let region := ((block.get! irCtx.raw).parent).get!
  let entry := ((region.get! irCtx.raw).firstBlock).get!
  let some metadata := region.getRegionMetadataFact? dfCtx irCtx
    | return (none, false)
  if block = entry then
    return (some entry, false)

  let mut currentPredUse := (block.get! irCtx.raw).firstUse
  let mut newIDom : Option BlockPtr := none
  let mut waiting := false -- Waiting for reachable predecessor

  while let some predUse := currentPredUse do
    let predUseStruct := predUse.get! irCtx.raw
    currentPredUse := predUseStruct.nextUse
    let predOp := predUseStruct.owner
    let some predBlock := (predOp.get! irCtx.raw).parent
      | continue
    if (predBlock.getIDom? dfCtx).isNone then
      if metadata.postOrderIndex.contains predBlock then
        waiting := true
      continue
    newIDom :=
      match newIDom with
      | none => predBlock
      | some idom =>
          intersect predBlock idom metadata.postOrderIndex dfCtx

  (newIDom, waiting)

/--
Solve the region whose entry is `point` using reverse postorder sweeps.

Revisiting every reachable block until an entire sweep makes no changes (i.e. fixpoint)
is the standard Cooper Harvey Kennedy iteration. In particular, a change to an ancestor
in an immediate dominator chain is observed on the next sweep without the need to
store a dependency edge for every chain traversal, which is too slow.
-/
def visit
    (point : InsertPoint)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : DataFlowContext := Id.run do
  if point.prev! irCtx.raw ≠ none then
    return dfCtx
  let entry := (point.block! irCtx.raw).get!
  let region := ((entry.get! irCtx.raw).parent).get!
  if (region.get! irCtx.raw).firstBlock ≠ some entry then
    return dfCtx
  let some metadata := region.getRegionMetadataFact? dfCtx irCtx
    | return dfCtx
  let reversePostOrder :=
    (metadata.postOrderIndex.toArray.qsort (·.2 > ·.2)).map (·.1)
  let mut dfCtx := dfCtx
  -- Records if a block's iDom changed or if it's waiting for a predecessor,
  -- meaning another reverse postorder sweep is required
  let mut changedOrWaiting := true
  while changedOrWaiting do
    changedOrWaiting := false
    for block in reversePostOrder do
      let (newIDom?, waiting) :=
        computeImmediateDominator block dfCtx irCtx
      changedOrWaiting := changedOrWaiting || waiting
      let some newIDom := newIDom?
        | continue
      let oldIDom := block.getIDom? dfCtx
      if oldIDom ≠ some newIDom then
        -- Initializing a fact cannot invalidate an earlier chain traversal: no
        -- traversal can pass through a block before that block has an iDom.
        -- A refinement of an existing fact can, so it requires another sweep.
        changedOrWaiting := changedOrWaiting || oldIDom.isSome
        dfCtx := dfCtx.modifyFactAndPropagate .dominator (.BlockPtr block) (fun fact =>
          (fact.setIDom (some newIDom), true)) irCtx
  dfCtx

end DominanceAnalysis

def DominanceAnalysis : DataFlowAnalysis :=
  { kind := DominanceAnalysis.kind
    init := DominanceAnalysis.init
    visit := DominanceAnalysis.visit }

end Veir
