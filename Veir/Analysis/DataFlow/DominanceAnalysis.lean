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
already processed predecessors. The `intersect` helper uses dense reverse postorder
indices as pointers into cached immediate dominator chains. The lower ranked
pointer is moved upward until both pointers meet at their nearest common dominator
`computeImmediateDominator` implements the paper's update step by choosing the first
predecessor whose immediate dominator is already known as an initial candidate, then
repeatedly intersects that candidate with the other predecessors whose immediate
dominator is already known. The resulting candidate is the current immediate
dominator estimate for the block. Each reverse postorder sweep either preserves the
estimates or moves them upward in the dominator tree (note that this is monotonic!),
and the process repeats until the facts reach a fixpoint.

In VeIR, one dominance fact attached to the entry block stores the result for an
entire region. It caches the reverse postorder, maps blocks to dense indices, and
stores the immediate dominator and predecessor indices used by `intersect`. A
region's entry point is its dataflow work item. Each visit performs exactly one
complete reverse postorder sweep, then re-enqueues the entry point when another
sweep is required.
-/

namespace RegionPtr

/--
Look up the region dominance fact stored at the entry block of `region`.

Returns `none` when the region has no entry block or when dominance analysis has
not attached a fact to that entry block.
-/
def getRegionDominanceFact? [FactSpec .regionDominance]
    (region : RegionPtr)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : Option RegionDominanceFact :=
  (region.get! irCtx.raw).firstBlock >>= dfCtx.getFact? .regionDominance ∘ .BlockPtr

end RegionPtr

namespace BlockPtr

/--
Did the dominance analysis reach `block` from the entry of its enclosing region?

Reachable blocks have an index and an initialized immediate dominator index in
their enclosing region's dominance fact.
-/
def isReachable [FactSpec .regionDominance]
    (block : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : Bool := Id.run do
  let some region := (block.get! irCtx.raw).parent
    | return false
  let some dominance := region.getRegionDominanceFact? dfCtx irCtx
    | return false
  let some index := dominance.blockIndex.get? block
    | return false
  return decide (dominance.immediateDominators[index]! < dominance.immediateDominators.size)

end BlockPtr

namespace RegionDominanceFact

def mkDefault : RegionDominanceFact :=
  { dependents := #[]
    payload := {} }

def propagate (fact : RegionDominanceFact) (_anchor : LatticeAnchor)
    (dfCtx : DataFlowContext) (_irCtx : WfIRContext OpCode) : DataFlowContext :=
  { dfCtx with workList := fact.enqueueDependents dfCtx.workList }

instance : FactSpec .regionDominance where
  mkDefault := RegionDominanceFact.mkDefault
  propagate := RegionDominanceFact.propagate

end RegionDominanceFact

namespace DominanceAnalysis

def kind : AnalysisKind :=
  .dominance

/--
The returned array is the CFG in postorder.
-/
private def collectPostOrder
    (region : RegionPtr)
    (irCtx : WfIRContext OpCode) : Array BlockPtr := Id.run do
  let mut postOrder : Array BlockPtr := #[]
  let some entry := (region.get! irCtx.raw).firstBlock
    | return postOrder
  let mut stack : Array (BlockPtr × Bool) := #[(entry, false)]
  let mut seen : HashSet BlockPtr := ∅

  while !stack.isEmpty do
    let (block, visited) := stack.back!
    stack := stack.pop

    if visited then
      postOrder := postOrder.push block
    else if seen.contains block then
      continue
    else
      seen := seen.insert block
      stack := stack.push (block, true)

      if let some terminator := (block.get! irCtx.raw).lastOp then
        for succ in terminator.getSuccessors! irCtx.raw do
          if !seen.contains succ then
            stack := stack.push (succ, false)
  postOrder

/-- Cache reachable predecessor indices once, outside the iterative solver. -/
private def collectPredecessors
    (reversePostOrder : Array BlockPtr)
    (blockIndex : HashMap BlockPtr Nat)
    (irCtx : WfIRContext OpCode) : Array (Array Nat) := Id.run do
  let mut predecessors := #[]
  for block in reversePostOrder do
    let mut preds := #[]
    let mut currentUse := (block.get! irCtx.raw).firstUse
    while let some predUse := currentUse do
      let use := predUse.get! irCtx.raw
      currentUse := use.nextUse
      let some predBlock := (use.owner.get! irCtx.raw).parent
        | continue
      if let some index := blockIndex.get? predBlock then
        preds := preds.push index
    predecessors := predecessors.push preds
  predecessors

/-- Initialize a region dominance fact and enqueue its first reverse postorder sweep. -/
private def initializeRegion
    (region : RegionPtr)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : DataFlowContext := Id.run do
  let mut dfCtx := dfCtx
  let some entry := (region.get! irCtx.raw).firstBlock
    | return dfCtx
  let reversePostOrder := (collectPostOrder region irCtx).reverse
  let mut blockIndex : HashMap BlockPtr Nat := {}
  let mut index := 0
  for block in reversePostOrder do
    blockIndex := blockIndex.insert block index
    index := index + 1
  let predecessors := collectPredecessors reversePostOrder blockIndex irCtx
  let mut immediateDominators := Array.replicate reversePostOrder.size reversePostOrder.size
  immediateDominators := immediateDominators.set! 0 0
  dfCtx :=
    dfCtx.modifyFactAndPropagate .regionDominance (.BlockPtr entry) (fun fact =>
      ({ fact with payload :=
          { reversePostOrder, blockIndex, predecessors, immediateDominators } }, true)) irCtx
  dfCtx.enqueue (InsertPoint.atStart! entry irCtx.raw, kind)

/-- Recursively initialize the analysis on nested regions. -/
partial def init
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
        dfCtx := init nestedOp dfCtx irCtx
        currentOp := (nestedOp.get! irCtx.raw).next
      currentBlock := (block.get! irCtx.raw).next

  dfCtx
/--
Find the nearest common dominator of two reverse postorder indices.

On each step, the finger with the larger reverse postorder index is moved upward
until both fingers coincide.
-/
private def intersect
    (index1 index2 : Nat)
    (immediateDominators : Array Nat) : Nat := Id.run do
  let mut finger1 := index1
  let mut finger2 := index2
  while finger1 ≠ finger2 do
    while finger1 > finger2 do
      finger1 := immediateDominators[finger1]!
    while finger2 > finger1 do
      finger2 := immediateDominators[finger2]!
  finger1

/--
Compute the next immediate dominator candidate for `block`.

The entry block dominates itself. For every other block, we scan its predecessors,
pick the first one whose working immediate dominator has already been computed, and then
repeatedly `intersect` that candidate with each other processed predecessor.

The boolean result reports whether a reachable predecessor is still waiting for
its first immediate dominator value, in which case the region needs another sweep.
-/
private def computeImmediateDominator
    (blockIndex : Nat)
    (predecessors : Array (Array Nat))
    (immediateDominators : Array Nat) : Option Nat × Bool := Id.run do
  if blockIndex = 0 then
    return (some 0, false)

  let mut newIDomIndex : Option Nat := none
  let mut waiting := false -- Waiting for reachable predecessor

  for predIndex in predecessors[blockIndex]! do
    if immediateDominators[predIndex]! = immediateDominators.size then
      waiting := true
      continue
    newIDomIndex :=
      match newIDomIndex with
      | none => predIndex
      | some idomIndex => intersect predIndex idomIndex immediateDominators

  (newIDomIndex, waiting)

/--
Perform one complete Cooper-Harvey-Kennedy reverse postorder sweep.

If an initialized immediate dominator changes, or a reachable predecessor is
still uninitialized, the region entry is re-enqueued for another sweep.
-/
def visit
    (point : InsertPoint)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : DataFlowContext := Id.run do
  if point.prev! irCtx.raw ≠ none then
    return dfCtx
  let block := (point.block! irCtx.raw).get!
  let region := ((block.get! irCtx.raw).parent).get!
  let entry := ((region.get! irCtx.raw).firstBlock).get!
  let some dominance := region.getRegionDominanceFact? dfCtx irCtx
    | return dfCtx
  let mut dfCtx := dfCtx
  let mut immediateDominators := dominance.immediateDominators
  let mut immediateDominatorsChanged := false
  let mut needsSweep := false
  for blockIndex in [:dominance.reversePostOrder.size] do
    let (newIDomIndex?, waiting) :=
      computeImmediateDominator blockIndex dominance.predecessors immediateDominators
    needsSweep := needsSweep || waiting
    if let some newIDomIndex := newIDomIndex? then
      let oldIDomIndex := immediateDominators[blockIndex]!
      if oldIDomIndex ≠ newIDomIndex then
        -- Initializing a fact cannot invalidate an earlier chain traversal: no
        -- traversal can pass through a block before that block has an iDom.
        -- A refinement of an existing fact can, so it requires another sweep.
        needsSweep := needsSweep || oldIDomIndex ≠ immediateDominators.size
        immediateDominatorsChanged := true
        immediateDominators := immediateDominators.set! blockIndex newIDomIndex
  if immediateDominatorsChanged then
    dfCtx := dfCtx.modifyFactAndPropagate .regionDominance (.BlockPtr entry) (fun fact =>
      (fact.setImmediateDominators immediateDominators, true)) irCtx
  if needsSweep then
    dfCtx := dfCtx.enqueue (InsertPoint.atStart! entry irCtx.raw, kind)
  dfCtx

end DominanceAnalysis

def DominanceAnalysis : DataFlowAnalysis :=
  { kind := DominanceAnalysis.kind
    init := DominanceAnalysis.init
    visit := DominanceAnalysis.visit }

end Veir
