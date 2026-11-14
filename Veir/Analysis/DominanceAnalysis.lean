module

public import Veir.Analysis.DataFlowFramework

public section

namespace Veir

open Std (HashMap HashSet)

/-!
# Dominance analysis

This module implements immediate dominator analysis using the Cooper-Harvey-Kennedy algorithm
described in "A Simple, Fast Dominance Algorithm."

Each region is solved independently with a local boolean fixpoint loop. Once it converges, the
stable result is published as facts in the supplied `DataFlowContext` for use by the dominance
query API.
-/

namespace BlockPtr

/-- Look up the dominator fact attached to `block`. -/
def getDominatorFact? [FactSpec .dominator]
    (block : BlockPtr) (dfCtx : DataFlowContext) : Option DominatorFact :=
  dfCtx.getFact? .dominator (.BlockPtr block)

/-- Return the immediate dominator recorded for `block`. -/
def getIDom? [FactSpec .dominator]
    (block : BlockPtr) (dfCtx : DataFlowContext) : Option BlockPtr :=
  block.getDominatorFact? dfCtx >>= (·.iDom)

/-- Return whether dominance analysis reached `block`. -/
def isReachable [FactSpec .dominator]
    (block : BlockPtr) (dfCtx : DataFlowContext) : Bool :=
  (block.getIDom? dfCtx).isSome

end BlockPtr

namespace DominatorFact

def mkDefault : DominatorFact :=
  { payload := {} }

def propagate (fact : DominatorFact) (_anchor : LatticeAnchor)
    (dfCtx : DataFlowContext) (_irCtx : WfIRContext OpCode) : DataFlowContext :=
  { dfCtx with workList := fact.enqueueDependents dfCtx.workList }

instance : FactSpec .dominator where
  mkDefault := mkDefault
  propagate := propagate

end DominatorFact

namespace DominanceAnalysis

/-- Collect the reachable blocks of `region` in CFG postorder. -/
private def collectPostOrder
    (region : RegionPtr)
    (irCtx : WfIRContext OpCode) : Array BlockPtr := Id.run do
  let mut postOrder : Array BlockPtr := #[]
  let some entry := region.getFirstBlock! irCtx.raw
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

      if let some terminator := block.getLastOp! irCtx.raw then
        for successor in terminator.getSuccessors! irCtx.raw do
          if !seen.contains successor then
            stack := stack.push (successor, false)
  postOrder

/-- Collect reachable predecessor indices for each block. -/
private def collectPredecessors
    (reversePostOrder : Array BlockPtr)
    (irCtx : WfIRContext OpCode) : Array (Array Nat) := Id.run do
  let mut blockIndex : HashMap BlockPtr Nat := {}
  for (block, index) in reversePostOrder.zipIdx do
    blockIndex := blockIndex.insert block index

  let mut preds := #[]
  for block in reversePostOrder do
    let mut blockPreds := #[]
    for predBlock in block.getPredecessors! irCtx.raw do
      if let some index := blockIndex.get? predBlock then
        blockPreds := blockPreds.push index
    preds := preds.push blockPreds
  preds

/-- Find the nearest common dominator of two reverse postorder indices. -/
private def intersect
    (index1 index2 : Nat)
    (iDoms : Array Nat) : Nat := Id.run do
  let mut finger1 := index1
  let mut finger2 := index2
  while finger1 != finger2 do
    while finger1 > finger2 do
      finger1 := iDoms[finger1]!
    while finger2 > finger1 do
      finger2 := iDoms[finger2]!
  finger1

/-- CHK fixpoint loop -/
private def fixpoint
    (reversePostOrder : Array BlockPtr)
    (preds : Array (Array Nat)) : Array Nat := Id.run do
  -- Initialize dominators array
  let mut iDoms := Array.replicate reversePostOrder.size reversePostOrder.size
  -- Start node
  iDoms := iDoms.set! 0 0
  -- Fixpoint loop
  let mut changed := true
  while changed do
    changed := false
    for blockIndex in [1:iDoms.size] do
      let mut newIDom : Option Nat := none
      for pred in preds[blockIndex]! do
        if iDoms[pred]! = iDoms.size then
          continue
        newIDom :=
          match newIDom with
          | none => some pred
          | some iDom => some (intersect pred iDom iDoms)
      let some iDom := newIDom
        | continue
      if iDoms[blockIndex]! != iDom then
        iDoms := iDoms.set! blockIndex iDom
        changed := true
  iDoms

/-- Solve one region to a fixpoint, then dominator facts to the dataflow context. -/
private def computeRegionDominance
    (region : RegionPtr)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : DataFlowContext := Id.run do
  -- Cache the post order of blocks
  let reversePostOrder := (collectPostOrder region irCtx).reverse
  if reversePostOrder.isEmpty then
    return dfCtx
  -- Cache the predecessor of blocks using post order indices
  let preds := collectPredecessors reversePostOrder irCtx
  -- Run a fixpoint loop on this region, calculating the immediate
  -- dominators for all reachable blocks in the region.
  let iDoms := fixpoint reversePostOrder preds
  -- Add dominance facts to the dataflow context.
  let mut dfCtx := dfCtx
  for (block, index) in reversePostOrder.zipIdx do
    let iDom := reversePostOrder[iDoms[index]!]!
    dfCtx := dfCtx.modifyFact .dominator (.BlockPtr block) fun fact =>
      (fact.setIDom iDom).setNextInReversePostOrder reversePostOrder[index + 1]?
  dfCtx

end DominanceAnalysis

/--
Compute dominance for every region nested under `top` and add the results to `dfCtx`.

Each region is solved independently with the Cooper-Harvey-Kennedy fixpoint algorithm. A finalized
dominator fact is attached to every block reachable from that region's entry; empty regions and
unreachable blocks receive no fact.

The operation worklist traverses the nested operation tree rooted at `top`. Because a well formed
operation has a unique parent, each operation is added at most once, so the number of operations in
the context bounds the traversal.
-/
def DominanceAnalysis
    (top : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : DataFlowContext := Id.run do
  let mut dfCtx := dfCtx
  let mut worklist := #[top]
  for _ in [:irCtx.raw.operations.size] do
    let some op := worklist.back?
      | break
    worklist := worklist.pop

    for region in op.getRegions! irCtx.raw do
      dfCtx := DominanceAnalysis.computeRegionDominance region dfCtx irCtx

      let mut currentBlock := region.getFirstBlock! irCtx.raw
      while let some block := currentBlock do
        let mut currentOp := block.getFirstOp! irCtx.raw
        while let some nestedOp := currentOp do
          worklist := worklist.push nestedOp
          currentOp := nestedOp.getNextOp! irCtx.raw
        currentBlock := block.getNextBlock! irCtx.raw
  dfCtx

end Veir
