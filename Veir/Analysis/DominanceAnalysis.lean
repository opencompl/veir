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

PROOF DEFINITIONS:
Let A be the current array of immediate dominator candidates for blocks.
Let R be the set of blocks reachable from the region entry.
For b ∈ R:
* If b is uninitialized, Dom(A, b) = R.
* Dom(A, entry) = {entry}
* else, Dom(A, b) = ∪ Dom(A, candidateIDom(A, b))
A block d is the semantic dominator of b when d properly dominates b and
every other proper dominator of b dominates d.
A block x is an A-ancestor of b if x = b or x is encountered by repeatedly
applying candidateIDom(A, ·) starting from b.
A proper A-ancestor is an A-ancestor different from b.
Dom(A, b) is the set of all A-ancestors of b.

We must prove, that upon reaching fixpoint, ∀ b ∈ R, Dom(A, b) = the set created by
finding all d ∈ R where BlockPtr.Dominates(d, b) is true.
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
    let mut currentUse := block.getFirstUse! irCtx.raw
    while let some predUse := currentUse do
      currentUse := predUse.getNextUse! irCtx.raw
      let predOp := predUse.getOwner! irCtx.raw
      let some predBlock := predOp.getParent! irCtx.raw
        | continue
      if let some index := blockIndex.get? predBlock then
        blockPreds := blockPreds.push index
    preds := preds.push blockPreds
  preds

/-- 
Find the nearest common dominator of two reverse postorder indices. 

PROOF:
In laymans terms, we are proving that this algorithm does in fact compute
the intersection.

We must prove that, if x and y are initialized, then
Dom(A, intersect(x, y, A)) = Dom(A, x) ∩ Dom(A, y). Let f₁ and f₂ be two fingers.
The following loop invartiant must be maintained: Dom(A, f₁) ∩ Dom(A, f₂) = Dom(A, x) ∩ Dom(A, y).
Initially, it holds because f₁ = x and f₂ = y.
Suppose f₁ > f₂. Since every proper A-ancestor has a smaller RPO index [LEMMA NEEDED], f₁ > f₂ implies
that f₁ cannot be  the ancestor of f₂. Therefore, f₁ ∉ Dom(A, f₂) [LEMMA NEEDED?]. Moving f₁ to its parent in
the iDom chain only removes f₁ from its ancestor set:
Dom(A, candidateIDom(f₁)) = Dom(f₁) \ {f₁}.
Because f₁ ∉ Dom(A, f₂), removing f₁ does not change the intersection:
Dom(A, candidateIDom(A, f₁)) ∩ Dom(A, f₂)
  = (Dom(A, f₁) \ {f₁}) ∩ Dom(A, f₂)
  = Dom(A, f₁) ∩ Dom(A, f₂).
Therefore advancing f₁ preserves the loop invariant. The same reasoning applies when f₂ > f₁.

Each advancement replaces a finger with a strictly smaller RPO index. When the fingers differ, 
one is larger and is advanced, so their sum strictly decreases. The loop therefore terminates.

At termination, f₁ = f₂ = q. Applying the loop invariatn gives us:
Dom(A, x) ∩ Dom(A, y)
  = Dom(A, q) ∩ Dom(A, q)
  = Dom(A, q).

Since q is the result of `intersect`, we know:
Dom(A, intersect(x, y, A)) = Dom(A, q) 
Dom(A, x) ∩ Dom(A, y). = Dom(A, q) ∩ Dom(A, q) = Dom(A, q)

Therefore,
Dom(A, intersect(x, y, A)) = Dom(A, x) ∩ Dom(A, y).
∎
-/
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

/--
CHK fixpoint loop

PROOF (for predecessor loop):
Fix some non entry block b. Let P be the prefix of predecessors of b processed so far.
The loop invariant is:
- if `newIDom = none`, every predecessor in the prefix P is uninitialized. Therefore,
  ∩_{p ∈ P} Dom(A, p) = R.
- if `newIDom = some q`, then
  Dom(A, q) = ∩_{p ∈ P} Dom(A, p).
The following cases occur:
- Initially, P is empty and `newIDom = none`. The intersection is thus R.
- If the next predecessor is uninitialized, then it has Dom(A, p) = R. 
  The code skips this, which is valid because, for some set S, S ∩ R = S.
- The first initialized predecessor changes `newIDom` from `none` to `some p`.
  For the prefix P right before p, we have:
  R ∩ Dom(A, p) = Dom(A, p).
- else, suppose `newIDom = some q` before processing an initialized predecessor p.
  The code replaces `newIDom` by `some (intersect(p, q, A))`. Let P be the old processed 
  prefix before p. Let Dom(A, q) = ⋂_{r ∈ P} Dom(A, r). After processing p, we get the prefix
  P' = P followed by p. The intersection for P' therefore is:
  ⋂_{r ∈ P'} Dom(A, r) = (⋂_{r ∈ P} Dom(A, r)) ∩ Dom(A, p).
  Using the `intersect` proof,
  this gives us:
  Dom(A, intersect(p, q, A)) 
    = Dom(A, p) ∩ Dom(A, q) 
    = Dom(A, p) ∩ (⋂_{r ∈ P} Dom(A, r))
    = (⋂_{r ∈ P} Dom(A, r)) ∩ Dom(A, p)
    = ⋂_{r ∈ P'} Dom(A, r)
  This clearly shows the preservation of the invariant.
After the predecessor loop, P = predecessors(b).
- If `newIDom = none`, the code does not change A [maybe need to elaborate why this is okay?].
- else, let `newIDom = some q`. The loop invariant gives:
  Dom(A, q) = ⋂_{p ∈ predecessors(b)} Dom(A, p).
Let A' = A[b ↦ q], i.e. we are setting b's candidate immediate dominator to q.
By the definition of Dom:
Dom(A', b) = {b} ∪ Dom(A', q).

Note:
The final candidate q has a smaller RPO index than b [LEMMA NEEDED].
Since immediate dominator candidate edges always point to smaller indices,
q's immediate dominator candidate chain cannot contain b.
Updating A at b therefore does not affect Dom(A, q) [LEMMA NEEDED?], so
Dom(A', q) = Dom(A, q).

Therefore,
Dom(A', b)
  = {b} ∪ Dom(A', q)
  = {b} ∪ Dom(A, q)
  = {b} ∪ ⋂_{p ∈ predecessors(b)} Dom(A, p).
where P is all predecessors of b.
-/
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
