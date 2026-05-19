module

public import Veir.Analysis.DataFlowFramework
public import Std.Data.HashSet
public import Std.Data.HashMap

public section

namespace Veir

open Std (HashMap HashSet)

namespace BlockPtr

def getDominatorFact? [FactSpec .dominator] (block : BlockPtr) (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Option DominatorFact :=
  dfCtx.getFact? .dominator (.InsertPoint (InsertPoint.atStart! block irCtx))

def getIDom? [FactSpec .dominator] (block : BlockPtr) (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Option BlockPtr :=
  match block.getDominatorFact? dfCtx irCtx with
  | some fact => fact.iDom
  | none => none

def getDoms? [FactSpec .dominator] (block : BlockPtr) (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Option (HashSet BlockPtr) :=
  match block.getDominatorFact? dfCtx irCtx with
  | none => none
  | some fact =>
    Id.run do
      let mut doms : HashSet BlockPtr := (∅ : HashSet BlockPtr).insert block
      let mut current := fact.iDom
      while current.isSome do
        let dom := current.get!
        if dom == block then
          return some doms
        doms := doms.insert dom
        let next := dom.getIDom? dfCtx irCtx
        if next == some dom then
          return some doms
        current := next
      some doms

end BlockPtr

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

/-- Get the immediate dominator for a block. -/
def getIDom? (block : BlockPtr) (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Option BlockPtr :=
  block.getIDom? dfCtx irCtx

/-- Walk up the dominator tree via iDoms to gather the dominators for a block. -/
def getDoms? (block : BlockPtr) (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Option (HashSet BlockPtr) :=
  block.getDoms? dfCtx irCtx

end DominatorFact

namespace RegionPtr

def getRegionMetadataFact? [FactSpec .regionMetadata] (region : RegionPtr) (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Option RegionMetadataFact :=
  match (region.get! irCtx).firstBlock with
  | some entry =>
    dfCtx.getFact? .regionMetadata (.InsertPoint (InsertPoint.atStart! entry irCtx))
  | none =>
    none

end RegionPtr

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

def get? (dfCtx : DataFlowContext) (region : RegionPtr)
    (irCtx : IRContext OpCode) : Option RegionMetadataFact :=
  region.getRegionMetadataFact? dfCtx irCtx

end RegionMetadataFact

namespace DominanceAnalysis

def kind : AnalysisKind :=
  .dominance

/-- Get the lattice anchor of a given block. -/
private def blockEntryAnchor (block : BlockPtr) (irCtx : IRContext OpCode) : LatticeAnchor :=
  .InsertPoint (InsertPoint.atStart! block irCtx)

/-- Get the successors of a given block. -/
private def successorsInRegion
    (block : BlockPtr)
    (region : RegionPtr)
    (irCtx : IRContext OpCode) : Array BlockPtr :=
  match (block.get! irCtx).lastOp with
  | none =>
    #[]
  | some term =>
    Id.run do
      let mut succs := #[]
      for i in [0:term.getNumSuccessors! irCtx] do
        let succ := term.getSuccessor! irCtx i
        if (succ.get! irCtx).parent == some region then
          succs := succs.push succ
      succs

/--
The returned array is CFG in postorder, and the map assigns each block a
postorder index used by `intersect`.
-/
private def collectPostOrder
    (region : RegionPtr)
    (irCtx : IRContext OpCode) : Array BlockPtr × HashMap BlockPtr Nat :=
  match (region.get! irCtx).firstBlock with
  | none =>
    (#[], {})
  | some entry =>
    Id.run do
      let mut worklist : Array (BlockPtr × Bool) := #[(entry, false)]
      let mut seen : HashSet BlockPtr := ∅
      let mut postOrder : Array BlockPtr := #[]
      let mut postOrderIndex : HashMap BlockPtr Nat := {}

      while !worklist.isEmpty do
        let (block, visited) := worklist.back!
        worklist := worklist.pop

        if visited then
          let index := postOrder.size
          postOrder := postOrder.push block
          postOrderIndex := postOrderIndex.insert block index
        else if seen.contains block then
          continue
        else
          seen := seen.insert block
          worklist := worklist.push (block, true)

          for succ in successorsInRegion block region irCtx do
            if !seen.contains succ then
              worklist := worklist.push (succ, false)
      (postOrder, postOrderIndex)

/- Initialize the dominators in post order and enqueue them in reverse post order. -/
private def initializeRegion
    (region : RegionPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext :=
  match (region.get! irCtx).firstBlock with
  | none =>
    dfCtx
  | some entry =>
    Id.run do
      let (postOrder, postOrderIndex) := collectPostOrder region irCtx
      let reversePostOrder := postOrder.reverse
      let mut dfCtx :=
        dfCtx.modifyFact .regionMetadata (blockEntryAnchor entry irCtx) (fun fact =>
          fact.setPostOrderIndex postOrderIndex)

      for block in postOrder do
        let mut dependents := #[]
        for succ in successorsInRegion block region irCtx do
          dependents := dependents.push (InsertPoint.atStart! succ irCtx, kind)
        dfCtx := dfCtx.modifyFact .dominator (blockEntryAnchor block irCtx) (fun fact =>
          (fact.setDependents dependents).setIDom
            (if block == entry then some entry else none))

      for block in reversePostOrder do
        match blockEntryAnchor block irCtx with
        | .InsertPoint point =>
          dfCtx := dfCtx.enqueue (point, kind)
        | _ =>
          unreachable!

      dfCtx

/-- Recursively initialize the analysis on nested regions. -/
partial def initializeRecursively
    (op : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  let mut dfCtx := dfCtx

  for i in [0:op.getNumRegions! irCtx] do
    let region := op.getRegion! irCtx i
    dfCtx := initializeRegion region dfCtx irCtx

    let regionData := region.get! irCtx
    let mut maybeBlock := regionData.firstBlock
    while hBlock : maybeBlock.isSome do
      let block := maybeBlock.get hBlock
      let mut maybeOp := (block.get! irCtx).firstOp
      while hOp : maybeOp.isSome do
        let nestedOp := maybeOp.get hOp
        dfCtx := initializeRecursively nestedOp dfCtx irCtx
        maybeOp := (nestedOp.get! irCtx).next
      maybeBlock := (block.get! irCtx).next

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
  while finger1 != finger2 do
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
    (irCtx : IRContext OpCode) : Option BlockPtr :=
  let region := ((block.get! irCtx).parent).get!
  let entry := ((region.get! irCtx).firstBlock).get!
  match region.getRegionMetadataFact? dfCtx irCtx with
  | none =>
    none
  | some metadata =>
    if block == entry then
      some entry
    else
      Id.run do
        let mut maybePredUse := (block.get! irCtx).firstUse
        let mut newIDom : Option BlockPtr := none

        while hUse : maybePredUse.isSome do
          let predUse := maybePredUse.get hUse
          let predUseStruct := predUse.get! irCtx
          maybePredUse := predUseStruct.nextUse
          let predOp := predUseStruct.owner
          let some predBlock := (predOp.get! irCtx).parent
            | continue
          if (predBlock.get! irCtx).parent != some region then
            continue
          let some _ := predBlock.getIDom? dfCtx irCtx
            | continue
          newIDom := match newIDom with
            | none => some predBlock
            | some current => some (intersect predBlock current metadata.postOrderIndex dfCtx irCtx)

        newIDom

def visit
    (point : InsertPoint)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext :=
  if !point.isBlockStart irCtx then
    dfCtx
  else
    let block := (point.block! irCtx).get!
    match computeImmediateDominator block dfCtx irCtx with
    | none => dfCtx
    | some newIDom =>
      let anchor := blockEntryAnchor block irCtx
      dfCtx.modifyFactAndPropagate .dominator anchor (fun fact =>
        (fact.setIDom (some newIDom), some newIDom != fact.iDom)) irCtx

/-- Get a block's immediate dominator. -/
def immediateDominator?
    (block : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Option BlockPtr :=
  match block.getIDom? dfCtx irCtx with
  | some iDom => if iDom == block then none else some iDom
  | none => none

/-- Recurse up the dominator tree to see if `dominator` dominates `block`. -/
def dominates
    (dominator block : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Bool :=
  if dominator == block then
    (block.getDominatorFact? dfCtx irCtx).isSome
  else
    match block.getDominatorFact? dfCtx irCtx with
    | none => false
    | some fact =>
      Id.run do
        let mut current := fact.iDom
        while current.isSome do
          let candidate := current.get!
          if candidate == dominator then
            return true
          let next := candidate.getIDom? dfCtx irCtx
          if next == some candidate then
            return false
          current := next
        false

/-- Same thing as `dominates` except a block dominating itself doesn't count. -/
def strictlyDominates
    (dominator block : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Bool :=
  dominator != block && dominates dominator block dfCtx irCtx

end DominanceAnalysis

def DominanceAnalysis : DataFlowAnalysis :=
  { kind := DominanceAnalysis.kind
    init := DominanceAnalysis.init
    visit := DominanceAnalysis.visit }

end Veir
