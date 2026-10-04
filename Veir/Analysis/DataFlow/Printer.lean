module

public import Veir.Analysis.DataFlow.SparseFact

public section

namespace Veir

/-!
# Dataflow analysis result printing

Dataflow facts have heterogeneous payloads, so a single printer cannot know how
to render every `FactKind`. Each analysis therefore supplies a type erased
`DataFlowPrinter` callback for the anchors and fact payloads it understands.
-/

namespace DataFlowPrinter

/-- Build a value printer for a sparse abstract domain. -/
def sparse
    (name : String)
    (kind : FactKind)
    [SparseFactSpec kind Domain]
    [Bot Domain]
    [ToString Domain]
    (shouldPrint : ValuePtr → WfIRContext OpCode → Bool := fun _ _ => true) :
    DataFlowPrinter :=
  { name
    format? := fun anchor dfCtx irCtx =>
      match anchor with
      | .ValuePtr value =>
        if shouldPrint value irCtx then
          some (toString (SparseFact.getElement kind value dfCtx))
        else
          none
      | _ => none }

end DataFlowPrinter

private def printDataFlowAnchor
    (label : String)
    (anchor : LatticeAnchor)
    (analyses : Array DataFlowAnalysis)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : IO Unit := do
  for analysis in analyses do
    let some printer := analysis.printer?
      | continue
    if let some value := printer.format? anchor dfCtx irCtx then
      IO.println s!"// dataflow.{printer.name} {label} = {value}"

/--
Print selected dataflow facts in IR order.

The traversal exposes block facts, block entry program points, SSA values, and
CFG edges. Each selected analysis's `DataFlowPrinter` chooses which anchors are
meaningful for its fact kind.
-/
partial def printDataFlowFacts
    (op : OperationPtr)
    (analyses : Array DataFlowAnalysis)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : IO Unit := do
  let opName := String.fromUTF8! (IsOpCode.name (op.getOpType! irCtx.raw))

  for i in [0:op.getNumResults! irCtx.raw] do
    printDataFlowAnchor
      s!"{opName} result {i}"
      (.ValuePtr (op.getResult i))
      analyses dfCtx irCtx

  if let some source := (op.get! irCtx.raw).parent then
    for i in [0:op.getNumSuccessors! irCtx.raw] do
      let target := op.getSuccessor! irCtx.raw i
      printDataFlowAnchor
        s!"{opName} successor {i}"
        (.CFGEdge { source, target })
        analyses dfCtx irCtx

  for regionPtr in (op.get! irCtx.raw).regions do
    let region := regionPtr.get! irCtx.raw
    let mut maybeBlock := region.firstBlock
    while let some block := maybeBlock do
      printDataFlowAnchor
        "block"
        (.BlockPtr block)
        analyses dfCtx irCtx
      printDataFlowAnchor
        "block entry"
        (.InsertPoint (InsertPoint.atStart! block irCtx.raw))
        analyses dfCtx irCtx

      for i in [0:block.getNumArguments! irCtx.raw] do
        printDataFlowAnchor
          s!"block argument {i}"
          (.ValuePtr (block.getArgument i))
          analyses dfCtx irCtx

      let mut maybeNestedOp := (block.get! irCtx.raw).firstOp
      while let some nestedOp := maybeNestedOp do
        printDataFlowFacts nestedOp analyses dfCtx irCtx
        maybeNestedOp := (nestedOp.get! irCtx.raw).next

      maybeBlock := (block.get! irCtx.raw).next

end Veir
