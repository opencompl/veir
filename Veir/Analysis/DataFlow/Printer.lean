module

public import Veir.Analysis.DataFlow.SparseFact

public section

namespace Veir

/-!
# Dataflow analysis result printing

Dataflow facts have heterogeneous payloads, so a single printer cannot know how
to render every `FactKind`. `DataFlowFactPrinter` type-erases that final step:
the framework walks lattice anchors once, while each analysis supplies a small
callback for the anchors and fact payloads it understands.
-/

/-- The IR role of an anchor visited by the dataflow result printer. -/
inductive DataFlowPrintPointKind where
  | block
  | blockEntry
  | value
  | operationExit
  | cfgEdge
deriving BEq, DecidableEq

/-- A named lattice anchor encountered during deterministic IR traversal. -/
structure DataFlowPrintPoint where
  kind : DataFlowPrintPointKind
  anchor : LatticeAnchor
  label : String

/--
Type-erased rendering for one family of dataflow facts.

Returning `none` means that the printer does not apply to this kind of anchor.
-/
structure DataFlowFactPrinter where
  name : String
  print? :
    DataFlowPrintPoint → DataFlowContext → WfIRContext OpCode → Option String

namespace DataFlowFactPrinter

/--
Build a printer for a fact kind, using its default fact when no state was stored
at a supported anchor.
-/
def ofFact
    (name : String)
    (kind : FactKind)
    [FactSpec kind]
    (supportedPoints : Array DataFlowPrintPointKind)
    (format : Fact kind → String) : DataFlowFactPrinter :=
  { name
    print? := fun point dfCtx _ =>
      if supportedPoints.contains point.kind then
        some (format (dfCtx.getOrMkFact kind point.anchor))
      else
        none }

/-- Build a value printer for a sparse abstract domain. -/
def sparse
    (name : String)
    (kind : FactKind)
    [SparseFactSpec kind Domain]
    [Bot Domain]
    [ToString Domain]
    (shouldPrint : ValuePtr → WfIRContext OpCode → Bool := fun _ _ => true) :
    DataFlowFactPrinter :=
  { name
    print? := fun point dfCtx irCtx =>
      match point.kind, point.anchor with
      | .value, .ValuePtr value =>
        if shouldPrint value irCtx then
          some (toString (SparseFact.getElement kind value dfCtx))
        else
          none
      | _, _ => none }

end DataFlowFactPrinter

private def printDataFlowPoint
    (point : DataFlowPrintPoint)
    (printers : Array DataFlowFactPrinter)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : IO Unit := do
  for printer in printers do
    if let some value := printer.print? point dfCtx irCtx then
      IO.println s!"// dataflow.{printer.name} {point.label} = {value}"

/--
Print selected dataflow facts in IR order.

The traversal exposes block facts, block-entry program points, SSA values,
operation-exit program points, and CFG edges. A `DataFlowFactPrinter` chooses
which of those anchors are meaningful for its fact kind.
-/
partial def printDataFlowFacts
    (op : OperationPtr)
    (printers : Array DataFlowFactPrinter)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : IO Unit := do
  let opName := String.fromUTF8! (IsOpCode.name (op.getOpType! irCtx.raw))

  for i in [0:op.getNumResults! irCtx.raw] do
    printDataFlowPoint
      { kind := .value
        anchor := .ValuePtr (op.getResult i)
        label := s!"{opName} result {i}" }
      printers dfCtx irCtx

  if let some point := InsertPoint.after? op irCtx.raw then
    printDataFlowPoint
      { kind := .operationExit
        anchor := .InsertPoint point
        label := s!"after {opName}" }
      printers dfCtx irCtx

  if let some source := (op.get! irCtx.raw).parent then
    for i in [0:op.getNumSuccessors! irCtx.raw] do
      let target := op.getSuccessor! irCtx.raw i
      printDataFlowPoint
        { kind := .cfgEdge
          anchor := .CFGEdge { source, target }
          label := s!"{opName} successor {i}" }
        printers dfCtx irCtx

  for regionPtr in (op.get! irCtx.raw).regions do
    let region := regionPtr.get! irCtx.raw
    let mut maybeBlock := region.firstBlock
    while let some block := maybeBlock do
      printDataFlowPoint
        { kind := .block
          anchor := .BlockPtr block
          label := "block" }
        printers dfCtx irCtx
      printDataFlowPoint
        { kind := .blockEntry
          anchor := .InsertPoint (InsertPoint.atStart! block irCtx.raw)
          label := "block entry" }
        printers dfCtx irCtx

      for i in [0:block.getNumArguments! irCtx.raw] do
        printDataFlowPoint
          { kind := .value
            anchor := .ValuePtr (block.getArgument i)
            label := s!"block argument {i}" }
          printers dfCtx irCtx

      let mut maybeNestedOp := (block.get! irCtx.raw).firstOp
      while let some nestedOp := maybeNestedOp do
        printDataFlowFacts nestedOp printers dfCtx irCtx
        maybeNestedOp := (nestedOp.get! irCtx.raw).next

      maybeBlock := (block.get! irCtx.raw).next

end Veir
