module

public import Veir.IR.Basic
public import Veir.Dialects.Builtin.OpInfo
public import Veir.Printer.CustomPrinting

import Veir.Rewriter.Basic

open Veir

public section

namespace Veir

/-- Options controlling operation printing. -/
structure PrinterOptions where
  /-- Print operations in generic form instead of using custom printers. -/
  printGenericOpForm : Bool := false
deriving Inhabited, DecidableEq, Repr

end Veir

namespace Veir.Printer

variable {OpCode : Type} [IsOpCode OpCode] [HasDialect OpCode Builtin]
  [HasCustomPrinting OpCode OpCode]

namespace OpPrinter

private def increaseIndent : OpPrinter OpCode Unit :=
  modify (· + 1)

private def decreaseIndent : OpPrinter OpCode Unit :=
  modify fun n => if n == 0 then 0 else n - 1

private def printIndent : OpPrinter OpCode Unit := do
  let n ← (get : OpPrinter OpCode Nat)
  for _ in List.range n do
    printString "  "

private def printOpResults (op : OperationPtr) : OpPrinter OpCode Unit := do
  let ctx ← getContext
  if op.getNumResults! ctx != 0 then
    printString s!"%{op.id}"
    if op.getNumResults! ctx > 1 then
      printString s!":{op.getNumResults! ctx}"
    printString " = "

private def printOpOperands (op : OperationPtr) : OpPrinter OpCode Unit := do
  let ctx ← getContext
  printString "("
  if op.getNumOperands! ctx != 0 then
    printOperand (op.getOperand! ctx 0)
    for index in List.range (op.getNumOperands! ctx - 1) do
      printString ", "
      printOperand (op.getOperand! ctx (index + 1))
  printString ")"

private def printBlockOperands (op : OperationPtr) : OpPrinter OpCode Unit := do
  let ctx ← getContext
  if op.getNumSuccessors! ctx == 0 then return
  printString " ["
  printSuccessor (op.getSuccessor! ctx 0)
  for index in List.range (op.getNumSuccessors! ctx - 1) do
    printString ", "
    printSuccessor (op.getSuccessor! ctx (index + 1))
  printString "]"

end OpPrinter

private def printOpAttrDict (op : OperationPtr) : OpPrinter OpCode Unit := do
  let ctx ← OpPrinter.getContext
  let attrs := (op.get! ctx).attrs
  if attrs.entries.size == 0 then return
  OpPrinter.printString " "
  -- `attrs` already prints as `{ "k" = v, ... }` via its Repr
  OpPrinter.printString s!"{attrs}"

private def printOpProperties (op : OperationPtr) : OpPrinter OpCode Unit := do
  let ctx ← OpPrinter.getContext
  let opType := (op.get! ctx).opType
  let properties := op.getProperties! ctx opType
  let attrDict := IsOpCode.toAttrDict opType properties
  if attrDict.size == 0 then return
  OpPrinter.printString " <"
  OpPrinter.printString s!"{DictionaryAttr.fromArray attrDict.toArray}"
  OpPrinter.printString ">"

mutual
/-- Print an operation and its siblings. -/
private partial def printOpList (op : OperationPtr) (options : PrinterOptions) : OpPrinter OpCode Unit := do
  printOperation op options
  let ctx ← OpPrinter.getContext
  match (op.get! ctx).next with
  | some nextOp => printOpList nextOp options
  | none => pure ()

/-- Print a block `^id(%args):` and its ops. -/
private partial def printBlock (block : BlockPtr) (options : PrinterOptions) : OpPrinter OpCode Unit := do
  let ctx ← OpPrinter.getContext
  OpPrinter.printIndent
  OpPrinter.printString s!"^{block.id}("
  for i in List.range (block.getNumArguments! ctx) do
    if i != 0 then OpPrinter.printString ", "
    -- Use region-argument printing for block args
    let argPtr := block.getArgument i
    -- BlockArgumentPtr -> ValuePtr
    let value : ValuePtr := ValuePtr.blockArgument argPtr
    OpPrinter.printRegionArgument value
    OpPrinter.printString s!" : {(argPtr.get! ctx).type}"
  OpPrinter.printString "):"
  OpPrinter.printNewline
  match (block.get! ctx).firstOp with
  | some firstOp =>
    OpPrinter.increaseIndent
    printOpList firstOp options
    OpPrinter.decreaseIndent
  | none => pure ()

/-- Print a block and its siblings. -/
private partial def printBlockList (block : BlockPtr) (options : PrinterOptions) : OpPrinter OpCode Unit := do
  printBlock block options
  let ctx ← OpPrinter.getContext
  match (block.get! ctx).next with
  | some nextBlock => printBlockList nextBlock options
  | none => pure ()

/-- Print a region `{ ... }`. If `printEntryBlockArgs` is false, elide the entry block's label and arguments. -/
private partial def printRegionImpl (region : Region) (printEntryBlockArgs : Bool) (options : PrinterOptions) : OpPrinter OpCode Unit := do
  let ctx ← OpPrinter.getContext
  OpPrinter.printString "{"
  match region.firstBlock with
  | none =>
    OpPrinter.printString "}"
  | some blockPtr =>
    if !printEntryBlockArgs then
      -- Elide entry block header: print entry block's ops, then trailing blocks
      OpPrinter.printNewline
      OpPrinter.increaseIndent
      match (blockPtr.get! ctx).firstOp with
      | some firstOp => printOpList firstOp options
      | none => pure ()
      match (blockPtr.get! ctx).next with
      | some nextBlock => printBlockList nextBlock options
      | none => pure ()
      OpPrinter.decreaseIndent
      OpPrinter.printIndent
      OpPrinter.printString "}"
    else
      OpPrinter.printNewline
      OpPrinter.increaseIndent
      printBlockList blockPtr options
      OpPrinter.decreaseIndent
      OpPrinter.printIndent
      OpPrinter.printString "}"

/-- Print all regions of an operation `( {..}, {..} )`. -/
private partial def printRegions (op : OperationPtr) (options : PrinterOptions) : OpPrinter OpCode Unit := do
  let ctx ← OpPrinter.getContext
  if op.getNumRegions! ctx == 0 then return
  OpPrinter.printString "("
  for i in List.range (op.getNumRegions! ctx - 1) do
    let region := (op.getRegion! ctx i).get! ctx
    printRegionImpl region true options
    OpPrinter.printString ", "
  let lastRegion := (op.getRegion! ctx (op.getNumRegions! ctx - 1)).get! ctx
  printRegionImpl lastRegion true options
  OpPrinter.printString ")"

/-- Print a single operation, dispatching to a custom printer when available and not in generic form. -/
private partial def printOperation (op : OperationPtr) (options : PrinterOptions) : OpPrinter OpCode Unit := do
  let ctx ← OpPrinter.getContext
  let opStruct := op.get! ctx
  let opType := opStruct.opType
  if !options.printGenericOpForm then
    match HasCustomPrinting.customPrinter?
      (Dialect := OpCode) (GlobalOpCode := OpCode) opType with
    | some cp =>
        OpPrinter.printIndent
        OpPrinter.printOpResults op
        OpPrinter.printString s!"{String.fromUTF8! (IsOpCode.name opType)}"
        cp op
        OpPrinter.printNewline
        return
    | none => pure ()
  -- Generic form
  OpPrinter.printIndent
  OpPrinter.printOpResults op
  let nameBytes : ByteArray :=
    match toDialect? Builtin opStruct.opType with
    | some Builtin.unregistered =>
      (op.getProperties! ctx Builtin.unregistered).opName
    | _ => IsOpCode.name opStruct.opType
  OpPrinter.printString s!"\"{String.fromUTF8! nameBytes}\""
  OpPrinter.printOpOperands op
  OpPrinter.printBlockOperands op
  printOpProperties op
  if op.getNumRegions! ctx > 0 then
    OpPrinter.printString " "
    printRegions op options
  printOpAttrDict op
  OpPrinter.printString " : "
  OpPrinter.printFunctionalType op
  OpPrinter.printNewline
end

/-- Build the reader context used by custom printers. -/
private partial def makeOpPrinterContext (ctx : IRContext OpCode) (options : PrinterOptions) : OpPrinterContext OpCode :=
  OpPrinterContext.create ctx fun region printEntryBlockArgs =>
    ReaderT.run (printRegionImpl region printEntryBlockArgs options)
      (makeOpPrinterContext ctx options)

/-- Top-level entry: print a module operation. -/
def printModule (ctx : IRContext OpCode) (op : OperationPtr) (options : PrinterOptions := {}) : IO Unit := do
  OpPrinter.run (makeOpPrinterContext ctx options) 0 (printOperation op options)

