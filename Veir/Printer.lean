module

public import Veir.IR.Basic
public import Veir.Dialects.Builtin.OpInfo
public import Veir.GlobalOpInfo
public import Veir.Printer.Basic
public import Veir.OpPrinters

import Veir.Rewriter.Basic

open Veir

public section

namespace Veir.Printer

variable {OpCode : Type} [IsOpCode OpCode] [HasDialect OpCode Builtin] [HasCustomPrinting OpCode]

def printIndent (identFactor: Nat) : IO Unit :=
  match identFactor with
  | 0 => IO.print ""
  | Nat.succ identFactor' => do
    IO.print ("  ")
    printIndent identFactor'

def printValue (ctx : IRContext OpCode) (value : ValuePtr) : IO Unit := do
  match value with
  | ValuePtr.opResult opResultPtr =>
    let opResult := opResultPtr.get! ctx
    let opStruct := opResult.owner.get! ctx
    if opStruct.results.size = 1 then
      IO.print s!"%{opResult.owner.id}"
    else
      IO.print s!"%{opResult.owner.id}#{opResult.index}"
  | ValuePtr.blockArgument blockArgPtr =>
    let blockArg := blockArgPtr.get! ctx
    IO.print s!"%arg{blockArg.owner.id}_{blockArg.index}"

def printOpResults (ctx: IRContext OpCode) (op: OperationPtr) : IO Unit := do
  if op.getNumResults! ctx ≠ 0 then
    IO.print s!"%{op.id}"
    if op.getNumResults! ctx > 1 then
      IO.print s!":{op.getNumResults! ctx}"
    IO.print " = "

def printOpOperands (ctx: IRContext OpCode) (op: OperationPtr) : IO Unit := do
  IO.print "("
  if op.getNumOperands! ctx ≠ 0 then
    printValue ctx (op.getOperand! ctx 0)
    for index in 1...(op.getNumOperands! ctx) do
      IO.print ", "
      printValue ctx (op.getOperand! ctx index)
  IO.print ")"

def printOperationType (ctx : IRContext OpCode) (op : OperationPtr) : IO Unit := do
  -- Print operand types
  IO.print " : ("
  if op.getNumOperands! ctx ≠ 0 then
    let firstOpType := (op.getOperand! ctx 0).getType! ctx
    IO.print s!"{firstOpType}"
    for index in 1...(op.getNumOperands! ctx) do
      let opType := (op.getOperand! ctx index).getType! ctx
      IO.print s!", {opType}"
  IO.print ") -> "

  -- Print result types
  if op.getNumResults! ctx = 0 then
    IO.print "()"
    return
  if op.getNumResults! ctx = 1 then
    let resType := ((op.getResult 0).get! ctx).type
    match resType.val with
    | .functionType _ => IO.print s!"({resType})"
    | _ => IO.print s!"{resType}"
    return
  IO.print "("
  let firstResType := ((op.getResult 0).get! ctx).type
  IO.print s!"{firstResType}"
  for index in 1...(op.getNumResults! ctx) do
    let resType := ((op.getResult index).get! ctx).type
    IO.print s!", {resType}"
  IO.print ")"

def printBlockOperands (ctx: IRContext OpCode) (op: OperationPtr) : IO Unit := do
  if op.getNumSuccessors! ctx = 0 then return
  IO.print " ["
  IO.print s!"^{(op.getSuccessor! ctx 0).id}"
  for index in 1...(op.getNumSuccessors! ctx) do
    IO.print s!", ^{(op.getSuccessor! ctx index).id}"
  IO.print "]"

def printAttrDictEntry (key : String) (value : Attribute) : IO Unit := do
  if value = UnitAttr.mk then
    IO.print s!"\"{key}\""
  else
    IO.print s!"\"{key}\" = {value}"

def printOpAttrDict (ctx : IRContext OpCode) (op : OperationPtr) : IO Unit := do
  let attrs := (op.get! ctx).attrs
  if attrs.entries.size = 0 then return
  IO.print " "
  IO.print (op.get! ctx).attrs

def printOpProperties (ctx : IRContext OpCode) (op : OperationPtr) : IO Unit := do
  let opType := (op.get! ctx).opType
  let properties := op.getProperties! ctx opType
  let attrDict := IsOpCode.toAttrDict opType properties
  if attrDict.size = 0 then return
  IO.print " <"
  IO.print (DictionaryAttr.fromArray attrDict.toArray)
  IO.print ">"

mutual
partial def printOpList (ctx: IRContext OpCode) (op: OperationPtr) (pretty : Bool := false) (indent: Nat := 0) : IO Unit := do
  printOperation ctx op pretty indent
  match _ : (op.get! ctx).next with
  | some nextOp =>
    printOpList ctx nextOp pretty indent
  | none =>
    pure ()

partial def printBlock (ctx: IRContext OpCode) (block: BlockPtr) (pretty : Bool := false) (indent: Nat := 0) : IO Unit := do
  printIndent indent
  IO.print s!"^{block.id}("
  for i in 0...(block.getNumArguments! ctx) do
    let arg := block.getArgument i
    IO.print s!"%arg{block.id}_{i} : {(arg.get! ctx).type}"
    if i + 1 < block.getNumArguments! ctx then
      IO.print ", "
  IO.println s!"):"
  match _ : (block.get! ctx).firstOp with
  | some firstOp =>
    printOpList ctx firstOp pretty (indent + 1)
  | none =>
    pure ()

partial def printBlockList (ctx: IRContext OpCode) (block: BlockPtr) (pretty : Bool := false) (indent: Nat := 0) : IO Unit := do
  printBlock ctx block pretty indent
  match _ : (block.get! ctx).next with
  | some nextBlock =>
    printBlockList ctx nextBlock pretty indent
  | none =>
    pure ()

partial def printRegion (ctx: IRContext OpCode) (region: Region) (pretty : Bool := false) (indent: Nat := 0) : IO Unit := do
  IO.print "{"
  match region.firstBlock with
  | none =>
    printIndent indent
    IO.print "}"
  | some blockPtr =>
    IO.println ""
    printBlockList ctx blockPtr pretty (indent + 1)
    printIndent indent
    IO.print "}"

partial def printRegions (ctx: IRContext OpCode) (op: OperationPtr) (pretty : Bool := false) (indent: Nat := 0) : IO Unit := do
  if op.getNumRegions! ctx = 0 then return
  IO.print "("
  for i in 0...((op.getNumRegions! ctx) - 1) do
    let region := (op.getRegion! ctx i).get! ctx
    printRegion ctx region pretty indent
    IO.print ", "
  printRegion ctx ((op.getRegion! ctx (op.getNumRegions! ctx - 1)).get! ctx) pretty indent
  IO.print ")"

partial def printOperation (ctx: IRContext OpCode) (op: OperationPtr) (pretty : Bool := false) (indent: Nat := 0) : IO Unit := do
  let opStruct := op.get! ctx
  let opType := opStruct.opType
  /- Custom (non-generic) syntax dispatch. When `pretty` is set, operations
     whose dialect registered a custom printer (via `HasCustomPrinting`) are
     printed in their custom form; everything else falls through to the
     generic form. -/
  if pretty then
    match HasCustomPrinting.customPrinter? opType with
    | some cp =>
        printIndent indent
        printOpResults ctx op
        IO.print s!"{String.fromUTF8! (IsOpCode.name opType)}"
        let env : PrintEnv OpCode :=
          { printValue     := printValue
          , printOpList    := fun ctx op indent => printOpList ctx op pretty indent
          , printBlockList := fun ctx block indent => printBlockList ctx block pretty indent
          , printRegion    := fun ctx region indent => printRegion ctx region pretty indent
          , printIndent    := printIndent }
        cp env ctx op indent
        IO.println ""
        return
    | none => pure ()
  printIndent indent
  printOpResults ctx op
  /- Unregistered operations store their original operation name in the properties. -/
  let nameBytes : ByteArray :=
    match toDialect? Builtin opStruct.opType with
    | some Builtin.unregistered =>
      (op.getProperties! ctx Builtin.unregistered).opName
    | _ => IsOpCode.name opStruct.opType
  IO.print s!"\"{String.fromUTF8! nameBytes}\""
  printOpOperands ctx op
  printBlockOperands ctx op
  printOpProperties ctx op
  if op.getNumRegions! ctx > 0 then
    IO.print " "
    printRegions ctx op pretty indent
  printOpAttrDict ctx op
  printOperationType ctx op
  IO.println ""
end

partial def printModule (ctx: IRContext OpCode) (op: OperationPtr) (pretty : Bool := false) : IO Unit := do
  printOperation ctx op pretty
