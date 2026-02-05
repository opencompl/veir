import Veir.IR.Basic
import Veir.IR.Grind
import Veir.Rewriter.Basic

open Veir

namespace Veir.Printer

def opName (opType: Nat) : String :=
  match opType with
  | 0 => "builtin.module"
  | 1 => "arith.constant"
  | 2 => "arith.addi"
  | 3 => "return"
  | 4 => "arith.muli"
  | 5 => "arith.andi"
  | 6 => "arith.subi"
  | 99 => "test.test"
  | _ => "UNREGISTERED"

def printIndent (identFactor: Nat) : IO Unit :=
  match identFactor with
  | 0 => IO.print ""
  | Nat.succ identFactor' => do
    IO.print ("  ")
    printIndent identFactor'

def printValue (ctx : IRContext) (value : ValuePtr) : IO Unit := do
  match value with
  | ValuePtr.opResult opResultPtr =>
    let opResult := opResultPtr.get! ctx
    let opStruct := opResult.owner.get! ctx
    if opStruct.results.size = 1 then
      IO.print s!"%{opResult.owner.id}"
    else
      IO.print s!"%{opResult.owner.id}_{opResult.index}"
  | ValuePtr.blockArgument blockArgPtr =>
    let blockArg := blockArgPtr.get! ctx
    IO.print s!"%arg{blockArg.owner.id}_{blockArg.index}"

def printOpResult (ctx: IRContext) (result: OpResultPtr) : IO Unit := do
  printValue ctx (ValuePtr.opResult result)

def printOpResults (ctx: IRContext) (op: OperationPtr) : IO Unit := do
  if op.getNumResults! ctx ≠ 0 then
    let res := op.getResult 0
    printValue ctx res
    for index in 1...(op.getNumResults! ctx) do
      IO.print ", "
      let res := op.getResult index
      printValue ctx res
    IO.print " = "

def printOpOperands (ctx: IRContext) (op: OperationPtr) : IO Unit := do
  IO.print "("
  if op.getNumOperands! ctx ≠ 0 then
    printValue ctx (op.getOperand! ctx 0)
    for index in 1...(op.getNumOperands! ctx) do
      IO.print ", "
      printValue ctx (op.getOperand! ctx index)
  IO.print ")"

def printOperationType (ctx : IRContext) (op : OperationPtr) : IO Unit := do
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
    IO.print s!"{resType}"
    return
  IO.print "("
  let firstResType := ((op.getResult 0).get! ctx).type
  IO.print s!"{firstResType}"
  for index in 1...(op.getNumResults! ctx) do
    let resType := ((op.getResult index).get! ctx).type
    IO.print s!", {resType}"
  IO.print ")"

def printBlockOperands (ctx: IRContext) (op: OperationPtr) : IO Unit := do
  if op.getNumSuccessors! ctx = 0 then return
  IO.print " ["
  IO.print s!"^{(op.getSuccessor! ctx 0).id}"
  for index in 1...(op.getNumSuccessors! ctx) do
    IO.print s!", ^{(op.getSuccessor! ctx index).id}"
  IO.print "]"

mutual
partial def printOpList (ctx: IRContext) (op: OperationPtr) (indent: Nat := 0) : IO Unit := do
  printOperation ctx op indent
  match _ : (op.get! ctx).next with
  | some nextOp =>
    printOpList ctx nextOp indent
  | none =>
    pure ()

partial def printBlock (ctx: IRContext) (block: BlockPtr) (indent: Nat := 0) : IO Unit := do
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
    printOpList ctx firstOp (indent + 1)
  | none =>
    pure ()

partial def printBlockList (ctx: IRContext) (block: BlockPtr) (indent: Nat := 0) : IO Unit := do
  printBlock ctx block indent
  match _ : (block.get! ctx).next with
  | some nextBlock =>
    printBlockList ctx nextBlock indent
  | none =>
    pure ()

partial def printRegion (ctx: IRContext) (region: Region) (indent: Nat := 0) : IO Unit := do
  IO.print "{"
  match region.firstBlock with
  | none =>
    IO.print "}"
  | some blockPtr =>
    IO.println ""
    printBlockList ctx blockPtr (indent + 1)
    IO.print "}"

partial def printRegions (ctx: IRContext) (op: OperationPtr) (indent: Nat := 0) : IO Unit := do
  if op.getNumRegions! ctx = 0 then return
  IO.print "("
  for i in 0...((op.getNumRegions! ctx) - 1) do
    let region := (op.getRegion! ctx i).get! ctx
    printRegion ctx region indent
    IO.print ", "
  printRegion ctx ((op.getRegion! ctx (op.getNumRegions! ctx - 1)).get! ctx) indent
  IO.print ")"

partial def printOperation (ctx: IRContext) (op: OperationPtr) (indent: Nat := 0) : IO Unit := do
  let opStruct := op.get! ctx
  printIndent indent
  printOpResults ctx op
  IO.print s!"\"{String.fromUTF8! opStruct.opType.name}\""
  printOpOperands ctx op
  if opStruct.opType = .arith_constant then
    IO.print s!" \{ \"value\" = {opStruct.properties} : i32 }"
  else
    printBlockOperands ctx op
  if op.getNumRegions! ctx > 0 then
    IO.print " "
    printRegions ctx op indent
  printOperationType ctx op
  IO.println ""
end

partial def printModule (ctx: IRContext) (op: OperationPtr) : IO Unit := do
  printOperation ctx op
