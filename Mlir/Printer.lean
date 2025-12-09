import Mlir.Core.Basic
import Mlir.Core.Grind
import Mlir.Ranges

open Mlir

namespace Mlir.Printer

def opName (opType: Nat) : String :=
  match opType with
  | 0 => "builtin.module"
  | 1 => "arith.constant"
  | 2 => "arith.addi"
  | 3 => "return"
  | 4 => "arith.muli"
  | 5 => "arith.andi"
  | 99 => "test.test"
  | _ => "UNREGISTERED"

def printIndent (identFactor: Nat) : IO Unit :=
  match identFactor with
  | 0 => IO.print ""
  | Nat.succ identFactor' => do
    IO.print ("  ")
    printIndent identFactor'

def printValue (ctx : IRContext) (value : ValuePtr) (hval : value.InBounds ctx := by grind) (hx : ctx.FieldsInBounds := by grind) : IO Unit := do
  match value with
  | ValuePtr.opResult opResultPtr =>
    let opResult := opResultPtr.get ctx (by grind)
    let opStruct := opResult.owner.get ctx (by grind)
    if opStruct.results.size = 1 then
      IO.print s!"%{opResult.owner}"
    else
      IO.print s!"%{opResult.owner}_{opResult.index}"
  | ValuePtr.blockArgument blockArgPtr =>
    let blockArg := blockArgPtr.get ctx (by grind)
    IO.print s!"%arg{blockArg.owner}_{blockArg.index}"

def printOpResult (ctx: IRContext) (result: OpResultPtr) (hres : result.InBounds ctx := by grind) (hx : ctx.FieldsInBounds := by grind) : IO Unit := do
  printValue ctx (ValuePtr.opResult result) (by grind) hx

def printOpResults (ctx: IRContext) (op: OperationPtr) (hop : op.InBounds ctx := by grind) (hx : ctx.FieldsInBounds := by grind) : IO Unit := do
  let opStruct := op.get ctx (by grind)
  if h : op.getNumResults! ctx ≠ 0 then
    let res := op.getResult 0
    printValue ctx res
    for h : index in 1...(op.getNumResults! ctx) do
      IO.print ", "
      let res := op.getResult index
      printValue ctx res
    IO.print " = "

def printOpOperands (ctx: IRContext) (op: OperationPtr) (hop : op.InBounds ctx := by grind) (hx : ctx.FieldsInBounds := by grind) : IO Unit := do
  let opStruct := op.get ctx (by grind)
  IO.print "("
  if h : op.getNumOperands! ctx ≠ 0 then
    printValue ctx (op.getOperand ctx 0)
    for h : index in 1...(op.getNumOperands! ctx) do
      IO.print ", "
      printValue ctx (op.getOperand ctx index)
  IO.print ")"

mutual
partial def printOpList (ctx: IRContext) (op: OperationPtr) (indent: Nat := 0) (hop : op.InBounds ctx := by grind) (hx : ctx.FieldsInBounds := by grind) : IO Unit := do
  printOperation ctx op indent
  match _ : (op.get ctx).next with
  | some nextOp =>
    printOpList ctx nextOp indent
  | none =>
    pure ()

partial def printRegion (ctx: IRContext) (region: Region) (indent: Nat := 0) (hr : region.FieldsInBounds ctx := by grind) (hx : ctx.FieldsInBounds := by grind) : IO Unit := do
  IO.println "{"
  let block := region.firstBlock
  match _ : region.firstBlock with
  | some blockPtr =>
    printIndent (indent + 1)
    IO.println s!"^{blockPtr}:"
    let block := blockPtr.get ctx
    match _ : block.firstOp with
    | some firstOp =>
      printOpList ctx firstOp (indent + 2)
    | none =>
      pure ()
  | none =>
    pure ()
  IO.println "}"

partial def printRegions (ctx: IRContext) (op: OperationPtr) (indent: Nat := 0)
  hop (hfib : Operation.FieldsInBounds op ctx hop := by grind) (hx : ctx.FieldsInBounds := by grind) : IO Unit := do
  for h : regionPtr in (op.get ctx hop).regions do
    let region := regionPtr.get ctx
    printRegion ctx region indent

partial def printOperation (ctx: IRContext) (op: OperationPtr) (indent: Nat := 0) (hop : op.InBounds ctx := by grind) (hx : ctx.FieldsInBounds := by grind) : IO Unit := do
  let opStruct := op.get ctx
  printIndent indent
  printOpResults ctx op
  IO.print (opName opStruct.opType)
  if opStruct.opType = 1 then
    IO.print s!" {opStruct.properties} "
  else
    printOpOperands ctx op
  if opStruct.regions.size > 0 then
    IO.print " "
    printRegions ctx op indent (by grind)
  IO.println ""
end

partial def printModule (ctx: IRContext) (op: OperationPtr) (hop : op.InBounds ctx) (hx : ctx.FieldsInBounds) : IO Unit := do
  printOperation ctx op
