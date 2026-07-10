module

public import Veir.IR.Basic
public import Veir.IR.Buffed.Sim
public import Veir.Properties
public import Veir.GlobalOpInfo

import Veir.IR.Grind
import Veir.Rewriter.Basic
import Veir.Properties

open Veir

public section

namespace Veir.Printer

set_option warn.sorry false

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

buffed (def_lemma := false)
def printValueSim (_ctx : Sim.IRContext OpCode) (value : Sim.ValuePtr) : IO Unit := do
  -- TODO: This just uses the raw address as index
  IO.print s!"%{value.impl}"

buffed (def_lemma := false)
def printOpResultsSim (ctx : Sim.IRContext OpCode) (op : Sim.OperationPtr) : IO Unit := do
  if op.getNumResults! ctx ≠ 0 then
    IO.print s!"%{op.getResultPtr! ctx 0 |>.impl}"
    for i in 1...(op.getNumResults! ctx) do
      IO.print s!", %{op.getResultPtr! ctx i |>.impl}"
    IO.print " = "

buffed (def_lemma := false)
def printOpOperandsSim (ctx : Sim.IRContext OpCode) (op : Sim.OperationPtr) : IO Unit := do
  IO.print "("
  if op.getNumOperands! ctx ≠ 0 then
    printValue ctx ((op.getOperandPtr! ctx 0).getValue! ctx)
    for index in 1...(op.getNumOperands! ctx) do
      IO.print ", "
      printValue ctx ((op.getOperandPtr! ctx index).getValue! ctx)
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

buffed (def_lemma := false)
def printOpAttrDictSim (ctx : Sim.IRContext OpCode) (op : Sim.OperationPtr) : IO Unit := do
  let attrs := op.getAttributes! ctx
  if attrs.entries.size = 0 then return
  IO.print " "
  IO.print attrs

def printOpProperties (ctx : IRContext OpCode) (op : OperationPtr) : IO Unit := do
  let opType := (op.get! ctx).opType
  let properties := op.getProperties! ctx opType
  let attrDict := Properties.toAttrDict opType properties
  if attrDict.size = 0 then return
  IO.print " <"
  IO.print (DictionaryAttr.fromArray attrDict.toArray)
  IO.print ">"

mutual
partial def printOpList (ctx: Sim.IRContext OpCode) (op: Sim.OperationPtr) (indent: Nat := 0) : IO Unit := do
  printOperation ctx op indent
  match _ : (op.getNextOp! ctx).toOption with
  | some nextOp =>
    printOpList ctx nextOp indent
  | none =>
    pure ()

partial def printBlock (ctx: Sim.IRContext OpCode) (block: Sim.BlockPtr) (indent: Nat := 0) : IO Unit := do
  printIndent indent
  IO.print s!"^{block.impl}("
  for i in 0...(block.getNumArguments! ctx) do
    let arg := block.getArgumentPtr! ctx i
    IO.print s!"{arg.impl}"
    if i + 1 < block.getNumArguments! ctx then
      IO.print ", "
  IO.println s!"):"
  match _ : (block.getFirstOp! ctx).toOption with
  | some firstOp =>
    printOpList ctx firstOp (indent + 1)
  | none =>
    pure ()

partial def printBlockList (ctx: Sim.IRContext OpCode) (block: Sim.BlockPtr) (indent: Nat := 0) : IO Unit := do
  printBlock ctx block indent
  match _ : (block.getNextBlock! ctx).toOption with
  | some nextBlock =>
    printBlockList ctx nextBlock indent
  | none =>
    pure ()

partial def printRegion (ctx: Sim.IRContext OpCode) (region: Sim.RegionPtr) (indent: Nat := 0) : IO Unit := do
  IO.print "{"
  match (region.getFirstBlock! ctx).toOption with
  | none =>
    printIndent indent
    IO.print "}"
  | some blockPtr =>
    IO.println ""
    printBlockList ctx blockPtr (indent + 1)
    printIndent indent
    IO.print "}"

partial def printRegions (ctx: Sim.IRContext OpCode) (op: Sim.OperationPtr) (indent: Nat := 0) : IO Unit := do
  if op.getNumRegions! ctx = 0 then return
  IO.print "("
  for i in 0...((op.getNumRegions! ctx) - 1) do
    let region := (op.getRegionPtr! ctx i)
    printRegion ctx region indent
    IO.print ", "
  printRegion ctx (op.getRegionPtr! ctx (op.getNumRegions! ctx - 1)) indent
  IO.print ")"

partial def printOperation (ctx: Sim.IRContext OpCode) (op: Sim.OperationPtr) (indent: Nat := 0) : IO Unit := do
  printIndent indent
  printOpResults ctx op
  /- Unregistered operations store their original operation name in the properties. -/
  let nameBytes : ByteArray := (op.getOpType! ctx).name
  IO.print s!"\"{String.fromUTF8! nameBytes}\""
  printOpOperands ctx op
  if op.getNumRegions! ctx > 0 then
    IO.print " "
    printRegions ctx op indent
  printOpAttrDict ctx op
  IO.println ""
end

partial def printModule (ctx: Sim.IRContext OpCode) (op: Sim.OperationPtr) : IO Unit := do
  printOperation ctx op
