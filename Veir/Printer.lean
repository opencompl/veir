module

public import Veir.IR.Basic
public import Veir.Properties
public import Veir.GlobalOpInfo
public import Veir.AssemblyFormat

import Veir.IR.Grind
import Veir.Rewriter.Basic
import Veir.Properties

open Veir

public section

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
  let attrDict := Properties.toAttrDict opType properties
  if attrDict.size = 0 then return
  IO.print " <"
  IO.print (DictionaryAttr.fromArray attrDict.toArray)
  IO.print ">"

/-!
  ## Declarative assembly format printing

  The helpers below interpret a parsed `AssemblyFormat.Format` to print an
  operation in its custom (pretty) syntax. Spacing follows MLIR's convention: a
  space is inserted before each element except where punctuation should hug the
  surrounding tokens.
-/

open Veir.AssemblyFormat in
/-- Literals that should not be preceded by a space (they hug the left token). -/
def Printer.noSpaceBefore (s : String) : Bool := s == ")" || s == "]" || s == ">" || s == "," || s == "("

/-- Literals that suppress the space after them (the next element glues on). -/
def Printer.gluesNext (s : String) : Bool := s == "(" || s == "[" || s == "<"

/-- Emit a literal with MLIR-style spacing; returns the new pending-space flag. -/
def Printer.emitLiteral (s : String) (pending : Bool) : IO Bool := do
  if pending && !Printer.noSpaceBefore s then IO.print " "
  IO.print s
  return !Printer.gluesNext s

/-- The types of all operands of `op`. -/
def Printer.operandTypes (ctx : IRContext OpCode) (op : OperationPtr) : Array TypeAttr := Id.run do
  let mut tys : Array TypeAttr := #[]
  for i in 0...(op.getNumOperands! ctx) do
    tys := tys.push ((op.getOperand! ctx i).getType! ctx)
  return tys

/-- The types of all results of `op`. -/
def Printer.resultTypes (ctx : IRContext OpCode) (op : OperationPtr) : Array TypeAttr := Id.run do
  let mut tys : Array TypeAttr := #[]
  for i in 0...(op.getNumResults! ctx) do
    tys := tys.push (((op.getResult i).get! ctx).type)
  return tys

/-- Print a comma-separated list of operands `%a, %b` (no surrounding parens). -/
def Printer.printOperandsFormat (ctx : IRContext OpCode) (op : OperationPtr) (pending : Bool) : IO Bool := do
  let n := op.getNumOperands! ctx
  if n = 0 then return pending
  if pending then IO.print " "
  printValue ctx (op.getOperand! ctx 0)
  for i in 1...n do
    IO.print ", "
    printValue ctx (op.getOperand! ctx i)
  return true

/-- Print a comma-separated list of types `t1, t2` (no surrounding parens). -/
def Printer.printCommaTypes (tys : Array TypeAttr) (pending : Bool) : IO Bool := do
  if tys.size = 0 then return pending
  if pending then IO.print " "
  IO.print s!"{tys[0]!}"
  for i in 1...tys.size do
    IO.print s!", {tys[i]!}"
  return true

/-- Print a function type `(ins) -> outs`, matching `printOperationType`'s
    result-side conventions (single result is printed without parens). -/
def Printer.printFunctionalTypeBody (ins outs : Array TypeAttr) (pending : Bool) : IO Bool := do
  if pending then IO.print " "
  IO.print "("
  if ins.size ≠ 0 then
    IO.print s!"{ins[0]!}"
    for i in 1...ins.size do
      IO.print s!", {ins[i]!}"
  IO.print ") -> "
  if outs.size = 0 then
    IO.print "()"
  else if outs.size = 1 then
    match outs[0]!.val with
    | .functionType _ => IO.print s!"({outs[0]!})"
    | _ => IO.print s!"{outs[0]!}"
  else
    IO.print "("
    IO.print s!"{outs[0]!}"
    for i in 1...outs.size do
      IO.print s!", {outs[i]!}"
    IO.print ")"
  return true

/-- Print the value of a `$name` variable, looked up first in the operation's
    properties (inherent attributes) and then in its discardable attributes.
    Absent variables print nothing. -/
def Printer.printAttrVar (ctx : IRContext OpCode) (op : OperationPtr) (opType : OpCode)
    (name : String) (pending : Bool) : IO Bool := do
  let key := name.toUTF8
  let props := op.getProperties! ctx opType
  let propDict := Properties.toAttrDict opType props
  let value : Option Attribute :=
    match propDict[key]? with
    | some v => some v
    | none => (((op.get! ctx).attrs).entries.find? (fun e => e.1 = key)).map (·.2)
  match value with
  | none => return pending
  | some v =>
    if pending then IO.print " "
    IO.print (toString v)
    return true

/-- Print the `attr-dict` (or `attr-dict-with-keyword`) directive: the merge of
    inherent properties and discardable attributes, excluding keys consumed by
    `$var`s elsewhere in the format. -/
def Printer.printAttrDictFormat (ctx : IRContext OpCode) (op : OperationPtr) (opType : OpCode)
    (consumed : List String) (withKeyword : Bool) (pending : Bool) : IO Bool := do
  let props := op.getProperties! ctx opType
  let propDict := Properties.toAttrDict opType props
  let mut entries : Array (ByteArray × Attribute) := #[]
  for (k, v) in propDict.toArray do
    if !consumed.contains (String.fromUTF8! k) then
      entries := entries.push (k, v)
  for (k, v) in ((op.get! ctx).attrs).entries do
    if !consumed.contains (String.fromUTF8! k) then
      entries := entries.push (k, v)
  if entries.size = 0 then return pending
  if pending then IO.print " "
  if withKeyword then IO.print "attributes "
  IO.print (DictionaryAttr.fromArray entries)
  return true

/-- Is the anchor element of an optional group "present" (so the group should be
    printed)? Mirrors MLIR: variadic operands/results/regions/successors are
    present when non-empty; an attribute variable is present when its key
    exists. -/
def Printer.isAnchorPresent (ctx : IRContext OpCode) (op : OperationPtr) (opType : OpCode)
    (el : AssemblyFormat.Element) : Bool :=
  match el with
  | .directive .operands => op.getNumOperands! ctx > 0
  | .directive .results => op.getNumResults! ctx > 0
  | .directive .regions => op.getNumRegions! ctx > 0
  | .directive .successors => op.getNumSuccessors! ctx > 0
  | .attrVar name =>
      let key := name.toUTF8
      let props := op.getProperties! ctx opType
      let propDict := Properties.toAttrDict opType props
      propDict.contains key || ((op.get! ctx).attrs).entries.any (fun e => e.1 = key)
  | _ => true

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

/-- Print a single assembly-format element. Returns the new pending-space flag. -/
partial def printFormatElement (ctx : IRContext OpCode) (op : OperationPtr) (opType : OpCode)
    (consumed : List String) (el : AssemblyFormat.Element) (pretty : Bool) (indent : Nat)
    (pending : Bool) : IO Bool := do
  match el with
  | .literal s => Printer.emitLiteral s pending
  | .attrVar name => Printer.printAttrVar ctx op opType name pending
  | .directive .attrDict => Printer.printAttrDictFormat ctx op opType consumed false pending
  | .directive .attrDictWithKeyword => Printer.printAttrDictFormat ctx op opType consumed true pending
  | .directive .operands => Printer.printOperandsFormat ctx op pending
  | .directive .results => return pending
  | .directive (.typeOf .operands) => Printer.printCommaTypes (Printer.operandTypes ctx op) pending
  | .directive (.typeOf .results) => Printer.printCommaTypes (Printer.resultTypes ctx op) pending
  | .directive (.functionalType ins outs) =>
      let insTys := match ins with
        | .operands => Printer.operandTypes ctx op
        | .results => Printer.resultTypes ctx op
      let outTys := match outs with
        | .operands => Printer.operandTypes ctx op
        | .results => Printer.resultTypes ctx op
      Printer.printFunctionalTypeBody insTys outTys pending
  | .directive .regions =>
      let n := op.getNumRegions! ctx
      if n = 0 then return pending
      if pending then IO.print " "
      for i in 0...n do
        if i > 0 then IO.print " "
        printRegion ctx ((op.getRegion! ctx i).get! ctx) pretty indent
      return true
  | .directive .successors =>
      let n := op.getNumSuccessors! ctx
      if n = 0 then return pending
      if pending then IO.print " "
      IO.print s!"^{(op.getSuccessor! ctx 0).id}"
      for i in 1...n do
        IO.print s!", ^{(op.getSuccessor! ctx i).id}"
      return true
  | .optional thenElems anchor elseElems =>
      let present := match thenElems[anchor]? with
        | some a => Printer.isAnchorPresent ctx op opType a
        | none => false
      if present then printFormatElements ctx op opType consumed thenElems pretty indent pending
      else printFormatElements ctx op opType consumed elseElems pretty indent pending

partial def printFormatElements (ctx : IRContext OpCode) (op : OperationPtr) (opType : OpCode)
    (consumed : List String) (elems : Array AssemblyFormat.Element) (pretty : Bool) (indent : Nat)
    (pending : Bool) : IO Bool := do
  let mut p := pending
  for el in elems do
    p ← printFormatElement ctx op opType consumed el pretty indent p
  return p

/-- Print an operation using a declarative assembly format. -/
partial def printWithFormat (ctx : IRContext OpCode) (op : OperationPtr) (opType : OpCode)
    (fmt : AssemblyFormat.Format) (pretty : Bool) (indent : Nat) : IO Unit := do
  let consumed := AssemblyFormat.Format.attrVarNames fmt
  let _ ← printFormatElements ctx op opType consumed fmt pretty indent true
  pure ()

/-- Print a function body region, eliding the entry block's label and arguments
    (they appear in the function signature). -/
partial def printFuncBodyRegion (ctx : IRContext OpCode) (entryPtr : BlockPtr) (pretty : Bool)
    (indent : Nat) : IO Unit := do
  IO.println "{"
  match (entryPtr.get! ctx).firstOp with
  | some firstOp => printOpList ctx firstOp pretty (indent + 1)
  | none => pure ()
  match (entryPtr.get! ctx).next with
  | some nextBlock => printBlockList ctx nextBlock pretty (indent + 1)
  | none => pure ()
  printIndent indent
  IO.print "}"

/-- Custom (pretty) printer for `func.func`, mirroring MLIR's
    `hasCustomAssemblyFormat`. Prints `func.func @name(%args) -> results { body }`. -/
partial def printFuncFunc (ctx : IRContext OpCode) (op : OperationPtr) (pretty : Bool)
    (indent : Nat) : IO Unit := do
  let props := op.getProperties! ctx (.func .func)
  let symName := match props.sym_name with
    | some s => String.fromUTF8! s.value
    | none => ""
  let funcType? : Option FunctionType :=
    match props.extra.entries.find? (fun e => e.1 = "function_type".toUTF8) with
    | some (_, .functionType ft) => some ft
    | _ => none
  IO.print s!"func.func @{symName}("
  match (op.getRegion! ctx 0).get! ctx |>.firstBlock with
  | some entryPtr =>
    let nargs := entryPtr.getNumArguments! ctx
    for i in 0...nargs do
      if i > 0 then IO.print ", "
      let arg := entryPtr.getArgument i
      IO.print s!"%arg{entryPtr.id}_{i}: {(arg.get! ctx).type}"
    IO.print ")"
    let outs := (funcType?.map (·.outputs)).getD #[]
    if outs.size = 1 then
      IO.print s!" -> {outs[0]!}"
    else if outs.size > 1 then
      IO.print " -> ("
      IO.print s!"{outs[0]!}"
      for i in 1...outs.size do
        IO.print s!", {outs[i]!}"
      IO.print ")"
    let extraEntries := props.extra.entries.filter (fun e => e.1 ≠ "function_type".toUTF8)
    if extraEntries.size > 0 then
      IO.print " attributes "
      IO.print (DictionaryAttr.fromArray extraEntries)
    IO.print " "
    printFuncBodyRegion ctx entryPtr pretty indent
  | none =>
    IO.print ") {}"

partial def printOperation (ctx: IRContext OpCode) (op: OperationPtr) (pretty : Bool := false) (indent: Nat := 0) : IO Unit := do
  let opStruct := op.get! ctx
  let opType := opStruct.opType
  /- Custom (pretty) syntax dispatch. Operations with a dedicated hook
     (`func.func`) or a registered declarative assembly format are printed in
     their custom form; everything else falls through to the generic form. -/
  if pretty then
    match opType with
    | .func .func =>
        printIndent indent
        printFuncFunc ctx op pretty indent
        IO.println ""
        return
    | _ =>
      match AssemblyFormat.OpCode.assemblyFormat? opType with
      | some fmt =>
          printIndent indent
          printOpResults ctx op
          IO.print s!"{String.fromUTF8! opType.name}"
          printWithFormat ctx op opType fmt pretty indent
          IO.println ""
          return
      | none => pure ()
  printIndent indent
  printOpResults ctx op
  /- Unregistered operations store their original operation name in the properties. -/
  let nameBytes : ByteArray :=
    match opStruct.opType with
    | .builtin .unregistered =>
      (op.getProperties! ctx (.builtin .unregistered)).opName
    | _ => opStruct.opType.name
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
