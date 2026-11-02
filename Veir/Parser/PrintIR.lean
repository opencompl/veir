module

public import Veir.Parser.BuffedIR

/-!
# Generic-form printer for parsed IR

Prints a buffered IR context in MLIR's generic operation form. Values and blocks are named by
their buffer address, so the output round-trips through the parser.
-/

public section

namespace Veir.Parser.PrintIR

open Veir
open Veir.Buffed

/-- An unused name, so block-argument names stay distinct from result names. -/
private def valueName (value : IR.Value) : String := s!"%v{value.impl}"

private def blockName (block : IR.Block) : String := s!"^b{block.impl}"

private def indent (n : Nat) : String := String.ofList (List.replicate (2 * n) ' ')

/-- Print the properties of an operation, if any. -/
private def propertiesString (ctx : IR.Context) (op : IR.Op) : String :=
  let opType := op.getOpType! ctx
  match HasBuffedProperties.readPropertyAt opType (op.impl + Operation.Offsets.properties) ctx.buf with
  | none => ""
  | some props =>
    let dict := Properties.toAttrDict opType props
    if dict.isEmpty then "" else s!" <{DictionaryAttr.fromArray dict.toArray}>"

private def opNameString (ctx : IR.Context) (op : IR.Op) : String :=
  let opType := op.getOpType! ctx
  match opType with
  | .builtin .unregistered =>
    match (HasBuffedProperties.readPropertyAt (OpCode.builtin .unregistered) (op.impl + Operation.Offsets.properties) ctx.buf : Option UnregisteredProperties) with
    | some props => String.fromUTF8! props.opName
    | none => "builtin.unregistered"
  | _ => String.fromUTF8! opType.name

mutual

partial def printOp (ctx : IR.Context) (op : IR.Op) (depth : Nat) : IO Unit := do
  let mut line := indent depth
  let numResults := op.getNumResults! ctx
  if numResults ≠ 0 then
    let results := (List.range numResults.toNat).map fun i => valueName (IR.opResult ctx op i.toUInt64)
    line := line ++ String.intercalate ", " results ++ " = "
  line := line ++ s!"\"{opNameString ctx op}\""
  let numOperands := op.getNumOperands! ctx
  let operands := (List.range numOperands.toNat).map fun i =>
    (op.getOperandPtr! ctx i.toUInt64).getValue! ctx
  line := line ++ "(" ++ String.intercalate ", " (operands.map valueName) ++ ")"
  let numSuccessors := op.getNumSuccessors! ctx
  if numSuccessors ≠ 0 then
    let successors := (List.range numSuccessors.toNat).map fun i =>
      blockName ((op.getBlockOperandPtr! ctx i.toUInt64).getValue! ctx)
    line := line ++ " [" ++ String.intercalate ", " successors ++ "]"
  line := line ++ propertiesString ctx op
  let numRegions := op.getNumRegions! ctx
  if numRegions ≠ 0 then
    IO.print (line ++ " (")
    for i in [0:numRegions.toNat] do
      if i ≠ 0 then IO.print ", "
      printRegion ctx (op.getRegionPtr! ctx i.toUInt64) depth
    IO.print ")"
    line := ""
  let attrs := op.getAttributes! ctx
  if !attrs.entries.isEmpty then
    line := line ++ s!" {attrs}"
  let operandTypes := operands.map fun v => toString (IR.valueType ctx v)
  let resultTypes := (List.range numResults.toNat).map fun i =>
    toString (IR.valueType ctx (IR.opResult ctx op i.toUInt64))
  let resultsString := match resultTypes with
    | [ty] => ty
    | tys => "(" ++ String.intercalate ", " tys ++ ")"
  line := line ++ s!" : ({String.intercalate ", " operandTypes}) -> {resultsString}"
  IO.println line

partial def printBlock (ctx : IR.Context) (block : IR.Block) (depth : Nat) : IO Unit := do
  let numArgs := block.getNumArguments! ctx
  let args := (List.range numArgs.toNat).map fun i =>
    let value := IR.blockArgument ctx block i.toUInt64
    s!"{valueName value} : {IR.valueType ctx value}"
  IO.println s!"{indent depth}{blockName block}({String.intercalate ", " args}):"
  let mut next := (block.getFirstOp! ctx).toOption
  while let some op := next do
    printOp ctx op (depth + 1)
    next := (op.getNextOp! ctx).toOption

partial def printRegion (ctx : IR.Context) (region : IR.Region) (depth : Nat) : IO Unit := do
  IO.println "{"
  let mut next := (region.getFirstBlock! ctx).toOption
  while let some block := next do
    printBlock ctx block (depth + 1)
    next := (block.getNextBlock! ctx).toOption
  IO.print s!"{indent depth}}"

end

/-- Print the operation `op` and everything nested inside it. -/
def printModule (ctx : IR.Context) (op : IR.Op) : IO Unit :=
  printOp ctx op 0

end Veir.Parser.PrintIR

end
