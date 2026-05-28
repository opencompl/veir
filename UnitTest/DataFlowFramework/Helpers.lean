import Veir.Analysis.DataFlowFramework
import Veir.Analysis.DataFlow.Domains
import Veir.Parser.MlirParser

open Std (HashMap)
open Veir
open Veir.Parser

/--
Human readable mismatches collected by a dataflow test.
-/
abbrev MismatchReport := Array String

/--
Render a mismatch report in the format expected by the `#guard_msgs` tests below.
-/
def renderReport (report : MismatchReport) : String :=
  if report.isEmpty then
    "ok"
  else
    "mismatches:\n" ++ String.intercalate "\n" report.toList

/--
Parse one top level MLIR operation together with the parser state that owns its IR context.
-/
def parseTopLevelOp (s : String) : Except String (OperationPtr × MlirParserState) := do
  let some (ctx, _) := WfIRContext.create OpCode
    | throw "internal error: failed to create IR context"
  let parserState ←
    match ParserState.fromInput s.toByteArray with
    | .ok parserState => pure parserState
    | .error err => throw (toString err)
  match (parseOp none).run (MlirParserState.fromContext ctx) parserState with
  | .ok (op, mlirState, _) =>
    pure (op, mlirState)
  | .error err =>
    throw (toString err)

/--
Recover textual block labels such as `^bb0` from an MLIR snippet string.
-/
def blockLabelsFromMlir (mlir : String) : Array String := Id.run do
  let mut names := #[]
  for line in mlir.splitOn "\n" do
    let trimmed := (line.trimAsciiStart).toString
    if trimmed.startsWith "^" then
      let name := ((trimmed.drop 1).takeWhile fun c => c ≠ ':' && c ≠ '(').toString
      names := names.push name
  names

/--
Extract one textual SSA name from a definition fragment such as `%x : i32` or `%x`.
-/
def parseSsaName? (fragment : String) : Option String :=
  let trimmed := (fragment.trimAsciiStart).toString
  if trimmed.startsWith "%" then
    let name := ((trimmed.drop 1).takeWhile fun c => c ≠ ':' && c ≠ ' ' && c ≠ '\t').toString
    if name.isEmpty then none else some name
  else
    none

/--
Recover textual SSA names from block arguments and operation result definitions.
-/
def definedSsaNamesFromMlir (mlir : String) : Array String := Id.run do
  let mut names := #[]
  for line in mlir.splitOn "\n" do
    let trimmed := (line.trimAsciiStart).toString
    if trimmed.startsWith "^" then
      let args := (((trimmed.splitOn "(").drop 1 |>.headD "").takeWhile fun c => c ≠ ')').toString
      for arg in args.splitOn "," do
        if let some name := parseSsaName? arg then
          names := names.push name
    else if trimmed.startsWith "%" then
      let lhs := (trimmed.splitOn "=").headD ""
      for result in lhs.splitOn "," do
        if let some name := parseSsaName? result then
          names := names.push name
  names

/--
Collect all blocks reachable by recursively traversing nested regions in source order.
-/
partial def collectBlocksInSourceOrder
    (op : OperationPtr)
    (irCtx : IRContext OpCode)
    (acc : Array BlockPtr := #[]) : Array BlockPtr := Id.run do
  let mut acc := acc
  for region in (op.get! irCtx).regions do
    let region := region.get! irCtx
    let mut currentBlock := region.firstBlock
    while let some block := currentBlock do
      acc := acc.push block
      let mut currentOp := (block.get! irCtx).firstOp
      while let some nestedOp := currentOp do
        acc := collectBlocksInSourceOrder nestedOp irCtx acc
        currentOp := (nestedOp.get! irCtx).next
      currentBlock := (block.get! irCtx).next
  acc

/--
Collect all SSA values in source order.
This includes the operation's results, followed by block arguments and nested
operation results inside each region.
-/
partial def collectDefinedValuesInSourceOrder
    (top : OperationPtr)
    (irCtx : IRContext OpCode)
    (acc : Array ValuePtr := #[]) : Array ValuePtr := Id.run do
  let mut acc := acc
  for result in top.getResults! irCtx do
    acc := acc.push result
  for region in (top.get! irCtx).regions do
    let region := region.get! irCtx
    let mut currentBlock := region.firstBlock
    while let some block := currentBlock do
      for arg in block.getArguments! irCtx do
        acc := acc.push arg
      let mut currentOp := (block.get! irCtx).firstOp
      while let some nestedOp := currentOp do
        acc := collectDefinedValuesInSourceOrder nestedOp irCtx acc
        currentOp := (nestedOp.get! irCtx).next
      currentBlock := (block.get! irCtx).next
  acc

/--
Recovered name maps built by pairing MLIR source names with IR nodes in source order.
-/
structure RecoveredNames where
  blocks : HashMap String BlockPtr
  values : HashMap String ValuePtr

/--
Recover block and SSA value maps by pairing MLIR source names with IR traversal order.
-/
def recoverNames?
    (top : OperationPtr)
    (irCtx : IRContext OpCode)
    (mlir : String) : Option RecoveredNames :=
  let blockLabels := blockLabelsFromMlir mlir
  let blocks := collectBlocksInSourceOrder top irCtx
  let valueNames := definedSsaNamesFromMlir mlir
  let values := collectDefinedValuesInSourceOrder top irCtx
  if blockLabels.size ≠ blocks.size || valueNames.size ≠ values.size then
    none
  else
    some <| Id.run do
      let mut blockMap : HashMap String BlockPtr := HashMap.emptyWithCapacity blockLabels.size
      for (blockLabel, block) in blockLabels.zip blocks do
        blockMap := blockMap.insert blockLabel block

      let mut valueMap : HashMap String ValuePtr := HashMap.emptyWithCapacity valueNames.size
      for (valueName, value) in valueNames.zip values do
        valueMap := valueMap.insert valueName value

      { blocks := blockMap, values := valueMap }

/--
Parse an MLIR snippet string, run the requested dataflow analyses to a fixpoint, and
render any test mismatches produced by `check`.
-/
def runWithAnalyses
    (mlir : String)
    (analyses : Array DataFlowAnalysis)
    (check : OperationPtr -> DataFlowContext -> MlirParserState -> MismatchReport) : String :=
  match parseTopLevelOp mlir with
  | .error err =>
    s!"parse failed: {err}"
  | .ok (top, parserState) =>
    match fixpointSolve top analyses parserState.ctx with
    | some dfCtx =>
      renderReport (check top dfCtx parserState)
    | none =>
      "analysis did not converge"
