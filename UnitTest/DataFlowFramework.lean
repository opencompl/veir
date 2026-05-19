import Veir.Analysis.DataFlowFramework 
import Veir.Parser.MlirParser

import Veir.Analysis.DataFlow.DominanceAnalysis

open Std (HashMap)
open Veir
open Veir.Parser

namespace UnitTest.DataFlowFramework

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
      let name := ((trimmed.drop 1).takeWhile fun c => c != ':' && c != '(').toString
      names := names.push name
  names

/--
Extract one textual SSA name from a definition fragment such as `%x : i32` or `%x`.
-/
def parseSsaName? (fragment : String) : Option String :=
  let trimmed := (fragment.trimAsciiStart).toString
  if trimmed.startsWith "%" then
    let name := ((trimmed.drop 1).takeWhile fun c => c != ':' && c != ' ' && c != '\t').toString
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
      let args := (((trimmed.splitOn "(").drop 1 |>.headD "").takeWhile fun c => c != ')').toString
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
  for i in [0:op.getNumRegions! irCtx] do
    let region := (op.getRegion! irCtx i).get! irCtx
    let mut maybeBlock := region.firstBlock
    while h : maybeBlock.isSome do
      let block := maybeBlock.get h
      acc := acc.push block
      let mut maybeOp := (block.get! irCtx).firstOp
      while hOp : maybeOp.isSome do
        let nestedOp := maybeOp.get hOp
        acc := collectBlocksInSourceOrder nestedOp irCtx acc
        maybeOp := (nestedOp.get! irCtx).next
      maybeBlock := (block.get! irCtx).next
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
  for i in [0:top.getNumResults! irCtx] do
    acc := acc.push (ValuePtr.opResult (top.getResult i))
  for i in [0:top.getNumRegions! irCtx] do
    let region := (top.getRegion! irCtx i).get! irCtx
    let mut maybeBlock := region.firstBlock
    while h : maybeBlock.isSome do
      let block := maybeBlock.get h
      for j in [0:block.getNumArguments! irCtx] do
        acc := acc.push (ValuePtr.blockArgument (block.getArgument j))
      let mut maybeOp := (block.get! irCtx).firstOp
      while hOp : maybeOp.isSome do
        let nestedOp := maybeOp.get hOp
        acc := collectDefinedValuesInSourceOrder nestedOp irCtx acc
        maybeOp := (nestedOp.get! irCtx).next
      maybeBlock := (block.get! irCtx).next
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
  if blockLabels.size != blocks.size || valueNames.size != values.size then
    none
  else
    some <| Id.run do
      let mut blockMap : HashMap String BlockPtr := HashMap.emptyWithCapacity blockLabels.size
      for i in [0:blockLabels.size] do
        blockMap := blockMap.insert blockLabels[i]! blocks[i]!
      let mut valueMap : HashMap String ValuePtr := HashMap.emptyWithCapacity valueNames.size
      for i in [0:valueNames.size] do
        valueMap := valueMap.insert valueNames[i]! values[i]!
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

def compareNamedDominators
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode)
    (blockMap : HashMap String BlockPtr)
    (expected : Array (String × Option (Array String))) : MismatchReport := Id.run do
  let mut report := #[]
  for (name, expectedDoms?) in expected do
    match blockMap[name]? with
    | none =>
      report := report.push s!"dominators {name}: missing block label"
    | some block =>
      let observedReachable := (block.getDominatorFact? dfCtx irCtx).isSome
      match expectedDoms? with
      | none =>
        if observedReachable then
          report := report.push s!"dominators {name}: expected unreachable block, observed initialized state"
      | some expectedDoms =>
        if !observedReachable then
          report := report.push s!"dominators {name}: expected initialized state, observed none"
        else
          for expectedDom in expectedDoms do
            match blockMap[expectedDom]? with
            | some expectedBlock =>
              if !Veir.DominanceAnalysis.dominates expectedBlock block dfCtx irCtx then
                report := report.push s!"dominators {name}: missing expected dominator {expectedDom}"
            | none =>
              report := report.push s!"dominators {name}: missing block label {expectedDom}"
          for (observedName, observedBlock) in blockMap.toList do
            if Veir.DominanceAnalysis.dominates observedBlock block dfCtx irCtx
                && !expectedDoms.contains observedName then
              report := report.push s!"dominators {name}: unexpected dominator {observedName}"
  report

namespace DominanceAnalysis

def run
    (mlir : String)
    (expected : Array (String × Option (Array String))) : String :=
  runWithAnalyses mlir #[Veir.DominanceAnalysis] (fun top dfCtx parserState => Id.run do
    let some recovered := recoverNames? top parserState.ctx mlir
      | return #["failed to recover block/value names from MLIR"]
    compareNamedDominators dfCtx parserState.ctx recovered.blocks expected)

/-
  Test: loop with a backedge
            ┌───┐
            │ 0 │
            └─┬─┘
              │
              │
            ┌─▼─┐
            │ 1 ◄──┐
            └─┬─┘  │
              │    │
              │    │
            ┌─▼─┐  │
            │ 2 ├──┘
            └───┘
-/
def testDomLoop : String :=
  run
    "\"builtin.module\"() ({\n\
^bb0:\n\
  \"test.test\"() [^bb1] : () -> ()\n\
^bb1:\n\
  \"test.test\"() [^bb2] : () -> ()\n\
^bb2:\n\
  \"test.test\"() [^bb1] : () -> ()\n\
}) : () -> ()"
    #[ ("bb0", some #["bb0"])
     , ("bb1", some #["bb0", "bb1"])
     , ("bb2", some #["bb0", "bb1", "bb2"])
     ]

/-
  Test: diamond
         ┌───┐
      ┌──┤ 0 ├──┐
      │  └───┘  │
    ┌─▼─┐     ┌─▼─┐
    │ 1 │     │ 2 │
    └─┬─┘     └─┬─┘
      │  ┌───┐  │
      └──► 3 ◄──┘
         └───┘
-/
def testDomDiamond : String :=
  run
    "\"builtin.module\"() ({\n\
^bb0:\n\
  \"test.test\"() [^bb1, ^bb2] : () -> ()\n\
^bb1:\n\
  \"test.test\"() [^bb3] : () -> ()\n\
^bb2:\n\
  \"test.test\"() [^bb3] : () -> ()\n\
^bb3:\n\
  \"test.test\"() : () -> ()\n\
}) : () -> ()"
    #[ ("bb0", some #["bb0"])
     , ("bb1", some #["bb0", "bb1"])
     , ("bb2", some #["bb0", "bb2"])
     , ("bb3", some #["bb0", "bb3"])
     ]

/-
  Test: straight line
        ┌───┐
        │ 0 │
        └─┬─┘
          │
        ┌─▼─┐
        │ 1 │
        └─┬─┘
          │
        ┌─▼─┐
        │ 2 │
        └─┬─┘
          │
        ┌─▼─┐
        │ 3 │
        └───┘
-/
def testDomLine : String :=
  run
    "\"builtin.module\"() ({\n\
^bb0:\n\
  \"test.test\"() [^bb1] : () -> ()\n\
^bb1:\n\
  \"test.test\"() [^bb2] : () -> ()\n\
^bb2:\n\
  \"test.test\"() [^bb3] : () -> ()\n\
^bb3:\n\
  \"test.test\"() : () -> ()\n\
}) : () -> ()"
    #[ ("bb0", some #["bb0"])
     , ("bb1", some #["bb0", "bb1"])
     , ("bb2", some #["bb0", "bb1", "bb2"])
     , ("bb3", some #["bb0", "bb1", "bb2", "bb3"])
     ]


/-
  Test: entry branches to a while-loop or to an if-statement, then join.
                      ┌───┐
                  ┌───┤ 0 ├───┐
                  │   └───┘   │
                ┌─▼─┐       ┌─▼─┐
              ┌─► 1 │    ┌──┤ 2 ├──┐
              │ └─┬─┘    │  └───┘  │
              │   │    ┌─▼─┐     ┌─▼─┐
              │ ┌─▼─┐  │ 3 │     │ 4 │
              └─┤ 5 │  └─┬─┘     └─┬─┘
                └─┬─┘    │  ┌───┐  │
                  │      └──► 6 ◄──┘  
                  │         └─┬─┘
                  │   ┌───┐   │
                  └───► 7 ◄───┘
                      └───┘
-/
def testDomIfLoopIf : String :=
  run
    "\"builtin.module\"() ({\n\
^bb0:\n\
  \"test.test\"() [^bb1, ^bb2] : () -> ()\n\
^bb1:\n\
  \"test.test\"() [^bb5] : () -> ()\n\
^bb2:\n\
  \"test.test\"() [^bb3, ^bb4] : () -> ()\n\
^bb3:\n\
  \"test.test\"() [^bb6] : () -> ()\n\
^bb4:\n\
  \"test.test\"() [^bb6] : () -> ()\n\
^bb5:\n\
  \"test.test\"() [^bb1, ^bb7] : () -> ()\n\
^bb6:\n\
  \"test.test\"() [^bb7] : () -> ()\n\
^bb7:\n\
  \"test.test\"() : () -> ()\n\
}) : () -> ()"
    #[ ("bb0", some #["bb0"])
     , ("bb1", some #["bb0", "bb1"])
     , ("bb2", some #["bb0", "bb2"])
     , ("bb3", some #["bb0", "bb2", "bb3"])
     , ("bb4", some #["bb0", "bb2", "bb4"])
     , ("bb5", some #["bb0", "bb1", "bb5"])
     , ("bb6", some #["bb0", "bb2", "bb6"])
     , ("bb7", some #["bb0", "bb7"])
     ]

/--
info: "ok"
-/
#guard_msgs in
#eval! testDomLoop

/--
info: "ok"
-/
#guard_msgs in
#eval! testDomDiamond

/--
info: "ok"
-/
#guard_msgs in
#eval! testDomLine

/--
info: "ok"
-/
#guard_msgs in
#eval! testDomIfLoopIf

end DominanceAnalysis

end UnitTest.DataFlowFramework
