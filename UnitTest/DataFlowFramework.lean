import Veir.Analysis.DataFlowFramework 
import Veir.Parser.MlirParser

import Veir.Analysis.DataFlow.Domains
import Veir.Analysis.DataFlow.DeadCodeAnalysis
import Veir.Analysis.DataFlow.SparseConstantPropagationAnalysis

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

def getConstant
    (dfCtx : DataFlowContext)
    (value : ValuePtr) : ConstantDomain :=
  SparseFact.getElementD .sparseConstant dfCtx value ConstantDomain.bottom

def isBlockLive (dfCtx : DataFlowContext) (block : BlockPtr) (irCtx : IRContext OpCode) : Bool :=
  match dfCtx.getFact? .executable (.InsertPoint (InsertPoint.atStart! block irCtx)) with
  | some fact => fact.live
  | none => false

def isEdgeLive (dfCtx : DataFlowContext) (src dst : BlockPtr) : Bool :=
  match dfCtx.getFact? .executable (.CFGEdge { source := src, target := dst }) with
  | some fact => fact.live
  | none => false

def showConstantDomain : ConstantDomain -> String
  | .top =>
    "top"
  | .bottom =>
    "bottom"
  | .constant c =>
    s!"const({c.value} : i{c.bitwidth})"

def checkNamedConstants
    (dfCtx : DataFlowContext)
    (valueDefs : HashMap String ValuePtr)
    (expected : Array (String × ConstantDomain)) : MismatchReport := Id.run do
  let mut report := #[]
  for (name, expectedValue) in expected do
    let some value := valueDefs[name]? |
      report := report.push s!"constant {name}: missing value definition"
      continue
    let observedValue :=
      SparseFact.getElementD .sparseConstant dfCtx value ConstantDomain.bottom
    if observedValue != expectedValue then
      report := report.push s!"constant {name}: expected {showConstantDomain expectedValue}, observed {showConstantDomain observedValue}"
  report

def checkNamedBlockLiveness
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode)
    (blockMap : HashMap String BlockPtr)
    (expected : Array (String × Bool)) : MismatchReport := Id.run do
  let mut report := #[]
  for (name, live) in expected do
    match blockMap[name]? with
    | some block =>
      let observed := isBlockLive dfCtx block irCtx
      if observed != live then
        report := report.push s!"block {name}: expected live={live}, observed live={observed}"
    | none =>
      report := report.push s!"block {name}: missing block label"
  report

def checkNamedEdgeLiveness
    (dfCtx : DataFlowContext)
    (blockMap : HashMap String BlockPtr)
    (expected : Array ((String × String) × Bool)) : MismatchReport := Id.run do
  let mut report := #[]
  for ((srcName, dstName), live) in expected do
    match blockMap[srcName]?, blockMap[dstName]? with
    | some src, some dst =>
      let observed := isEdgeLive dfCtx src dst
      if observed != live then
        report := report.push s!"edge {srcName} -> {dstName}: expected live={live}, observed live={observed}"
    | _, _ =>
      report := report.push s!"edge {srcName} -> {dstName}: missing block label(s)"
  report

namespace SparseConstantPropagation

def run
    (mlir : String)
    (expected : Array (String × ConstantDomain)) : String :=
  runWithAnalyses mlir #[Veir.SparseConstantPropagationAnalysis, Veir.DeadCodeAnalysis]
    (fun top dfCtx parserState =>
      match recoverNames? top parserState.ctx mlir with
      | some recovered => checkNamedConstants dfCtx recovered.values expected
      | none => #["failed to recover block/value names from MLIR"])

def testAddiAllConstant : String :=
  let mlir := "\"builtin.module\"() ({\n\
^bb0:\n\
  %a = \"arith.constant\"() <{ value = 5 : i32 }> : () -> i32\n\
  %b = \"arith.constant\"() <{ value = 7 : i32 }> : () -> i32\n\
  %c = \"arith.addi\"(%a, %b) : (i32, i32) -> i32\n\
}) : () -> ()"
  run mlir
    #[ ("a", ConstantDomain.ofInt 32 5)
     , ("b", ConstantDomain.ofInt 32 7)
     , ("c", ConstantDomain.ofInt 32 12)
     ]

def testMuliAllConstant : String :=
  let mlir := "\"builtin.module\"() ({\n\
^bb0:\n\
  %a = \"arith.constant\"() <{ value = 3 : i32 }> : () -> i32\n\
  %b = \"arith.constant\"() <{ value = 2 : i32 }> : () -> i32\n\
  %c = \"arith.muli\"(%a, %b) : (i32, i32) -> i32\n\
}) : () -> ()"
  run mlir
    #[ ("a", ConstantDomain.ofInt 32 3)
     , ("b", ConstantDomain.ofInt 32 2)
     , ("c", ConstantDomain.ofInt 32 6)
     ]

def testAndiAllConstant : String :=
  let mlir := "\"builtin.module\"() ({\n\
^bb0:\n\
  %a = \"arith.constant\"() <{ value = 27 : i32 }> : () -> i32\n\
  %b = \"arith.constant\"() <{ value = 3 : i32 }> : () -> i32\n\
  %c = \"arith.andi\"(%a, %b) : (i32, i32) -> i32\n\
}) : () -> ()"
  run mlir
    #[ ("a", ConstantDomain.ofInt 32 27)
     , ("b", ConstantDomain.ofInt 32 3)
     , ("c", ConstantDomain.ofInt 32 3)
     ]

def testSubiAllConstant : String :=
  let mlir := "\"builtin.module\"() ({\n\
^bb0:\n\
  %a = \"arith.constant\"() <{ value = 12 : i32 }> : () -> i32\n\
  %b = \"arith.constant\"() <{ value = 37 : i32 }> : () -> i32\n\
  %c = \"arith.subi\"(%a, %b) : (i32, i32) -> i32\n\
}) : () -> ()"
  run mlir
    #[ ("a", ConstantDomain.ofInt 32 12)
     , ("b", ConstantDomain.ofInt 32 37)
     , ("c", ConstantDomain.ofInt 32 (-25))
     ]

def testAddiUnknownOperand : String :=
  let mlir := "\"builtin.module\"() ({\n\
^bb0:\n\
  %a = \"arith.constant\"() <{ value = -3 : i32 }> : () -> i32\n\
  %u = \"test.test\"() : () -> i32\n\
  %c = \"arith.addi\"(%a, %u) : (i32, i32) -> i32\n\
}) : () -> ()"
  run mlir
    #[ ("a", ConstantDomain.ofInt 32 (-3))
     , ("u", ConstantDomain.unknown)
     , ("c", ConstantDomain.unknown)
     ]

def testMuliUnknownOperand : String :=
  let mlir := "\"builtin.module\"() ({\n\
^bb0:\n\
  %a = \"arith.constant\"() <{ value = 7 : i32 }> : () -> i32\n\
  %u = \"test.test\"() : () -> i32\n\
  %c = \"arith.muli\"(%a, %u) : (i32, i32) -> i32\n\
}) : () -> ()"
  run mlir
    #[ ("a", ConstantDomain.ofInt 32 7)
     , ("u", ConstantDomain.unknown)
     , ("c", ConstantDomain.unknown)
     ]

def testAndiUnknownOperand : String :=
  let mlir := "\"builtin.module\"() ({\n\
^bb0:\n\
  %a = \"arith.constant\"() <{ value = -2 : i32 }> : () -> i32\n\
  %u = \"test.test\"() : () -> i32\n\
  %c = \"arith.andi\"(%a, %u) : (i32, i32) -> i32\n\
}) : () -> ()"
  run mlir
    #[ ("a", ConstantDomain.ofInt 32 (-2))
     , ("u", ConstantDomain.unknown)
     , ("c", ConstantDomain.unknown)
     ]

def testSubiUnknownOperand : String :=
  let mlir := "\"builtin.module\"() ({\n\
^bb0:\n\
  %a = \"arith.constant\"() <{ value = 0 : i32 }> : () -> i32\n\
  %u = \"test.test\"() : () -> i32\n\
  %c = \"arith.subi\"(%a, %u) : (i32, i32) -> i32\n\
}) : () -> ()"
  run mlir
    #[ ("a", ConstantDomain.ofInt 32 0)
     , ("u", ConstantDomain.unknown)
     , ("c", ConstantDomain.unknown)
     ]

/--
info: "ok"
-/
#guard_msgs in
#eval! testAddiAllConstant

/--
info: "ok"
-/
#guard_msgs in
#eval! testMuliAllConstant

/--
info: "ok"
-/
#guard_msgs in
#eval! testAndiAllConstant

/--
info: "ok"
-/
#guard_msgs in
#eval! testSubiAllConstant

/--
info: "ok"
-/
#guard_msgs in
#eval! testAddiUnknownOperand

/--
info: "ok"
-/
#guard_msgs in
#eval! testMuliUnknownOperand

/--
info: "ok"
-/
#guard_msgs in
#eval! testAndiUnknownOperand

/--
info: "ok"
-/
#guard_msgs in
#eval! testSubiUnknownOperand

end SparseConstantPropagation

namespace DeadCodeAnalysis

def run
    (mlir : String)
    (expectedBlockLives : Array (String × Bool)) : String :=
  runWithAnalyses mlir #[Veir.DeadCodeAnalysis] (fun top dfCtx parserState => Id.run do
    let some recovered := recoverNames? top parserState.ctx mlir
      | return #["failed to recover block/value names from MLIR"]
    checkNamedBlockLiveness dfCtx parserState.ctx recovered.blocks expectedBlockLives)

def testTopLevelAndFunctionEntryBlocksLive : String :=
  let mlir := "\"builtin.module\"() ({\n\
^bb0:\n\
  \"func.func\"() ({\n\
  ^entry:\n\
  }) : () -> ()\n\
}) : () -> ()"
  run mlir #[("bb0", true), ("entry", true)]

def testBranchWithoutSCPLeavesSuccessorsDead : String :=
  let mlir := "\"builtin.module\"() ({\n\
^bb0:\n\
  %cond = \"arith.constant\"() <{ value = 1 : i32 }> : () -> i32\n\
  \"test.test\"(%cond)[^bb1, ^bb2] : (i32) -> ()\n\
^bb1:\n\
  %x = \"arith.constant\"() <{ value = 10 : i32 }> : () -> i32\n\
^bb2:\n\
  %y = \"arith.constant\"() <{ value = 20 : i32 }> : () -> i32\n\
}) : () -> ()"
  run mlir #[("bb1", false), ("bb2", false)]

/--
info: "ok"
-/
#guard_msgs in
#eval! testTopLevelAndFunctionEntryBlocksLive

/--
info: "ok"
-/
#guard_msgs in
#eval! testBranchWithoutSCPLeavesSuccessorsDead

end DeadCodeAnalysis

namespace SCCP

def run
    (mlir : String)
    (expectedBlockLives : Array (String × Bool))
    (expectedEdgeLives : Array ((String × String) × Bool))
    (expectedConstants : Array (String × ConstantDomain)) : String :=
  runWithAnalyses mlir #[Veir.SparseConstantPropagationAnalysis, Veir.DeadCodeAnalysis] (fun top dfCtx parserState => Id.run do
    let some recovered := recoverNames? top parserState.ctx mlir
      | return #["failed to recover block/value names from MLIR"]
    checkNamedEdgeLiveness dfCtx recovered.blocks expectedEdgeLives
      ++ checkNamedBlockLiveness dfCtx parserState.ctx recovered.blocks expectedBlockLives
      ++ checkNamedConstants dfCtx recovered.values expectedConstants)

/--
Pseudo-code modeled by this test:

```
int x₀ ← 1;

do {
    x₁ ← φ(x₀, x₃);

    b ← (x₁ ≠ 1);

    if (b)
        x₂ ← 2;

    x₃ ← φ(x₁, x₂);

} while (pred());

return(x₃);
```
Line 0 is reachable.
x_0 is 1
Line 1 is reachable.
x_1 is 1
Line 2 is reachable.
b is 0 (false)
Line 3 is reachable.
Line 4 is unreachable.
x_2 is bottom
Line 5 is reachable.
x_3 is 1
Line 6 is reachable.
pred is top
Line 7 is reachable.

Temporary `.test.test` semantics used by this test:
- When the op has successors, operand 0 is the branch condition.
- Zero takes successor 1 and nonzero takes successor 0.
- All operands are forwarded to the successor block as block arguments.
- When the op has no successors, its result is treated as an unknown value.

Because the branch condition is also forwarded, some destination blocks accept
an extra ignored argument like `%dead1`, `%dead2`, or `%dead3`. Those are just
the forwarded branch conditions; the later block arguments are the actual values
we care about.
-/
def testLoopCarriesConstantThroughUnknownBackedge : String :=
  let mlir := "\"builtin.module\"() ({\n\
^bb0:\n\
  %x0 = \"arith.constant\"() <{ value = 1 : i32 }> : () -> i32\n\
  \"test.test\"(%x0, %x0)[^bb1] : (i32, i32) -> ()\n\
^bb1(%dead1 : i32, %x1 : i32):\n\
  %one = \"arith.constant\"() <{ value = 1 : i32 }> : () -> i32\n\
  %b = \"arith.subi\"(%x1, %one) : (i32, i32) -> i32\n\
  \"test.test\"(%b, %x1)[^bb2, ^bb3] : (i32, i32) -> ()\n\
^bb2(%dead_then : i32, %x1_then : i32):\n\
  %x2 = \"arith.constant\"() <{ value = 2 : i32 }> : () -> i32\n\
  \"test.test\"(%x2, %x2)[^bb3] : (i32, i32) -> ()\n\
^bb3(%dead2 : i32, %x3 : i32):\n\
  %pred = \"test.test\"() : () -> i32\n\
  \"test.test\"(%pred, %x3)[^bb1, ^bb4] : (i32, i32) -> ()\n\
^bb4(%dead3 : i32, %retv : i32):\n\
}) : () -> ()"
  run mlir
    #[("bb0", true), ("bb1", true), ("bb2", false), ("bb3", true), ("bb4", true)]
    #[ (("bb0", "bb1"), true)
     , (("bb1", "bb2"), false)
     , (("bb1", "bb3"), true)
     , (("bb2", "bb3"), false)
     , (("bb3", "bb1"), true)
     , (("bb3", "bb4"), true)
     ]
    #[ ("x0", ConstantDomain.ofInt 32 1)
     , ("x1", ConstantDomain.ofInt 32 1)
     , ("one", ConstantDomain.ofInt 32 1)
     , ("b", ConstantDomain.ofInt 32 0)
     , ("x2", ConstantDomain.bottom)
     , ("x3", ConstantDomain.ofInt 32 1)
     , ("pred", ConstantDomain.unknown)
     , ("retv", ConstantDomain.ofInt 32 1)
     ]

/--
info: "ok"
-/
#guard_msgs in
#eval! testLoopCarriesConstantThroughUnknownBackedge

end SCCP

end UnitTest.DataFlowFramework
