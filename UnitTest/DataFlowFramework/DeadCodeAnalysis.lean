import UnitTest.DataFlowFramework.Helpers

import Veir.Analysis.DataFlow.DeadCodeAnalysis

open Std (HashMap)
open Veir

-- TODO: Facts not initialized in the Dataflow Analysis Framework are implicitly assumed to be the pessimistic bottom state.
-- We should not assume this implicitly, but rather encode this in the framework!!!!
def isBlockLive (dfCtx : DataFlowContext) (block : BlockPtr) (irCtx : IRContext OpCode) : Bool :=
  match dfCtx.getFact? .executable (.InsertPoint (InsertPoint.atStart! block irCtx)) with
  | some fact => fact.live
  | none => false

def isEdgeLive (dfCtx : DataFlowContext) (src dst : BlockPtr) : Bool :=
  match dfCtx.getFact? .executable (.CFGEdge { source := src, target := dst }) with
  | some fact => fact.live
  | none => false

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

private def run
    (mlir : String)
    (expectedBlockLives : Array (String × Bool))
    (expectedEdgeLives : Array ((String × String) × Bool)) : String :=
  runWithAnalyses mlir #[Veir.DeadCodeAnalysis] (fun top dfCtx parserState => Id.run do
    match recoverNames top parserState.ctx mlir with
    | Except.error err =>
        return #[err]
    | Except.ok recovered =>
        checkNamedBlockLiveness dfCtx parserState.ctx recovered.blocks expectedBlockLives ++
          checkNamedEdgeLiveness dfCtx recovered.blocks expectedEdgeLives)

private def testTopLevelAndFunctionEntryBlocksLive : String :=
  let mlir := "\"builtin.module\"() ({\n\
^bb0:\n\
  \"func.func\"() ({\n\
  ^entry:\n\
  }) : () -> ()\n\
}) : () -> ()"
  run mlir #[("bb0", true), ("entry", true)] #[]

private def testLiteralBranchWithoutSCPTakesKnownSuccessor : String :=
  let mlir := "\"builtin.module\"() ({\n\
^bb0:\n\
  %cond = \"arith.constant\"() <{ value = 1 : i32 }> : () -> i32\n\
  \"test.test\"(%cond)[^bb1, ^bb2] : (i32) -> ()\n\
^bb1:\n\
  %x = \"arith.constant\"() <{ value = 10 : i32 }> : () -> i32\n\
^bb2:\n\
  %y = \"arith.constant\"() <{ value = 20 : i32 }> : () -> i32\n\
}) : () -> ()"
  run mlir
    #[("bb1", true), ("bb2", false)]
    #[ (("bb0", "bb1"), true)
     , (("bb0", "bb2"), false)
     ]

private def testUnknownBranchWithoutSCPMarksAllSuccessorsLive : String :=
  let mlir := "\"builtin.module\"() ({\n\
^bb0:\n\
  %cond = \"test.test\"() : () -> i32\n\
  \"test.test\"(%cond)[^bb1, ^bb2] : (i32) -> ()\n\
^bb1:\n\
  %x = \"arith.constant\"() <{ value = 10 : i32 }> : () -> i32\n\
^bb2:\n\
  %y = \"arith.constant\"() <{ value = 20 : i32 }> : () -> i32\n\
}) : () -> ()"
  run mlir
    #[("bb1", true), ("bb2", true)]
    #[ (("bb0", "bb1"), true)
     , (("bb0", "bb2"), true)
     ]

private def testDiamond : String :=
  let mlir := "\"builtin.module\"() ({\n\
^bb0:\n\
  \"test.test\"() [^bb1] : () -> ()\n\
^bb1:\n\
  %cond = \"arith.constant\"() <{ value = 1 : i32 }> : () -> i32\n\
  \"test.test\"(%cond)[^bb2, ^bb3] : (i32) -> ()\n\
^bb2:\n\
  \"test.test\"() [^bb5] : () -> ()\n\
^bb3:\n\
  \"test.test\"() [^bb4] : () -> ()\n\
^bb4:\n\
  \"test.test\"() [^bb6] : () -> ()\n\
^bb5:\n\
  \"test.test\"() [^bb6] : () -> ()\n\
^bb6:\n\
  %x = \"arith.constant\"() <{ value = 10 : i32 }> : () -> i32\n\
}) : () -> ()"
  run mlir
    #[("bb1", true), ("bb2", true), ("bb3", false), ("bb4", false), ("bb5", true), ("bb6", true)]
    #[ (("bb0", "bb1"), true)
     , (("bb1", "bb2"), true)
     , (("bb1", "bb3"), false)
     , (("bb2", "bb5"), true)
     , (("bb3", "bb4"), false)
     , (("bb4", "bb6"), false)
     , (("bb5", "bb6"), true)
     ]

/--
info: "ok"
-/
#guard_msgs in
#eval! testTopLevelAndFunctionEntryBlocksLive

/--
info: "ok"
-/
#guard_msgs in
#eval! testLiteralBranchWithoutSCPTakesKnownSuccessor

/--
info: "ok"
-/
#guard_msgs in
#eval! testUnknownBranchWithoutSCPMarksAllSuccessorsLive

/--
info: "ok"
-/
#guard_msgs in
#eval! testDiamond
