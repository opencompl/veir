import UnitTest.DataFlowFramework.Helpers

import Veir.Analysis.DataFlow.DeadCodeAnalysis

open Veir

private def run
    (mlir : String)
    (expectedBlockLives : Array (String × Bool)) : String :=
  runWithAnalyses mlir #[Veir.DeadCodeAnalysis] (fun top dfCtx parserState => Id.run do
    match recoverNames top parserState.ctx mlir with
    | Except.error err =>
        return #[err]
    | Except.ok recovered =>
        checkNamedBlockLiveness dfCtx parserState.ctx recovered.blocks expectedBlockLives)

private def testTopLevelAndFunctionEntryBlocksLive : String :=
  let mlir := "\"builtin.module\"() ({\n\
^bb0:\n\
  \"func.func\"() ({\n\
  ^entry:\n\
  }) : () -> ()\n\
}) : () -> ()"
  run mlir #[("bb0", true), ("entry", true)]

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
  run mlir #[("bb1", true), ("bb2", false)]

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
  run mlir #[("bb1", true), ("bb2", true)]

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
