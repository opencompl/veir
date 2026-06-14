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
  run
    r#""builtin.module"() ({
^bb0:
  "func.func"() ({
  ^entry:
  }) : () -> ()
}) : () -> ()"#
    #[("bb0", true), ("entry", true)]

private def testLiteralBranchWithoutSCPTakesKnownSuccessor : String :=
  run
    r#""builtin.module"() ({
^bb0:
  %cond = "arith.constant"() <{ value = 1 : i32 }> : () -> i32
  "test.test"(%cond)[^bb1, ^bb2] : (i32) -> ()
^bb1:
  %x = "arith.constant"() <{ value = 10 : i32 }> : () -> i32
^bb2:
  %y = "arith.constant"() <{ value = 20 : i32 }> : () -> i32
}) : () -> ()"#
    #[("bb1", true), ("bb2", false)]

private def testUnknownBranchWithoutSCPMarksAllSuccessorsLive : String :=
  run
    r#""builtin.module"() ({
^bb0:
  %cond = "test.test"() : () -> i32
  "test.test"(%cond)[^bb1, ^bb2] : (i32) -> ()
^bb1:
  %x = "arith.constant"() <{ value = 10 : i32 }> : () -> i32
^bb2:
  %y = "arith.constant"() <{ value = 20 : i32 }> : () -> i32
}) : () -> ()"#
    #[("bb1", true), ("bb2", true)]

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
