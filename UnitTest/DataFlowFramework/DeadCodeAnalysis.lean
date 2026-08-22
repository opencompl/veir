import UnitTest.DataFlowFramework.Helpers


open Std (HashMap)
open Veir

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
  run
    r#""builtin.module"() ({
^bb0:
  "func.func"() <{sym_name = "f", function_type = () -> ()}> ({
  ^entry:
  }) : () -> ()
}) : () -> ()"#
    #[("bb0", true), ("entry", true)]
    #[]

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
    #[ (("bb0", "bb1"), true)
     , (("bb0", "bb2"), false)
     ]

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
    #[ (("bb0", "bb1"), true)
     , (("bb0", "bb2"), true)
     ]

private def testDiamond : String :=
  run
    r#""builtin.module"() ({
^bb0:
  "test.test"() [^bb1] : () -> ()
^bb1:
  %cond = "arith.constant"() <{ value = 1 : i32 }> : () -> i32
  "test.test"(%cond)[^bb2, ^bb3] : (i32) -> ()
^bb2:
  "test.test"() [^bb5] : () -> ()
^bb3:
  "test.test"() [^bb4] : () -> ()
^bb4:
  "test.test"() [^bb6] : () -> ()
^bb5:
  "test.test"() [^bb6] : () -> ()
^bb6:
  %x = "arith.constant"() <{ value = 10 : i32 }> : () -> i32
}) : () -> ()"#
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
Exercise reachability that is discovered against source order.

`bb1` is scanned while dead, so its terminator subscribes the dead-code analysis
to the block's liveness fact. Visiting the later `bb2` then makes `bb1` live.
-/
private def testReachabilityDiscoveredAfterSourceOrderScan : String :=
  run
    r#""builtin.module"() ({
^bb0:
  "test.test"() [^bb2] : () -> ()
^bb1:
  "test.test"() [^bb0] : () -> ()
^bb2:
  "test.test"() [^bb1] : () -> ()
}) : () -> ()"#
    #[("bb0", true), ("bb1", true), ("bb2", true)]
    #[ (("bb0", "bb2"), true)
     , (("bb2", "bb1"), true)
     , (("bb1", "bb0"), true)
     ]
/--
info: "ok"
-/
#guard_msgs in
#eval! testReachabilityDiscoveredAfterSourceOrderScan

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
