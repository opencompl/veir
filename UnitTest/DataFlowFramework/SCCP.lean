import UnitTest.DataFlowFramework.Helpers

import Veir.Analysis.DataFlow.Domains.ConstantDomain
import Veir.Analysis.DataFlow.DeadCodeAnalysis
import Veir.Analysis.DataFlow.SparseConstantPropagationAnalysis

open Veir

private def constInt (bitwidth : Nat) (value : Int) : AbstractConstant :=
  .constant (.int bitwidth (Data.LLVM.Int.constant bitwidth value))

private def poisonInt (bitwidth : Nat) : AbstractConstant :=
  .constant (.int bitwidth .poison)

private def checkNamedConstantLattices
    (dfCtx : DataFlowContext)
    (valueDefs : Std.HashMap String ValuePtr)
    (expected : Array (String × AbstractConstant)) : MismatchReport := Id.run do
  let mut report := #[]
  for (name, expectedValue) in expected do
    let some value := valueDefs[name]?
      | report := report.push s!"constant {name}: missing value definition"
        continue
    let observed := SparseFact.getElement .sparseConstant value dfCtx
    if observed != expectedValue then
      report := report.push s!"constant {name}: expected {expectedValue}, observed {observed}"
  report

private def run
    (mlir : String)
    (expectedBlockLives : Array (String × Bool))
    (expectedEdgeLives : Array ((String × String) × Bool))
    (expectedConstants : Array (String × AbstractConstant)) : String :=
  runWithAnalyses mlir #[Veir.SparseConstantPropagationAnalysis, Veir.DeadCodeAnalysis]
    (fun top dfCtx irCtx => Id.run do
      match recoverNames top irCtx mlir with
      | Except.error err =>
          return #[err]
      | Except.ok recovered =>
          checkNamedEdgeLiveness dfCtx recovered.blocks expectedEdgeLives
            ++ checkNamedBlockLiveness dfCtx irCtx recovered.blocks expectedBlockLives
            ++ checkNamedConstantLattices dfCtx recovered.values expectedConstants)

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
-/
private def testLoopCarriesConstantThroughUnknownBackedge : String :=
  run
    r#""func.func"() <{sym_name = "f", function_type = () -> ()}> ({
^bb0:
  %x0 = "arith.constant"() <{ value = 1 : i32 }> : () -> i32
  "cf.br"(%x0) [^bb1] : (i32) -> ()
^bb1(%x1 : i32):
  %one = "arith.constant"() <{ value = 1 : i32 }> : () -> i32
  %b = "arith.cmpi"(%x1, %one) <{predicate = 1 : i64}> : (i32, i32) -> i1
  "cf.cond_br"(%b, %x1, %x1) [^bb2, ^bb3]
    <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
^bb2(%x1_then : i32):
  %x2 = "arith.constant"() <{ value = 2 : i32 }> : () -> i32
  "cf.br"(%x2) [^bb3] : (i32) -> ()
^bb3(%x3 : i32):
  %pred = "test.test"() : () -> i1
  "cf.cond_br"(%pred, %x3, %x3) [^bb1, ^bb4]
    <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
^bb4(%retv : i32):
  "func.return"() : () -> ()
}) : () -> ()"#
    #[("bb0", true), ("bb1", true), ("bb2", false), ("bb3", true), ("bb4", true)]
    #[ (("bb0", "bb1"), true)
     , (("bb1", "bb2"), false)
     , (("bb1", "bb3"), true)
     , (("bb2", "bb3"), false)
     , (("bb3", "bb1"), true)
     , (("bb3", "bb4"), true)
     ]
    #[ ("x0", constInt 32 1)
     , ("x1", constInt 32 1)
     , ("one", constInt 32 1)
     , ("b", constInt 1 0)
     , ("x2", .bottom)
     , ("x3", constInt 32 1)
     , ("pred", .top)
     , ("retv", constInt 32 1)
     ]

/--
info: "ok"
-/
#guard_msgs in
#eval! testLoopCarriesConstantThroughUnknownBackedge

private def testPoisonConditionKeepsBothSuccessorsLive : String :=
  run
    r#""func.func"() <{sym_name = "f", function_type = () -> ()}> ({
^bb0:
  %condition = "llvm.mlir.poison"() : () -> i1
  "cf.cond_br"(%condition) [^bb1, ^bb2]
    <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
^bb1:
  "func.return"() : () -> ()
^bb2:
  "func.return"() : () -> ()
}) : () -> ()"#
    #[ ("bb0", true)
     , ("bb1", true)
     , ("bb2", true)
     ]
    #[ (("bb0", "bb1"), true)
     , (("bb0", "bb2"), true)
     ]
    #[("condition", poisonInt 1)]

/--
info: "ok"
-/
#guard_msgs in
#eval! testPoisonConditionKeepsBothSuccessorsLive

private def testLlvmBranchUsesControlFlowInterface : String :=
  run
    r#""func.func"() <{sym_name = "f", function_type = () -> ()}> ({
^bb0:
  %condition = "llvm.mlir.constant"() <{value = 0 : i1}> : () -> i1
  "llvm.cond_br"(%condition) [^bb1, ^bb2]
    <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
^bb1:
  "func.return"() : () -> ()
^bb2:
  "func.return"() : () -> ()
}) : () -> ()"#
    #[ ("bb0", true)
     , ("bb1", false)
     , ("bb2", true)
     ]
    #[ (("bb0", "bb1"), false)
     , (("bb0", "bb2"), true)
     ]
    #[("condition", constInt 1 0)]

/--
info: "ok"
-/
#guard_msgs in
#eval! testLlvmBranchUsesControlFlowInterface
