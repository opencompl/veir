import UnitTest.DataFlowFramework.Helpers

import Veir.Analysis.DataFlow.Domains.ConstantDomain
import Veir.Analysis.DataFlow.DeadCodeAnalysis
import Veir.Analysis.DataFlow.SparseConstantPropagationAnalysis

open Veir

private def constInt (bitwidth : Nat) (value : Int) : AbstractConstant :=
  .constant ⟨bitwidth, Data.LLVM.Int.constant bitwidth value⟩

private def run
    (mlir : String)
    (expectedBlockLives : Array (String × Bool))
    (expectedEdgeLives : Array ((String × String) × Bool))
    (expectedConstants : Array (String × AbstractConstant)) : String :=
  runWithAnalyses mlir #[Veir.SparseConstantPropagationAnalysis, Veir.DeadCodeAnalysis]
    (fun top dfCtx parserState => Id.run do
      match recoverNames top parserState.ctx mlir with
      | Except.error err =>
          return #[err]
      | Except.ok recovered =>
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
-/
private def testLoopCarriesConstantThroughUnknownBackedge : String :=
  run
    r#""builtin.module"() ({
^bb0:
  %x0 = "arith.constant"() <{ value = 1 : i32 }> : () -> i32
  "cf.br"(%x0) [^bb1] : (i32) -> ()
^bb1(%x1 : i32):
  %one = "arith.constant"() <{ value = 1 : i32 }> : () -> i32
  %b = "arith.subi"(%x1, %one) : (i32, i32) -> i32
  "cf.cond_br"(%b, %x1, %x1) [^bb2, ^bb3]
    <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i32, i32, i32) -> ()
^bb2(%x1_then : i32):
  %x2 = "arith.constant"() <{ value = 2 : i32 }> : () -> i32
  "cf.br"(%x2) [^bb3] : (i32) -> ()
^bb3(%x3 : i32):
  %pred = "test.test"() : () -> i32
  "cf.cond_br"(%pred, %x3, %x3) [^bb1, ^bb4]
    <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i32, i32, i32) -> ()
^bb4(%retv : i32):
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
     , ("b", constInt 32 0)
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
