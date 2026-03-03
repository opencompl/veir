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
private def testLoopCarriesConstantThroughUnknownBackedge : String :=
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
