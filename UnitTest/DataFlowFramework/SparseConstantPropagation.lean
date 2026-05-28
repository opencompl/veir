import UnitTest.DataFlowFramework.Helpers

import Veir.Analysis.DataFlow.Domains.ConstantDomain
import Veir.Analysis.DataFlow.SparseConstantPropagationAnalysis

open Veir

private def constInt (bitwidth : Nat) (value : Int) : AbstractConstant :=
  .constant ⟨bitwidth, Data.LLVM.Int.constant bitwidth value⟩

private def run
    (mlir : String)
    (expected : Array (String × AbstractConstant)) : String :=
  runWithAnalyses mlir #[Veir.SparseConstantPropagationAnalysis]
  (fun top dfCtx parserState => Id.run do
      match recoverNames top parserState.ctx mlir with
      | Except.error err =>
          return #[err]
      | Except.ok recovered =>
          checkNamedConstants dfCtx recovered.values expected)

private def testAddiAllConstant : String :=
  let mlir := "\"builtin.module\"() ({\n\
^bb0:\n\
  %a = \"arith.constant\"() <{ value = 5 : i32 }> : () -> i32\n\
  %b = \"arith.constant\"() <{ value = 7 : i32 }> : () -> i32\n\
  %c = \"arith.addi\"(%a, %b) : (i32, i32) -> i32\n\
}) : () -> ()"
  run mlir
    #[ ("a", constInt 32 5)
     , ("b", constInt 32 7)
     , ("c", constInt 32 12)
     ]

private def testMuliAllConstant : String :=
  let mlir := "\"builtin.module\"() ({\n\
^bb0:\n\
  %a = \"arith.constant\"() <{ value = 3 : i32 }> : () -> i32\n\
  %b = \"arith.constant\"() <{ value = 2 : i32 }> : () -> i32\n\
  %c = \"arith.muli\"(%a, %b) : (i32, i32) -> i32\n\
}) : () -> ()"
  run mlir
    #[ ("a", constInt 32 3)
     , ("b", constInt 32 2)
     , ("c", constInt 32 6)
     ]

private def testAndiAllConstant : String :=
  let mlir := "\"builtin.module\"() ({\n\
^bb0:\n\
  %a = \"arith.constant\"() <{ value = 27 : i32 }> : () -> i32\n\
  %b = \"arith.constant\"() <{ value = 3 : i32 }> : () -> i32\n\
  %c = \"arith.andi\"(%a, %b) : (i32, i32) -> i32\n\
}) : () -> ()"
  run mlir
    #[ ("a", constInt 32 27)
     , ("b", constInt 32 3)
     , ("c", constInt 32 3)
     ]

private def testSubiAllConstant : String :=
  let mlir := "\"builtin.module\"() ({\n\
^bb0:\n\
  %a = \"arith.constant\"() <{ value = 12 : i32 }> : () -> i32\n\
  %b = \"arith.constant\"() <{ value = 37 : i32 }> : () -> i32\n\
  %c = \"arith.subi\"(%a, %b) : (i32, i32) -> i32\n\
}) : () -> ()"
  run mlir
    #[ ("a", constInt 32 12)
     , ("b", constInt 32 37)
     , ("c", constInt 32 (-25))
     ]

private def testAddiUnknownOperand : String :=
  let mlir := "\"builtin.module\"() ({\n\
^bb0:\n\
  %a = \"arith.constant\"() <{ value = -3 : i32 }> : () -> i32\n\
  %u = \"test.test\"() : () -> i32\n\
  %c = \"arith.addi\"(%a, %u) : (i32, i32) -> i32\n\
}) : () -> ()"
  run mlir
    #[ ("a", constInt 32 (-3))
     , ("u", ⊤)
     , ("c", ⊤)
     ]

private def testMuliUnknownOperand : String :=
  let mlir := "\"builtin.module\"() ({\n\
^bb0:\n\
  %a = \"arith.constant\"() <{ value = 7 : i32 }> : () -> i32\n\
  %u = \"test.test\"() : () -> i32\n\
  %c = \"arith.muli\"(%a, %u) : (i32, i32) -> i32\n\
}) : () -> ()"
  run mlir
    #[ ("a", constInt 32 7)
     , ("u", ⊤)
     , ("c", ⊤)
     ]

private def testAndiUnknownOperand : String :=
  let mlir := "\"builtin.module\"() ({\n\
^bb0:\n\
  %a = \"arith.constant\"() <{ value = -2 : i32 }> : () -> i32\n\
  %u = \"test.test\"() : () -> i32\n\
  %c = \"arith.andi\"(%a, %u) : (i32, i32) -> i32\n\
}) : () -> ()"
  run mlir
    #[ ("a", constInt 32 (-2))
     , ("u", ⊤)
     , ("c", ⊤)
     ]

private def testSubiUnknownOperand : String :=
  let mlir := "\"builtin.module\"() ({\n\
^bb0:\n\
  %a = \"arith.constant\"() <{ value = 0 : i32 }> : () -> i32\n\
  %u = \"test.test\"() : () -> i32\n\
  %c = \"arith.subi\"(%a, %u) : (i32, i32) -> i32\n\
}) : () -> ()"
  run mlir
    #[ ("a", constInt 32 0)
     , ("u", ⊤)
     , ("c", ⊤)
     ]

private def testStandalonePropagatesAcrossLiveByDefaultEdge : String :=
  let mlir := "\"builtin.module\"() ({\n\
^bb0:\n\
  %x = \"arith.constant\"() <{ value = 1 : i32 }> : () -> i32\n\
  \"test.test\"(%x, %x)[^bb1] : (i32, i32) -> ()\n\
^bb1(%dead : i32, %y : i32):\n\
  %z = \"arith.addi\"(%y, %y) : (i32, i32) -> i32\n\
}) : () -> ()"
  run mlir
    #[ ("x", constInt 32 1)
     , ("y", constInt 32 1)
     , ("z", constInt 32 2)
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

/--
info: "ok"
-/
#guard_msgs in
#eval! testStandalonePropagatesAcrossLiveByDefaultEdge
