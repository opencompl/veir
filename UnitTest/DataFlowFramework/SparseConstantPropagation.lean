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
  run
    r#""builtin.module"() ({
^bb0:
  %a = "arith.constant"() <{ value = 5 : i32 }> : () -> i32
  %b = "arith.constant"() <{ value = 7 : i32 }> : () -> i32
  %c = "arith.addi"(%a, %b) : (i32, i32) -> i32
}) : () -> ()"#
    #[ ("a", constInt 32 5)
     , ("b", constInt 32 7)
     , ("c", constInt 32 12)
     ]

private def testMuliAllConstant : String :=
  run
    r#""builtin.module"() ({
^bb0:
  %a = "arith.constant"() <{ value = 3 : i32 }> : () -> i32
  %b = "arith.constant"() <{ value = 2 : i32 }> : () -> i32
  %c = "arith.muli"(%a, %b) : (i32, i32) -> i32
}) : () -> ()"#
    #[ ("a", constInt 32 3)
     , ("b", constInt 32 2)
     , ("c", constInt 32 6)
     ]

private def testAndiAllConstant : String :=
  run
    r#""builtin.module"() ({
^bb0:
  %a = "arith.constant"() <{ value = 27 : i32 }> : () -> i32
  %b = "arith.constant"() <{ value = 3 : i32 }> : () -> i32
  %c = "arith.andi"(%a, %b) : (i32, i32) -> i32
}) : () -> ()"#
    #[ ("a", constInt 32 27)
     , ("b", constInt 32 3)
     , ("c", constInt 32 3)
     ]

private def testSubiAllConstant : String :=
  run
    r#""builtin.module"() ({
^bb0:
  %a = "arith.constant"() <{ value = 12 : i32 }> : () -> i32
  %b = "arith.constant"() <{ value = 37 : i32 }> : () -> i32
  %c = "arith.subi"(%a, %b) : (i32, i32) -> i32
}) : () -> ()"#
    #[ ("a", constInt 32 12)
     , ("b", constInt 32 37)
     , ("c", constInt 32 (-25))
     ]

private def testAddiUnknownOperand : String :=
  run
    r#""builtin.module"() ({
^bb0:
  %a = "arith.constant"() <{ value = -3 : i32 }> : () -> i32
  %u = "test.test"() : () -> i32
  %c = "arith.addi"(%a, %u) : (i32, i32) -> i32
}) : () -> ()"#
    #[ ("a", constInt 32 (-3))
     , ("u", ⊤)
     , ("c", ⊤)
     ]

private def testMuliUnknownOperand : String :=
  run
    r#""builtin.module"() ({
^bb0:
  %a = "arith.constant"() <{ value = 7 : i32 }> : () -> i32
  %u = "test.test"() : () -> i32
  %c = "arith.muli"(%a, %u) : (i32, i32) -> i32
}) : () -> ()"#
    #[ ("a", constInt 32 7)
     , ("u", ⊤)
     , ("c", ⊤)
     ]

private def testAndiUnknownOperand : String :=
  run
    r#""builtin.module"() ({
^bb0:
  %a = "arith.constant"() <{ value = -2 : i32 }> : () -> i32
  %u = "test.test"() : () -> i32
  %c = "arith.andi"(%a, %u) : (i32, i32) -> i32
}) : () -> ()"#
    #[ ("a", constInt 32 (-2))
     , ("u", ⊤)
     , ("c", ⊤)
     ]

private def testSubiUnknownOperand : String :=
  run
    r#""builtin.module"() ({
^bb0:
  %a = "arith.constant"() <{ value = 0 : i32 }> : () -> i32
  %u = "test.test"() : () -> i32
  %c = "arith.subi"(%a, %u) : (i32, i32) -> i32
}) : () -> ()"#
    #[ ("a", constInt 32 0)
     , ("u", ⊤)
     , ("c", ⊤)
     ]

private def testStandalonePropagatesAcrossLiveByDefaultEdge : String :=
  run
    r#""builtin.module"() ({
^bb0:
  %x = "arith.constant"() <{ value = 1 : i32 }> : () -> i32
  "test.test"(%x, %x)[^bb1] : (i32, i32) -> ()
^bb1(%dead : i32, %y : i32):
  %z = "arith.addi"(%y, %y) : (i32, i32) -> i32
}) : () -> ()"#
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
