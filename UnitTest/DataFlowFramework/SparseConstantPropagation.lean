import UnitTest.DataFlowFramework.Helpers

import Veir.Analysis.DataFlow.Domains.ConstantDomain
import Veir.Analysis.DataFlow.SparseConstantPropagationAnalysis

open Veir

private def constInt (bitwidth : Nat) (value : Int) : AbstractConstant :=
  .constant ⟨bitwidth, Data.LLVM.Int.constant bitwidth value⟩

private def poisonInt (bitwidth : Nat) : AbstractConstant :=
  .constant ⟨bitwidth, .poison⟩

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

private def testConstantPropagatesAcrossEdge : String :=
  run
    r#""builtin.module"() ({
^bb0:
  %source = "arith.constant"() <{ value = 5 : i32 }> : () -> i32
  "cf.br"(%source) [^bb1] : (i32) -> ()
^bb1(%forwarded : i32):
}) : () -> ()"#
    #[ ("source", constInt 32 5)
     , ("forwarded", constInt 32 5)
     ]

/--
info: "ok"
-/
#guard_msgs in
#eval! testConstantPropagatesAcrossEdge

private def testPoisonConstantPropagatesAcrossEdge : String :=
  run
    r#""builtin.module"() ({
^bb0:
  %source = "llvm.mlir.poison"() : () -> i32
  "cf.br"(%source) [^bb1] : (i32) -> ()
^bb1(%forwarded : i32):
}) : () -> ()"#
    #[ ("source", poisonInt 32)
     , ("forwarded", poisonInt 32)
     ]

/--
info: "ok"
-/
#guard_msgs in
#eval! testPoisonConstantPropagatesAcrossEdge

private def testPoisonConstantFoldsWithUnknownOperand : String :=
  run
    r#""builtin.module"() ({
^bb0:
  %unknown = "test.test"() : () -> i32
  %poison = "llvm.mlir.poison"() : () -> i32
  %result = "arith.addi"(%unknown, %poison) : (i32, i32) -> i32
}) : () -> ()"#
    #[ ("unknown", ⊤)
     , ("poison", poisonInt 32)
     , ("result", poisonInt 32)
     ]

/--
info: "ok"
-/
#guard_msgs in
#eval! testPoisonConstantFoldsWithUnknownOperand

private def testConstantsPropagateByArgumentPosition : String :=
  run
    r#""builtin.module"() ({
^bb0:
  %first = "arith.constant"() <{ value = 3 : i32 }> : () -> i32
  %second = "arith.constant"() <{ value = 7 : i32 }> : () -> i32
  "cf.br"(%second, %first) [^bb1] : (i32, i32) -> ()
^bb1(%forwardedSecond : i32, %forwardedFirst : i32):
}) : () -> ()"#
    #[ ("forwardedSecond", constInt 32 7)
     , ("forwardedFirst", constInt 32 3)
     ]

/--
info: "ok"
-/
#guard_msgs in
#eval! testConstantsPropagateByArgumentPosition

private def testConstantPropagatesAcrossBlockChain : String :=
  run
    r#""builtin.module"() ({
^bb0:
  %source = "arith.constant"() <{ value = -25 : i32 }> : () -> i32
  "cf.br"(%source) [^bb1] : (i32) -> ()
^bb1(%middle : i32):
  "cf.br"(%middle) [^bb2] : (i32) -> ()
^bb2(%destination : i32):
}) : () -> ()"#
    #[ ("middle", constInt 32 (-25))
     , ("destination", constInt 32 (-25))
     ]

/--
info: "ok"
-/
#guard_msgs in
#eval! testConstantPropagatesAcrossBlockChain

private def testConditionalSuccessorOperandsPropagateIndependently : String :=
  run
    r#""builtin.module"() ({
^bb0:
  %condition = "test.test"() : () -> i32
  %trueValue = "arith.constant"() <{ value = 12 : i32 }> : () -> i32
  %falseValue = "arith.constant"() <{ value = 37 : i32 }> : () -> i32
  "cf.cond_br"(%condition, %trueValue, %falseValue) [^bb1, ^bb2]
    <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i32, i32, i32) -> ()
^bb1(%fromTrueEdge : i32):
^bb2(%fromFalseEdge : i32):
}) : () -> ()"#
    #[ ("fromTrueEdge", constInt 32 12)
     , ("fromFalseEdge", constInt 32 37)
     ]

/--
info: "ok"
-/
#guard_msgs in
#eval! testConditionalSuccessorOperandsPropagateIndependently

private def testSameConstantJoinsAcrossPredecessors : String :=
  run
    r#""builtin.module"() ({
^bb0:
  %left = "arith.constant"() <{ value = 42 : i32 }> : () -> i32
  "cf.br"(%left) [^bb2] : (i32) -> ()
^bb1:
  %right = "arith.constant"() <{ value = 42 : i32 }> : () -> i32
  "cf.br"(%right) [^bb2] : (i32) -> ()
^bb2(%joined : i32):
}) : () -> ()"#
    #[("joined", constInt 32 42)]

/--
info: "ok"
-/
#guard_msgs in
#eval! testSameConstantJoinsAcrossPredecessors

private def testDifferentConstantsJoinToTop : String :=
  run
    r#""builtin.module"() ({
^bb0:
  %left = "arith.constant"() <{ value = -3 : i32 }> : () -> i32
  "cf.br"(%left) [^bb2] : (i32) -> ()
^bb1:
  %right = "arith.constant"() <{ value = 9 : i32 }> : () -> i32
  "cf.br"(%right) [^bb2] : (i32) -> ()
^bb2(%joined : i32):
}) : () -> ()"#
    #[("joined", ⊤)]

/--
info: "ok"
-/
#guard_msgs in
#eval! testDifferentConstantsJoinToTop

private def testConstantAndUnknownJoinToTop : String :=
  run
    r#""builtin.module"() ({
^bb0:
  %known = "arith.constant"() <{ value = 7 : i32 }> : () -> i32
  "cf.br"(%known) [^bb2] : (i32) -> ()
^bb1:
  %unknown = "test.test"() : () -> i32
  "cf.br"(%unknown) [^bb2] : (i32) -> ()
^bb2(%joined : i32):
}) : () -> ()"#
    #[ ("unknown", ⊤)
     , ("joined", ⊤)
     ]

/--
info: "ok"
-/
#guard_msgs in
#eval! testConstantAndUnknownJoinToTop

private def testEntryArgumentPropagatesAsTop : String :=
  run
    r#""builtin.module"() ({
^bb0(%input : i32):
  "cf.br"(%input) [^bb1] : (i32) -> ()
^bb1(%forwarded : i32):
}) : () -> ()"#
    #[ ("input", ⊤)
     , ("forwarded", ⊤)
     ]

/--
info: "ok"
-/
#guard_msgs in
#eval! testEntryArgumentPropagatesAsTop

private def testLatePredecessorUpdateRevisitsBlock : String :=
  run
    r#""builtin.module"() ({
^bb0:
  "cf.br"() [^bb2] : () -> ()
^bb1(%forwarded : i32):
^bb2:
  %late = "arith.constant"() <{ value = 19 : i32 }> : () -> i32
  "cf.br"(%late) [^bb1] : (i32) -> ()
}) : () -> ()"#
    #[ ("late", constInt 32 19)
     , ("forwarded", constInt 32 19)
     ]

/--
info: "ok"
-/
#guard_msgs in
#eval! testLatePredecessorUpdateRevisitsBlock

private def testLateConflictPropagatesTopThroughSuccessorChain : String :=
  run
    r#""builtin.module"() ({
^bb0:
  %first = "arith.constant"() <{ value = 1 : i32 }> : () -> i32
  "cf.br"(%first) [^bb1] : (i32) -> ()
^bb1(%joined : i32):
  "cf.br"(%joined) [^bb3] : (i32) -> ()
^bb2:
  %late = "arith.constant"() <{ value = 2 : i32 }> : () -> i32
  "cf.br"(%late) [^bb1] : (i32) -> ()
^bb3(%downstream : i32):
}) : () -> ()"#
    #[ ("joined", ⊤)
     , ("downstream", ⊤)
     ]

/--
info: "ok"
-/
#guard_msgs in
#eval! testLateConflictPropagatesTopThroughSuccessorChain
