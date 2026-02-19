import Veir.Transforms.ModArith
import Veir.Parser.MlirParser
import Veir.PatternRewriter.Basic
import Veir.Printer

open Veir
open Veir.Parser

set_option warn.sorry false in
def testPattern (pattern : RewritePattern) (s : String) : IO Unit := do
  let some (ctx, _) := IRContext.create
    | throw (IO.userError "internal error: failed to create IR context")
  let parser ← match ParserState.fromInput s.toByteArray with
    | .ok parser => pure parser
    | .error err => throw (IO.userError err)
  let (topOp, state, _) ←
    match (parseOp none).run (MlirParserState.fromContext ctx) parser with
    | .ok parsed => pure parsed
    | .error err => throw (IO.userError err)
  let some rewritten := RewritePattern.applyInContext
      pattern state.ctx sorry
    | throw (IO.userError "rewrite failed")
  Printer.printOperation rewritten topOp

set_option warn.sorry false in
def testBarretReducePattern (s : String) : IO Unit := do
  testPattern Veir.Transforms.ModArith.barretReduceRewriterPattern s

set_option warn.sorry false in
def testSubIfGePattern (s : String) : IO Unit := do
  testPattern Veir.Transforms.ModArith.subIfGeRewriterPattern s

set_option warn.sorry false in
def testReducePattern (s : String) : IO Unit := do
  testPattern Veir.Transforms.ModArith.reduceRewriterPattern s

/--
  info: "builtin.module"() ({
  ^4():
    "func.func"() ({
      ^6(%arg6_0 : i10):
        %11 = "arith.constant"() <{ "value" = 60 : i15 }> : () -> i15
        %12 = "arith.constant"() <{ "value" = 10 : i15 }> : () -> i15
        %13 = "arith.constant"() <{ "value" = 17 : i15 }> : () -> i15
        %14 = "arith.extui"(%arg6_0) : (i10) -> i15
        %15 = "arith.muli"(%14, %11) : (i15, i15) -> i15
        %16 = "arith.shrui"(%15, %12) : (i15, i15) -> i15
        %17 = "arith.muli"(%16, %13) : (i15, i15) -> i15
        %18 = "arith.subi"(%14, %17) : (i15, i15) -> i15
        %19 = "arith.trunci"(%18) : (i15) -> i10
        "func.return"(%19) : (i10) -> ()
    }) : () -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! testBarretReducePattern r#""builtin.module"() ({
  "func.func"() <{function_type = (i10) -> i10, sym_name = "test_lower_barrett_reduce_int"}> ({
  ^bb0(%arg0: i10):
    %0 = "mod_arith.barrett_reduce"(%arg0) <{modulus = 17 : i64}> : (i10) -> i10
    "func.return"(%0) : (i10) -> ()
  }) : () -> ()
}) : () -> ()"#

/--
  info: "builtin.module"() ({
  ^4():
    "func.func"() ({
      ^6(%arg6_0 : i10, %arg6_1 : i10):
        %11 = "arith.subi"(%arg6_0, %arg6_1) : (i10, i10) -> i10
        %12 = "arith.cmpi"(%arg6_0, %arg6_1) : (i10, i10) -> i1
        %13 = "arith.select"(%12, %11, %arg6_0) : (i1, i10, i10) -> i10
        "func.return"(%13) : (i10) -> ()
    }) : () -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! testSubIfGePattern r#""builtin.module"() ({
  "func.func"() <{function_type = (i10, i10) -> i10, sym_name = "test_lower_subifge_int"}> ({
  ^bb0(%arg0: i10, %arg1: i10):
    %0 = "mod_arith.subifge"(%arg0, %arg1) : (i10, i10) -> i10
    "func.return"(%0) : (i10) -> ()
  }) : () -> ()
}) : () -> ()"#

/--
  info: "builtin.module"() ({
  ^4():
    "func.func"() ({
      ^6(%arg6_0 : i10):
        %7 = "mod_arith.encapsulate"(%arg6_0) : (i10) -> !mod_arith.int<17 : i10>
        %13 = "mod_arith.extract"(%7) : (!mod_arith.int<17 : i10>) -> i10
        %14 = "mod_arith.barrett_reduce"(%13) <{ "modulus" = 17 : i10 }> : (i10) -> i10
        %15 = "arith.constant"() <{ "value" = 17 : i10 }> : () -> i10
        %16 = "mod_arith.subifge"(%14, %15) : (i10, i10) -> i10
        %17 = "mod_arith.encapsulate"(%16) : (i10) -> !mod_arith.int<17 : i10>
        %9 = "mod_arith.extract"(%17) : (!mod_arith.int<17 : i10>) -> i10
        "func.return"(%9) : (i10) -> ()
    }) : () -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! testReducePattern r#""builtin.module"() ({
  "func.func"() <{function_type = (i10) -> i10, sym_name = "test_lower_reduce_int"}> ({
  ^bb0(%arg0: i10):
    %0 = "mod_arith.encapsulate"(%arg0) : (i10) -> !mod_arith.int<17 : i10>
    %1 = "mod_arith.reduce"(%0) : (!mod_arith.int<17 : i10>) -> !mod_arith.int<17 : i10>
    %2 = "mod_arith.extract"(%1) : (!mod_arith.int<17 : i10>) -> i10
    "func.return"(%2) : (i10) -> ()
  }) : () -> ()
}) : () -> ()"#
