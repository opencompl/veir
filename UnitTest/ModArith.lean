import Veir.Transforms.ModArith
import Veir.Parser.MlirParser
import Veir.PatternRewriter.Basic
import Veir.Printer

open Veir
open Veir.Parser

set_option warn.sorry false in
def testBarretReducePattern (s : String) : IO Unit := do
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
      Veir.Transforms.ModArith.barretReduceRewriterPattern state.ctx sorry
    | throw (IO.userError "rewrite failed")
  Printer.printOperation rewritten topOp

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
