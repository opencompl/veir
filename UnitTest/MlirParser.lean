import Veir.Parser.MlirParser
import Veir.IR.Basic
import Veir.Printer

open Veir
open Veir.Parser

/--
  Parse an operation and print it.
-/
def testParseOp (s : String) : IO Unit :=
  match IRContext.create with
  | some (ctx, _) =>
    match ParserState.fromInput (s.toByteArray) with
    | .ok parser =>
      match (parseOp none).run (MlirParserState.fromContext ctx) parser with
      | .ok (op, state, _) => Printer.printOperation state.ctx op
      | .error err => .error err
    | .error err => .error err
  | none => .error "internal error: failed to create IR context"

/--
  info: "arith.addi"() ({
  ^4():
    "arith.muli"() : () -> ()
}, {}) : () -> ()
-/
#guard_msgs in
#eval! testParseOp "\"arith.addi\"() ({
  \"arith.muli\"() : () -> ()
}, {}) : () -> ()"


/--
  info: "arith.addi"() ({
  ^4():
    %5 = "arith.muli"() : () -> i32
}, {}) : () -> ()
-/
#guard_msgs in
#eval! testParseOp "\"arith.addi\"() ({
  %x = \"arith.muli\"() : () -> i32
}, {}) : () -> ()"


/--
  info: "arith.addi"() ({
  ^4():
    %5_0, %5_1 = "arith.muli"() : () -> (i32, i32)
}, {}) : () -> ()
-/
#guard_msgs in
#eval! testParseOp "\"arith.addi\"() ({
  %x, %y = \"arith.muli\"() : () -> (i32, i32)
}, {}) : () -> ()"

/--
  info: "arith.addi"() ({
  ^4():
    %5 = "arith.constant"() <{"value" = 12 : i32}> : () -> i32
    %6 = "arith.constant"() <{"value" = 0 : i32}> : () -> i32
    %7 = "arith.muli"(%5, %6) : (i32, i32) -> i32
}) : () -> ()
-/
#guard_msgs in
#eval! testParseOp r#""arith.addi"() ({
  %a = "arith.constant"() <{ value = 12 : i32 }> : () -> i32
  %b = "arith.constant"() <{ value = 0 : i32 }> : () -> i32
  %c = "arith.muli"(%a, %b) : (i32, i32) -> i32
}) : () -> ()"#

/--
  error: type mismatch for value %a: expected i32, got i64
-/
#guard_msgs in
#eval! testParseOp r#""arith.addi"() ({
  %a = "arith.constant"() <{ value = 0 : i64 }> : () -> i64
  %c = "arith.muli"(%a, %a) : (i32, i32) -> i32
}) : () -> ()"#

/--
  error: operation 'arith.muli' declares 2 operand types, but 1 operands were provided
-/
#guard_msgs in
#eval! testParseOp r#""arith.addi"() ({
  %a = "arith.constant"() <{ value = 0 : i64 }> : () -> i64
  %c = "arith.muli"(%a) : (i32, i32) -> i32
}) : () -> ()"#

/--
  info: "builtin.module"() ({
  ^4():
    %5 = "arith.constant"() <{"value" = 13 : i64}> : () -> i64
}) : () -> ()-/
#guard_msgs in
#eval! testParseOp r#""builtin.module"() ({
^bb0:
  %a = "arith.constant"() <{ value = 13 : i64 }> : () -> i64
}) : () -> ()"#

/--
  info: "builtin.module"() ({
  ^4(%arg4_0 : i32, %arg4_1 : i32):
    %5 = "arith.addi"(%arg4_0, %arg4_1) : (i32, i32) -> i32
}) : () -> ()-/
#guard_msgs in
#eval! testParseOp "\"builtin.module\"() ({
^bb0(%x : i32, %y : i32):
  %a = \"arith.addi\"(%x, %y) : (i32, i32) -> (i32)
}) : () -> ()"

/--
  info: "builtin.module"() ({
  ^4():
    "builtin.module"() ({
      ^6():
        %7 = "arith.constant"() <{"value" = 13 : i64}> : () -> i64
    }) : () -> ()
}) : () -> ()-/
#guard_msgs in
#eval! testParseOp r#""builtin.module"() ({
  "builtin.module"() ({
    %a = "arith.constant"() <{ value = 13 : i64 }> : () -> i64
  }) : () -> ()
}) : () -> ()"#

/--
  info: "builtin.module"() ({
  ^4():
    "test.test"() [^5] : () -> ()
  ^5():
    "test.test"() [^7] : () -> ()
  ^7():
    "test.test"() [^5] : () -> ()
}) : () -> ()-/
#guard_msgs in
#eval! testParseOp "\"builtin.module\"() ({
^bb0:
  \"test.test\"() [^bb1] : () -> ()
^bb1:
  \"test.test\"() [^bb2] : () -> ()
^bb2:
  \"test.test\"() [^bb1] : () -> ()
}) : () -> ()"

/--
  error: block %bb0 was declared but not defined
-/
#guard_msgs in
#eval! testParseOp "\"builtin.module\"() ({
  \"test.test\"() [^bb0] : () -> ()
}) : () -> ()"

/--
  error: block %bb0 was declared but not defined
-/
#guard_msgs in
#eval! testParseOp "\"builtin.module\"() ({
^bb0:
  \"builtin.module\"() ({
    \"test.test\"() [^bb0] : () -> ()
  }) : () -> ()
}) : () -> ()"
