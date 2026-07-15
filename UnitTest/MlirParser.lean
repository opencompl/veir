import Veir.IR.Basic
import Veir.Parser.MlirParser
import Veir.Printer
import Veir.Rewriter.WfRewriter

open Veir
open Veir.Parser

/--
  Parse an operation and print it.
-/
def testParseOp (s : String) : IO Unit :=
  match WfIRContext.create OpCode with
  | some (ctx, _) =>
    match ParserState.fromInput (s.toByteArray) with
    | .ok parser =>
      match parseTopLevelOp.run (MlirParserState.fromContext ctx) parser with
      | .ok (op, state, _) => Printer.printOperation state.ctx op
      | .error err => .error (toString err)
    | .error err => .error (toString err)
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
    %5:2 = "arith.muli"() : () -> (i32, i32)
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
  ^4(%arg4_0 : i32, %arg4_1 : i32):
    %5 = "arith.addi"(%arg4_0, %arg4_1) <{"overflowFlags" = #arith.overflow<nsw, nuw>}> : (i32, i32) -> i32
}) : () -> ()-/
#guard_msgs in
#eval! testParseOp "\"builtin.module\"() ({
^bb0(%x : i32, %y : i32):
  %a = \"arith.addi\"(%x, %y) <{ overflowFlags = #arith.overflow<nsw, nuw> }> : (i32, i32) -> i32
}) : () -> ()"

/--
  error: expected 'overflowFlags' to be an arith integer overflow flags attribute, but got 1 : i32
-/
#guard_msgs in
#eval! testParseOp "\"builtin.module\"() ({
^bb0(%x : i32, %y : i32):
  %a = \"arith.addi\"(%x, %y) <{ overflowFlags = 1 : i32 }> : (i32, i32) -> i32
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
  info: "builtin.module"() ({
  ^4():
    %5:2 = "test.test"() : () -> (i32, i64)
}) : () -> ()
-/
#guard_msgs in
#eval! testParseOp "\"builtin.module\"() ({
  %x:2 = \"test.test\"() : () -> (i32, i64)
}) : () -> ()"

/--
  info: "builtin.module"() ({
  ^4():
    %5:3 = "test.test"() : () -> (i10, i32, i64)
    %6 = "test.test"(%5#2, %5#0) : (i64, i10) -> i1
}) : () -> ()
-/
#guard_msgs in
#eval! testParseOp "\"builtin.module\"() ({
  %a, %x:2 = \"test.test\"() : () -> (i10, i32, i64)
  %b = \"test.test\"(%x#1, %a#0) : (i64, i10) -> i1
}) : () -> ()"

/--
  error: invalid result index 2 for %a
-/
#guard_msgs in
#eval! testParseOp "\"builtin.module\"() ({
  %a:2 = \"test.test\"() : () -> (i32, i64)
  %b = \"test.test\"(%a#2) : (i32) -> i1
}) : () -> ()"

/--
  error: type mismatch for value %a#1: expected i32, got i64
-/
#guard_msgs in
#eval! testParseOp "\"builtin.module\"() ({
  %a:2 = \"test.test\"() : () -> (i32, i64)
  %b = \"test.test\"(%a#1) : (i32) -> i1
}) : () -> ()"

/--
  error: operation 'test.test' declares 4 result types, but 3 result values were provided
-/
#guard_msgs in
#eval! testParseOp "\"builtin.module\"() ({
  %a, %b:2 = \"test.test\"() : () -> (i1, i2, i3, i4)
}) : () -> ()"

/--
  error: operation 'test.test' declares 2 result types, but 3 result values were provided
-/
#guard_msgs in
#eval! testParseOp "\"builtin.module\"() ({
  %a:2, %b = \"test.test\"() : () -> (i1, i2)
}) : () -> ()"

/--
  error: use of undefined value %a
-/
#guard_msgs in
#eval! testParseOp r#""builtin.module"() ({
  "test.test"(%a) : (i32) -> ()
}) : () -> ()"#

/--
  error: use of undefined value %a
-/
#guard_msgs in
#eval! testParseOp r#""builtin.module"() ({
  "test.test"(%a#2) : (i32) -> ()
}) : () -> ()"#

/--
  error: use of undefined value %a
-/
#guard_msgs in
#eval! testParseOp r#""builtin.module"() ({
  "test.test"() ({
    %a = "test.test"() : () -> i32
  }) : () -> ()
  "test.test"(%a) : (i32) -> ()
}) : () -> ()"#

/--
  error: value %a has already been defined
-/
#guard_msgs in
#eval! testParseOp r#""builtin.module"() ({
  %a = "test.test"() : () -> i32
  %a = "test.test"() : () -> i32
}) : () -> ()"#

/--
  error: value %a has already been defined
-/
#guard_msgs in
#eval! testParseOp r#""builtin.module"() ({
  %a = "test.test"() : () -> i32
  "test.test"() ({
    %a = "test.test"() : () -> i32
  }) : () -> ()
}) : () -> ()"#

/--
  error: value %a has already been defined
-/
#guard_msgs in
#eval! testParseOp r#""builtin.module"() ({
^bb0:
  %a = "test.test"() : () -> i32
^bb1:
  %a = "test.test"() : () -> i32
}) : () -> ()"#

/-!
## Forward references to SSA values

The parser accepts textual forward references to SSA values by creating a placeholder
for the not-yet-defined value and resolving it once the definition is parsed. Dominance
is not checked by the parser.
-/

/--
  info: "builtin.module"() ({
  ^4():
    "test.test"() [^5] : () -> ()
  ^5():
    "test.test"(%10) : (i32) -> ()
  ^9():
    %10 = "test.test"() : () -> i32
}) : () -> ()
-/
#guard_msgs in
#eval! testParseOp r#""builtin.module"() ({
^bb0:
  "test.test"() [^bb1] : () -> ()
^bb1:
  "test.test"(%v) : (i32) -> ()
^bb2:
  %v = "test.test"() : () -> i32
}) : () -> ()"#

/--
  info: "builtin.module"() ({
  ^4():
    %6 = "test.test"(%7) : (i32) -> i32
    %7 = "test.test"() : () -> i32
}) : () -> ()
-/
#guard_msgs in
#eval! testParseOp r#""builtin.module"() ({
  %b = "test.test"(%a) : (i32) -> i32
  %a = "test.test"() : () -> i32
}) : () -> ()"#

/--
  info: "builtin.module"() ({
  ^4():
    "test.test"() [^5] : () -> ()
  ^5():
    %8 = "test.test"(%10#1) : (i64) -> i32
  ^9():
    %10:2 = "test.test"() : () -> (i32, i64)
}) : () -> ()
-/
#guard_msgs in
#eval! testParseOp r#""builtin.module"() ({
^bb0:
  "test.test"() [^bb1] : () -> ()
^bb1:
  %b = "test.test"(%a#1) : (i64) -> i32
^bb2:
  %a:2 = "test.test"() : () -> (i32, i64)
}) : () -> ()"#

/--
  error: definition of value %a#0 has type i64 but was used with type i32
-/
#guard_msgs in
#eval! testParseOp r#""builtin.module"() ({
  %b = "test.test"(%a) : (i32) -> i32
  %a = "test.test"() : () -> i64
}) : () -> ()"#

/--
  error: type mismatch for value %a: expected i64, got i32
-/
#guard_msgs in
#eval! testParseOp r#""builtin.module"() ({
  %b = "test.test"(%a) : (i32) -> i32
  %c = "test.test"(%a) : (i64) -> i32
  %a = "test.test"() : () -> i32
}) : () -> ()"#

-- A forward reference resolves to the first textual definition of the name, even one inside
-- a nested region (MLIR's generic-form parser keeps a flat SSA name table). Legality under
-- dominance / IsolatedFromAbove is deferred to future implementation (for details see
-- `ForwardValue` in `Veir.Parser.MlirParser`).
/--
info: "builtin.module"() ({
  ^4():
    "test.test"(%9) : (i32) -> ()
    "test.test"() ({
      ^8():
        %9 = "test.test"() : () -> i32
    }) : () -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! testParseOp r#""builtin.module"() ({
  "test.test"(%a) : (i32) -> ()
  "test.test"() ({
    %a = "test.test"() : () -> i32
  }) : () -> ()
}) : () -> ()"#

/--
  error: use of undefined value %a
-/
#guard_msgs in
#eval! testParseOp r#""builtin.module"() ({
  "test.test"(%a) : (i32) -> ()
}) : () -> ()"#
