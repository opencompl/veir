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
      match (parseOp none).run (MlirParserState.mk ctx) parser with
      | .ok (op, state, _) => Printer.printOperation state.ctx op
      | .error err => .error err
    | .error err => .error err
  | none => .error "internal error: failed to create IR context"

/--
  info: arith.addi() {
  ^4:
    arith.muli()
}
{
  ^7:
}
-/
#guard_msgs in
#eval! testParseOp "\"arith.addi\"() ({
  \"arith.muli\"() : () -> ()
}, {}) : () -> ()"


/--
  info: arith.addi() {
  ^4:
    %5 = arith.muli()
}
{
  ^7:
}
-/
#guard_msgs in
#eval! testParseOp "\"arith.addi\"() ({
  %x = \"arith.muli\"() : () -> i32
}, {}) : () -> ()"


/--
  info: arith.addi() {
  ^4:
    %5_0, %5_1 = arith.muli()
}
{
  ^7:
}
-/
#guard_msgs in
#eval! testParseOp "\"arith.addi\"() ({
  %x, %y = \"arith.muli\"() : () -> (i32, i32)
}, {}) : () -> ()"
