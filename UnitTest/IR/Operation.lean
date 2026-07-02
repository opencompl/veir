import Veir.IR.Basic
import Veir.Parser.MlirParser

open Veir
open Veir.Parser

private def parse (s : String) : OperationPtr × IRContext OpCode :=
  match WfIRContext.create OpCode with
  | none => panic! "failed to create IR context"
  | some (ctx, _) =>
    match ParserState.fromInput s.toByteArray with
    | .error _ => panic! "lex error"
    | .ok parser =>
      match parseTopLevelOp.run (MlirParserState.fromContext ctx) parser with
      | .error _ => panic! "parse error"
      | .ok (op, state, _) => (op, state.ctx.raw)

private def noRegions := parse r#""arith.muli"() : () -> ()"#
#guard noRegions.1.getNumRegions! noRegions.2 == 0

private def oneRegion := parse r#""arith.addi"() ({
  "arith.muli"() : () -> ()
}) : () -> ()"#
#guard oneRegion.1.getNumRegions! oneRegion.2 == 1

private def twoRegions := parse r#""arith.addi"() ({
  "arith.muli"() : () -> ()
}, {
  "arith.muli"() : () -> ()
}) : () -> ()"#
#guard twoRegions.1.getNumRegions! twoRegions.2 == 2
#guard (twoRegions.1.getRegions! twoRegions.2).size == twoRegions.1.getNumRegions! twoRegions.2
#guard (twoRegions.1.getRegions! twoRegions.2)[0]! == twoRegions.1.getRegion! twoRegions.2 0
#guard (twoRegions.1.getRegions! twoRegions.2)[1]! == twoRegions.1.getRegion! twoRegions.2 1
