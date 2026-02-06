import Veir.IR.Basic
import Veir.Parser.MlirParser
import Veir.IR.Dominance
import Veir.Printer

open Veir
open Veir.Parser

open Veir

/--
  Parse an operation and print it.
-/
def testParseOp (s : String) : IO Unit :=
  match IRContext.create with
  | some (ctx, _) =>
    match ParserState.fromInput (s.toByteArray) with
    | .ok parser =>
      match (parseOp none).run (MlirParserState.fromContext ctx) parser with
      | .ok (op, state, _) => do
          dbg_trace "debug: IRContext"
          dbg_trace (reprStr state.ctx)
          dbg_trace "debug: region0"
          let region0 := (op.getRegion! state.ctx 0).get! state.ctx
          Printer.printRegion state.ctx region0
          dbg_trace ""
          dbg_trace "debug: module"
          Printer.printOperation state.ctx op
          dbg_trace "debug: domctx"
          let dom := (op.getRegion! state.ctx 0).computeDomTree! ({} : DomContext) state.ctx
          dbg_trace (reprStr dom)
      | .error err => .error err
    | .error err => .error err
  | none => .error "internal error: failed to create IR context"


def debugPrint : IO Unit := do
  IO.println "debug: hello from UnitTest.Debug"
  let mlir := "\"builtin.module\"() ({
^bb0:
  \"test.test\"() [^bb1] : () -> ()
^bb1:
  \"test.test\"() [^bb2] : () -> ()
^bb2:
  \"test.test\"() [^bb1] : () -> ()
}) : () -> ()"
  testParseOp mlir

#eval! debugPrint
