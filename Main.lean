import Veir.Parser.MlirParser
import Veir.Printer
import Veir.IR.Basic

open Veir.Parser
open Veir

def main (args : List String) : IO Unit := do
  match args with
  | [filename] =>
    let fileContent ← IO.FS.readBinFile filename
    let some (ctx, _) := IRContext.create | IO.println "Failed to create IR context"; return
    match ParserState.fromInput fileContent with
    | .ok parser =>
      match (parseOp none).run (MlirParserState.fromContext ctx) parser with
      | .ok (op, state, _) =>
        IO.println "Parsed Operation:"
        Veir.Printer.printOperation state.ctx op
      | .error errMsg => IO.eprintln s!"Error parsing operation: {errMsg}"
    | .error errMsg => IO.eprintln s!"Error reading file: {errMsg}"; return
  | _ =>
    IO.eprintln "Wrong number of arguments."
    IO.eprintln "Usage: veir_parser <filename>"
