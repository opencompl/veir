import Veir.Parser.MlirParser
import Veir.Printer
import Veir.IR.Basic
import Veir.Verifier

open Veir.Parser
open Veir

def parseOperation (filename : String) : ExceptT String IO (IRContext × OperationPtr) := do
  let fileContent ← IO.FS.readBinFile filename
  let some (ctx, _) := IRContext.create
    | throw "Failed to create IR context"
  match ParserState.fromInput fileContent with
  | .ok parser =>
    match (parseOp none).run (MlirParserState.fromContext ctx) parser with
    | .ok (op, state, _) =>
      return (state.ctx, op)
    | .error errMsg =>
      throw s!"Error parsing operation: {errMsg}"
  | .error errMsg =>
    throw s!"Error reading file: {errMsg}"

def main (args : List String) : IO Unit := do
  match args with
  | [filename] =>
    match ← parseOperation filename with
    | .ok (ctx, op) =>
      match ctx.verify with
      | .ok _ => Veir.Printer.printOperation ctx op
      | .error errMsg => IO.eprintln s!"Error verifying input program: {errMsg}"
    | .error errMsg =>
      IO.eprintln s!"Error: {errMsg}"
  | _ =>
    IO.eprintln "Wrong number of arguments."
    IO.eprintln "Usage: veir-opt <filename>"
