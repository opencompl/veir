import Veir.Parser.MlirParser
import Veir.Parser.DecidableInBounds
import Veir.Printer
import Veir.IR.Basic
import Veir.Verifier
import Veir.Interpreter.Basic
import Veir.Rewriter.GetSetInBounds

/-!
  # Veir Interpreter CLI Tool

  This file implements a simple command-line tool that reads an MLIR file,
  and then executes the block of the builtin.module operation in it using
  the interpreter defined in `Veir.Interpreter`.
-/

open Veir.Parser
open Veir

/-- Result of parsing, bundled with proofs -/
structure ParseResult where
  ctx : IRContext OpCode
  op : OperationPtr
  hctx : ctx.FieldsInBounds
  hopIn : op.InBounds ctx

def parseOperation (filename : String) : ExceptT String IO ParseResult := do
  let fileContent ← IO.FS.readBinFile filename
  match hcreate : IRContext.create OpCode with
  | none => throw "Failed to create IR context"
  | some (ctx, _) =>
    have hctx : ctx.FieldsInBounds := (IRContext.create_fieldsInBounds hcreate).1
    match ParserState.fromInput fileContent with
    | .ok parser =>
      match (parseOp none).run (MlirParserState.fromContext ctx hctx) parser with
      | .ok (op, state, _) =>
        -- Use runtime check for op.InBounds
        let ⟨hopIn⟩ ← Veir.Parser.liftExcept (checkOpInBounds op state.ctx)
        return ⟨state.ctx, op, state.hctx, hopIn⟩
      | .error errMsg =>
        throw s!"Error parsing operation: {errMsg}"
    | .error errMsg =>
      throw s!"Error reading file: {errMsg}"

set_option warn.sorry false in
def main (args : List String) : IO Unit := do
  match args with
  | [filename] =>
    match ← parseOperation filename with
    | .ok ⟨ctx, op, _, hopIn⟩ =>
      match ctx.verify with
      | .ok _ =>
        -- TODO: ctx.WellFormed needs proper verification
        match interpretModule ctx op hopIn (by sorry) with
        | some results => IO.println s!"Program output: {results}"
        | none => IO.eprintln "Error while interpreting module"
      | .error errMsg => IO.eprintln s!"Error verifying input program: {errMsg}"
    | .error errMsg =>
      IO.eprintln s!"Error: {errMsg}"
  | _ =>
    IO.eprintln "Wrong number of arguments."
    IO.eprintln "Usage: veir-interpret <filename>"
