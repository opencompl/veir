import Veir.Parser.MlirParser
import Veir.Printer
import Veir.IR.Basic
import Veir.Verifier

open Veir.Parser
open Veir

private def bytePosToLineCol (input : ByteArray) (pos : Nat) : Nat × Nat := Id.run do
  let mut line := 1
  let mut col := 1
  let endPos := Nat.min pos input.size
  let mut i := 0
  while i < endPos do
    if input.getD i 0 = '\n'.toUInt8 then
      line := line + 1
      col := 1
    else
      col := col + 1
    i := i + 1
  (line, col)

private def lineBoundsAt (input : ByteArray) (pos : Nat) : Nat × Nat := Id.run do
  let p := Nat.min pos input.size
  let mut start := p
  while start > 0 && input.getD (start - 1) 0 != '\n'.toUInt8 do
    start := start - 1
  let mut stop := p
  while stop < input.size && input.getD stop 0 != '\n'.toUInt8 do
    stop := stop + 1
  (start, stop)

private def parserFailureContext (state : ParserState) : String := Id.run do
  let tok := state.currentToken
  let pos := tok.slice.start
  let (line, col) := bytePosToLineCol state.input pos
  let tokText := (String.fromUTF8? (tok.slice.of state.input)).getD "<non-utf8>"
  let (lineStart, lineStop) := lineBoundsAt state.input pos
  let lineText := (String.fromUTF8? (({ start := lineStart, stop := lineStop } : Lexer.Slice).of state.input)).getD "<non-utf8 line>"
  let caret := String.ofList (List.replicate (Nat.max (col - 1) 0) ' ') ++ "^"
  s!"at line {line}, column {col} (byte {pos}) near token {tok.kind} '{tokText}'\n{lineText}\n{caret}"

def parseOperation (filename : String) : ExceptT String IO (IRContext × OperationPtr) := do
  let fileContent ← IO.FS.readBinFile filename
  let some (ctx, _) := IRContext.create
    | throw "Failed to create IR context"
  match ParserState.fromInput fileContent with
  | .ok parser =>
    match (StateT.run (parseOp none) (MlirParserState.fromContext ctx)).run parser with
    | .ok (op, state) _ =>
      return (state.ctx, op)
    | .error errMsg parserState =>
      throw s!"Error parsing operation: {errMsg}\n{parserFailureContext parserState}"
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
