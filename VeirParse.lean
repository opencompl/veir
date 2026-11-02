import Veir.Parser.MlirParser
import Veir.Parser.PrintIR

/-!
# `veir-parse`

Parses an MLIR file in generic form into the buffered IR, reports the parse time, and
optionally prints the parsed module back.

```
veir-parse <file> [--allow-unregistered-dialect] [--print] [--lex-only] [--repeat=N]
```
-/

open Veir Veir.Parser

structure Args where
  filename : Option String := none
  allowUnregisteredDialect : Bool := false
  print : Bool := false
  lexOnly : Bool := false
  repeatCount : Nat := 1

def parseArgs (args : List String) : Except String Args := do
  let mut result : Args := {}
  for arg in args do
    if arg = "--allow-unregistered-dialect" then
      result := { result with allowUnregisteredDialect := true }
    else if arg = "--lex-only" then
      result := { result with lexOnly := true }
    else if arg = "--print" then
      result := { result with print := true }
    else if arg.startsWith "--repeat=" then
      let some n := (arg.drop 9).toString.toNat?
        | throw s!"invalid repeat count in '{arg}'"
      result := { result with repeatCount := n }
    else if arg.startsWith "-" then
      throw s!"unrecognized flag '{arg}'"
    else if result.filename.isSome then
      throw "expected at most one input file"
    else
      result := { result with filename := some arg }
  return result

def readInput (filename : Option String) : IO ByteArray := do
  match filename with
  | some f => IO.FS.readBinFile f
  | none => IO.FS.Stream.readBinToEnd (← IO.getStdin)

def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error msg =>
    IO.eprintln s!"Error: {msg}"
    IO.eprintln "Usage: veir-parse <file> [--allow-unregistered-dialect] [--print] [--lex-only] [--repeat=N]"
    return 1
  | .ok args =>
    let content ← readInput args.filename
    let sourceName := args.filename.getD "<stdin>"
    if args.lexOnly then
      for _ in [0:args.repeatCount] do
        let start ← IO.monoNanosNow
        let mut state : Lexer.LexerState := { input := content, pos := { byteOffset := 0 } }
        let mut count := 0
        repeat
          match Lexer.lex state with
          | .error err =>
            IO.eprintln (err.format sourceName content)
            return 1
          | .ok (token, state') =>
            state := state'
            count := count + 1
            if token.kind = .eof then break
        let stop ← IO.monoNanosNow
        IO.eprintln s!"lex time (s): {(stop - start).toFloat / 1000000000} ({count} tokens)"
      return 0
    let mut last : Option (IR.Context × IR.Op) := none
    for _ in [0:args.repeatCount] do
      let start ← IO.monoNanosNow
      match parseSourceString content sourceName args.allowUnregisteredDialect with
      | .error err =>
        IO.eprintln err
        return 1
      | .ok (ctx, op, _) =>
        let stop ← IO.monoNanosNow
        IO.eprintln s!"parse time (s): {(stop - start).toFloat / 1000000000}"
        last := some (ctx, op)
    if args.print then
      if let some (ctx, op) := last then
        PrintIR.printModule ctx op
    return 0
