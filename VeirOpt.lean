import Veir.Parser.MlirParser
import Veir.Parser.DecidableInBounds
import Veir.Printer
import Veir.IR.Basic
import Veir.Verifier
import Veir.Properties
import Veir.Pass
import Veir.Rewriter.GetSetInBounds

import Veir.Passes.PrintIR
import Veir.Passes.InstCombine

open Veir.Parser
open Veir

/--
  A map of all available compilation passes, keyed by their unique names.
-/
def availablePasses : Std.HashMap String (Pass OpCode) :=
  (Std.HashMap.emptyWithCapacity 1)
    |>.insert PrintIRPass.name PrintIRPass
    |>.insert InstCombinePass.name InstCombinePass

/--
  Arguments for the `veir-opt` command-line tool, parsed from the CLI.
-/
structure VeirOptArgs where
  /-- The input filename. -/
  filename : String
  /-- List of passes to run. -/
  passes : PassPipeline OpCode

/--
  Parse the `-p` flag to construct a pass pipeline.
  Returns an error if the flag is malformed or if any pass name is unknown.
-/
def parsePipelineOption (args : List String) : Except String (PassPipeline OpCode) := do
  let passesFlags := args.filter (·.startsWith "-p=")
  match passesFlags with
  | [] => return { passes := #[] }
  | [flag] =>
    let arg := (flag.drop 3).toString
    match PassPipeline.ofString? availablePasses arg with
    | .ok pipeline => return pipeline
    | .error errMsg => .error s!"Error parsing -p flag: {errMsg}"
  | _ => .error "Expected at most one -p flag."

/--
  Parse CLI arguments. Returns an error if the arguments are malformed.
-/
def parseArgs (args : List String) : Except String VeirOptArgs := do
  let (flags, positional) := args.partition (·.startsWith "-")
  let [filename] := positional
    | .error "Expected exactly one positional argument for the input filename."
  -- Parses the `-p` flag if present.
  let pipeline ← parsePipelineOption flags
  return VeirOptArgs.mk filename pipeline

/-- Result of parsing, bundled with proofs -/
structure ParseResult where
  ctx : IRContext OpCode
  op : OperationPtr
  hctx : ctx.FieldsInBounds

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
        return ⟨state.ctx, op, state.hctx⟩
      | .error errMsg =>
        throw s!"Error parsing operation: {errMsg}"
    | .error errMsg =>
      throw s!"Error reading file: {errMsg}"

set_option warn.sorry false in
def main (args : List String) : IO Unit := do
  match parseArgs args with
  | .error errMsg =>
    IO.eprintln s!"Error: {errMsg}"
    IO.eprintln "Usage: veir-opt <filename> [-p=\"pass1,pass2,...\"]"
  | .ok { filename, passes } =>
    match ← parseOperation filename with
    | .error errMsg =>
      IO.eprintln s!"Error: {errMsg}"
    | .ok ⟨ctx, op, _⟩ =>
      match ctx.verify with
      | .error errMsg =>
        IO.eprintln s!"Error verifying input program: {errMsg}"
      | .ok _ =>
        -- TODO: ctx.WellFormed needs proper verification
        match ← passes.run ⟨ctx, by sorry⟩ op with
        | .error errMsg =>
          IO.eprintln s!"Error: {errMsg}"
        | .ok finalCtx =>
          Veir.Printer.printOperation finalCtx.val op
