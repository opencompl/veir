import Veir.Parser.MlirParser
import Veir.Parser.ParserError
import Veir.Printer
import Veir.IR.Basic
import Veir.Verifier
import Veir.Properties
import Veir.Pass
import Veir.Panic

import Veir.Passes.PrintIR
import Veir.Passes.InstCombine
import Veir.Passes.CSE
import Veir.Passes.InstructionSelection.RISCV64
import Veir.Passes.InstructionSelection.RISCV64Sdag
import Veir.Passes.InstructionSelection.RISCV64Branches
import Veir.Passes.DCE.dce
import Veir.Passes.CastsReconciliation.Reconciliation
import Veir.Passes.RISCVCombines.Combine
import Veir.Passes.ModArithToArith
import Veir.Passes.Canonicalize

open Veir.Parser
open Veir.Parser.ParserError
open Veir

/--
  A map of all available compilation passes, keyed by their unique names.
-/
def availablePasses : Std.HashMap String (Pass OpCode) :=
  (Std.HashMap.emptyWithCapacity 1)
    |>.insert PrintIRPass.name PrintIRPass
    |>.insert InstCombinePass.name InstCombinePass
    |>.insert CSEPass.name CSEPass
    |>.insert IselRISCV64.name IselRISCV64
    |>.insert IselSDAG.name IselSDAG
    |>.insert IselBrRISCV64.name IselBrRISCV64
    |>.insert DCEPass.name DCEPass
    |>.insert CastReconcilePass.name CastReconcilePass
    |>.insert RISCV.Combine.name RISCV.Combine
    |>.insert ModArithToArithPass.name ModArithToArithPass
    |>.insert CanonicalizePass.name CanonicalizePass

/--
  A map of named pass groups, each expanding to a comma-separated pipeline of pass names.
  Selected with the `-pgrp=` flag.
-/
def passGroups : Std.HashMap String String :=
  (Std.HashMap.emptyWithCapacity 2)
    |>.insert "O" "canonicalize,instcombine,cse,dce"
    |>.insert "riscv"
        "isel-br-riscv64,canonicalize,isel-sdag-riscv64,isel-riscv64,riscv-combine,reconcile-cast,dce"

/--
  A human-readable description of every pass group and the passes it expands to,
  used in the usage message.
-/
def passGroupsUsage : String :=
  String.intercalate "\n"
    ((passGroups.toList.toArray.qsort (·.1 < ·.1)).toList.map fun (name, passes) =>
      s!"    {name}: {passes}")

/--
  Arguments for the `veir-opt` command-line tool, parsed from the CLI.
-/
structure VeirOptArgs where
  /-- The input filename. -/
  filename : Option String
  /-- List of passes to run. -/
  passes : PassPipeline OpCode
  /-- Whether to accept ops/types/attrs from unregistered dialects. -/
  allowUnregisteredDialect : Bool

/--
  Parse the `-p` and `-pgrp` flags to construct a pass pipeline.
  `-p` takes a comma-separated list of pass names; `-pgrp` takes the name of a predefined
  pass group (see `passGroups`). The two flags are mutually exclusive, and at most one of
  each may appear. Both are optional.
  Returns an error if a flag is malformed or if any pass name / group is unknown.
-/
def parsePipelineOption (args : List String) :
    Except String (PassPipeline OpCode × List String) := do
  let (passesFlags, rest) := args.partition (·.startsWith "-p=")
  let (groupFlags, rest) := rest.partition (·.startsWith "-pgrp=")
  match passesFlags, groupFlags with
  | [], [] => return ({ passes := #[] }, rest)
  | [flag], [] =>
    let arg := (flag.drop 3).toString
    match PassPipeline.ofString? availablePasses arg with
    | .ok pipeline => return (pipeline, rest)
    | .error errMsg => .error s!"Error parsing -p flag: {errMsg}"
  | [], [flag] =>
    let groupName := (flag.drop 6).toString
    match passGroups.get? groupName with
    | some arg =>
      match PassPipeline.ofString? availablePasses arg with
      | .ok pipeline => return (pipeline, rest)
      | .error errMsg => .error s!"Error parsing -pgrp flag: {errMsg}"
    | none =>
      .error s!"Unknown pass group '{groupName}'. Available groups: {", ".intercalate passGroups.keys}"
  | _, _ =>
    .error "Expected at most one -p or -pgrp flag, and they are mutually exclusive."

/--
  Parse CLI arguments. Returns an error if the arguments are malformed.
-/
def parseArgs (args : List String) : Except String VeirOptArgs := do
  let (flags, positional) := args.partition (·.startsWith "-")
  -- Consume the `-p` flag if present.
  let (pipeline, flags) ← parsePipelineOption flags
  -- Consume `--allow-unregistered-dialect` if present.
  let allowUnregisteredDialect := flags.contains "--allow-unregistered-dialect"
  let flags := flags.filter (· != "--allow-unregistered-dialect")
  -- If anything survived, it was unrecognized and we error out.
  if let some flag := flags.head? then
    .error s!"Unrecognized flag '{flag}'."

  if positional.length == 0 then -- read from stdin
    return { filename := none, passes := pipeline, allowUnregisteredDialect }

  let [filename] := positional
    | .error "Expected exactly one positional argument for the input filename."

  if filename == "-" then
    return { filename := none, passes := pipeline, allowUnregisteredDialect }

  return { filename := some filename, passes := pipeline, allowUnregisteredDialect }

def getFileContent (filename : Option String) : ExceptT String IO ByteArray := do
  if let some f := filename then
    try
      return ← IO.FS.readBinFile f
    catch e =>
      throw s!"Error reading file '{filename}': {e}"

  return ← IO.FS.Stream.readBinToEnd (←IO.getStdin)

def parseOperation (filename : Option String) (allowUnregisteredDialect : Bool := false) :
    ExceptT String IO (WfIRContext OpCode × OperationPtr) := do
  let fileContent ← getFileContent filename
  let some (ctx, _) := WfIRContext.create OpCode
    | throw "Failed to create IR context"

  let filename := if let some f := filename then f else "<stdin>"

  match ParserState.fromInput fileContent with
  | .ok parser =>
    let state := MlirParserState.fromContext ctx allowUnregisteredDialect
    match parseTopLevelOp.run state parser with
    | .ok (op, state, _) =>
      return (state.ctx, op)
    | .error err =>
      throw (err.format filename fileContent)
  | .error err =>
    throw (err.format filename fileContent)

set_option warn.sorry false in
def main (args : List String) : IO Unit := do
  enableExitOnPanic
  match parseArgs args with
  | .error errMsg =>
    IO.eprintln s!"Error: {errMsg}"
    IO.eprintln "Usage: veir-opt <filename> [-p=\"pass1,pass2,...\" | -pgrp=<group>] [--allow-unregistered-dialect]"
    IO.eprintln "Pass groups (-pgrp):"
    IO.eprintln passGroupsUsage
    IO.Process.exit 1
  | .ok { filename, passes, allowUnregisteredDialect } =>
    match ← parseOperation filename allowUnregisteredDialect with
    | .error errMsg =>
      IO.eprintln errMsg
      IO.Process.exit 1
    | .ok (ctx, op) =>
      match ctx.verify with
      | .error errMsg =>
        IO.eprintln s!"Error verifying input program: {errMsg}"
        IO.Process.exit 1
      | .ok _ =>
        match ← passes.run ⟨ctx, by sorry⟩ op with
        | .error errMsg =>
          IO.eprintln s!"Error: {errMsg}"
          IO.Process.exit 1
        | .ok finalCtx =>
          Veir.Printer.printOperation finalCtx op
