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
import Veir.Passes.ArithToLLVM
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
    |>.insert ArithToLLVMPass.name ArithToLLVMPass
    |>.insert CanonicalizePass.name CanonicalizePass

/--
  A map of named pass groups, each expanding to a comma-separated pipeline of pass names.
  A group name may be used wherever a pass name is expected in a `-p` list and expands
  in place to its member passes. If a name is both a pass and a group, the pass wins.
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
  /-- Whether to disable IR verification -/
  disableVerifiers : Bool

/--
  Parse the `-p` flags to construct a pass pipeline.
  `-p` takes a comma-separated list of pass names and pass-group names; a group name
  (see `passGroups`) expands in place to its member passes. The flag may appear any
  number of times; the resulting pipeline is the concatenation of their passes, in the
  order the flags appear on the command line.
  Returns an error if a flag is malformed or if any name is neither a pass nor a group.
-/
def parsePipelineOption (args : List String) :
    Except String (PassPipeline OpCode × List String) := do
  let (pipelineFlags, rest) := args.partition (·.startsWith "-p=")
  let mut passes : Array (Pass OpCode) := #[]
  for flag in pipelineFlags do
    let arg := (flag.drop 3).toString
    let expanded := String.intercalate "," (arg.splitOn "," |>.map fun name =>
      if availablePasses.contains name then name
      else (passGroups.get? name).getD name)
    match PassPipeline.ofString? availablePasses expanded with
    | .ok pipeline => passes := passes ++ pipeline.passes
    | .error errMsg => throw s!"Error parsing -p flag: {errMsg}"
  return ({ passes }, rest)

/--
  Parse CLI arguments. Returns an error if the arguments are malformed.
-/
def parseArgs (args : List String) : Except String VeirOptArgs := do
  let (flags, positional) := args.partition (·.startsWith "-")
  -- Consume any `-p` flags.
  let (pipeline, flags) ← parsePipelineOption flags
  -- Consume `--allow-unregistered-dialect` if present.
  let allowUnregisteredDialect := flags.contains "--allow-unregistered-dialect"
  let flags := flags.filter (· != "--allow-unregistered-dialect")
  -- Consume `--disable-verifiers` if present.
  let disableVerifiers := flags.contains "--disable-verifiers"
  let flags := flags.filter (· != "--disable-verifiers")
  -- If anything survived, it was unrecognized and we error out.
  if let some flag := flags.head? then
    .error s!"Unrecognized flag '{flag}'."

  if positional.length == 0 then -- read from stdin
    return { filename := none, passes := pipeline, allowUnregisteredDialect, disableVerifiers }

  let [filename] := positional
    | .error "Expected exactly one positional argument for the input filename."

  if filename == "-" then
    return { filename := none, passes := pipeline, allowUnregisteredDialect, disableVerifiers }

  return { filename := some filename, passes := pipeline, allowUnregisteredDialect, disableVerifiers }

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
    IO.eprintln "Usage: veir-opt <filename> [-p=\"pass1,pass2,...\"]... [--allow-unregistered-dialect] [--disable-verifiers]"
    IO.eprintln "  -p may be repeated; passes run in the order the flags appear."
    IO.eprintln "  A pass list may also contain pass-group names, which expand in place:"
    IO.eprintln passGroupsUsage
    IO.Process.exit 1
  | .ok { filename, passes, allowUnregisteredDialect, disableVerifiers } =>
    match ← parseOperation filename allowUnregisteredDialect with
    | .error errMsg =>
      IO.eprintln errMsg
      IO.Process.exit 1
    | .ok (ctx, op) =>
      if !disableVerifiers then
        if let .error errMsg := ctx.verify then
          IO.eprintln s!"Error verifying input program: {errMsg}"
          IO.Process.exit 1
      match ← passes.run ⟨ctx, by sorry⟩ op disableVerifiers with
      | .error errMsg =>
        IO.eprintln s!"Error: {errMsg}"
        IO.Process.exit 1
      | .ok finalCtx =>
        Veir.Printer.printOperation finalCtx op
