import Veir.Parser.MlirParser
import Veir.GlobalOpInfo
import Veir.Printer
import Veir.Panic
import Veir.Input

import Veir.Passes.PrintIR
import Veir.Passes.PrintDataFlow
import Veir.Passes.InstCombine
import Veir.Passes.ApplyPatterns
import Veir.Passes.CSE
import Veir.Passes.InstructionSelection.RISCV64
import Veir.Passes.InstructionSelection.RISCV64Sdag
import Veir.Passes.InstructionSelection.RISCV64Branches
import Veir.Passes.InstructionSelection.RISCV64Abi
import Veir.Passes.DCE.dce
import Veir.Passes.CastsReconciliation.Reconciliation
import Veir.Passes.FunctionBoundaryCoercion.Coercion
import Veir.Passes.RISCVCombines.Combine
import Veir.Passes.RegisterAllocation.RegisterAllocation
import Veir.Passes.ModArithToArith
import Veir.Passes.ArithToLLVM
import Veir.Passes.Canonicalize
import Veir.Passes.Legalization
import Veir.Passes.Legalization.RISCV64LegalizerInfo
import Veir.Passes.Legalization.RISCV64PostLegalizerCombiner
import Veir.Passes.CirToStd
import Veir.Passes.LLVMToGMIR

open Veir.Parser
open Veir.Parser.ParserError
open Veir.Input
open Veir

/--
  A map of all available compilation passes, keyed by their unique names.
-/
def availablePasses : Std.HashMap String (Pass OpCode) :=
  ([ PrintIRPass,
     PrintDataFlowPass,
     InstCombinePass,
     ApplyPatternsPass,
     CSEPass,
     IselRISCV64,
     IselSDAG,
     IselBrRISCV64,
     IselAbiRISCV64,
     DCEPass,
     CastReconcilePass,
     CoerceModArithFunctionBoundariesPass,
     CoerceCirFunctionBoundariesPass,
     RISCV.Combine,
     RegisterAllocationPass,
     ModArithToArithPass,
     ArithToLLVMPass,
     CanonicalizePass,
     LegalizePass,
     LegalizeRISCV64Pass,
     PostLegalizerCombinerRISCV64Pass,
     CirToStdPass,
     LLVMToGMIRPass ] : List (Pass OpCode)).foldl
    (fun m pass => m.insert pass.name pass)
    (Std.HashMap.emptyWithCapacity 16)

/--
  A map of named pass groups, each expanding to a comma-separated pipeline of pass names.
  A group name may be used wherever a pass name is expected in a `-p` list and expands
  in place to its member passes. If a name is both a pass and a group, the pass wins.
-/
def passGroups : Std.HashMap String String :=
  (Std.HashMap.emptyWithCapacity 2)
    |>.insert "O" "canonicalize,instcombine,cse,dce"
    |>.insert "mod-arith"
        "mod-arith-to-arith{barrett},cse,coerce-mod-arith-function-boundaries,reconcile-cast,canonicalize,cse,dce"
    |>.insert "mod-arith-pow2-width"
        "mod-arith-to-arith{barrett pow2-width},cse,coerce-mod-arith-function-boundaries{pow2-width},reconcile-cast,canonicalize,cse,dce"
    |>.insert "riscv"
        "isel-sdag-riscv64,llvm-to-gmir,legalize-riscv64,postlegalizer-combiner-riscv64,isel-br-riscv64,isel-riscv64,isel-abi-riscv64,reconcile-cast,riscv-combine,dce"
    |>.insert "cir"
        "cir-to-std,cse,coerce-cir-function-boundaries,reconcile-cast,canonicalize,cse,dce"

/--
  A human-readable description of every pass group and the passes it expands to,
  used in the usage message.
-/
def passGroupsUsage : String :=
  String.intercalate "\n"
    ((passGroups.toList.toArray.qsort (·.1 < ·.1)).toList.map fun (name, passes) =>
      s!"    {name}: {passes}")

/--
  A human-readable description of the options taken by those passes that have any,
  used in the usage message. Passes without options are omitted.
-/
def passOptionsUsage : String :=
  let withOptions := (availablePasses.values.toArray.qsort (·.name < ·.name)).toList.filter
    (!·.options.isEmpty)
  String.intercalate "\n" (withOptions.flatMap fun pass =>
    s!"    {pass.name}:" ::
      (pass.options.toList.toArray.qsort (·.1 < ·.1)).toList.map fun (name, option) =>
        let defaultValue := if option.defaultValue then "true" else "false"
        s!"      {name} (default: {defaultValue}): {option.description}")

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
  /-- Whether to print operations in generic form. -/
  printGenericOpForm : Bool
  /-- The marker to split the input at, if any. -/
  splitInputFile : Option String

/--
  Replace every pass-group name in a pipeline string by the passes it stands for, leaving
  everything else alone. Names that are neither a pass nor a group are left in place so
  that `PassPipeline.ofString?` reports them. Groups do not take options.
-/
def expandPassGroups (pipeline : String) : Except String String := do
  let elements ← (pipeline.splitOn ",").mapM fun element => do
    let (name, options) ← splitPipelineElement element
    if availablePasses.contains name then return element
    match passGroups.get? name with
    | none => return element
    | some expansion =>
      unless options.isEmpty do
        throw s!"pass group '{name}' does not take options"
      return expansion
  return String.intercalate "," elements

/--
  Parse the `-p` flags to construct a pass pipeline.
  `-p` takes a comma-separated list of pass names and pass-group names; a group name
  (see `passGroups`) expands in place to its member passes. A pass name may be followed by
  a brace-enclosed, space-separated list of boolean options, as in
  `pass{opt1 opt2=false}`. Bare option names mean `true`; omitted options take their declared
  defaults. The flag may appear any number of times; the resulting pipeline
  is the concatenation of their passes, in the order the flags appear on the command line.
  Returns an error if a flag is malformed, if any name is neither a pass nor a group, or if
  a pass is given an option it does not accept.
-/
def parsePipelineOption (args : List String) :
    Except String (PassPipeline OpCode × List String) := do
  let (pipelineFlags, rest) := args.partition (·.startsWith "-p=")
  let mut passes : Array (Pass OpCode × PassOptions) := #[]
  for flag in pipelineFlags do
    let arg := (flag.drop 3).toString
    let expanded ← match expandPassGroups arg with
      | .ok expanded => pure expanded
      | .error errMsg => throw s!"Error parsing -p flag: {errMsg}"
    match PassPipeline.ofString? availablePasses expanded with
    | .ok pipeline => passes := passes ++ pipeline.passes
    | .error errMsg => throw s!"Error parsing -p flag: {errMsg}"
  return ({ passes }, rest)

/--
  The marker given by a `--split-input-file[=<marker>]` flag or `defaultSplitMarker` if it has none.
-/
def splitMarkerOfFlag? (flag : String) : Option String :=
  if flag == "--split-input-file" || flag == "--split-input-file=" then
    some defaultSplitMarker
  else
    (flag.dropPrefix? "--split-input-file=").map (·.toString)

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
  -- Consume `--print-op-generic` if present.
  let printGenericOpForm := flags.contains "--print-op-generic"
  let flags := flags.filter (· != "--print-op-generic")
  -- Consume `--split-input-file[=<marker>]` if present.
  let splitInputFile := flags.findSome? splitMarkerOfFlag?
  let flags := flags.filter fun flag => (splitMarkerOfFlag? flag).isNone
  -- If anything survived, it was unrecognized and we error out.
  if let some flag := flags.head? then
    .error s!"Unrecognized flag '{flag}'."

  match inputSourceOfArgs positional with
  | .ok filename =>
    return { filename, passes := pipeline, allowUnregisteredDialect, disableVerifiers,
             printGenericOpForm, splitInputFile }
  | .error errMsg => .error errMsg

set_option warn.sorry false in
/--
  Parse `input` starting at `start`, run the passes on it, and print the result.
-/
def processBuffer (args : VeirOptArgs) (sourceName : String) (input : ByteArray)
    (start : Parser.Location) : ExceptT String IO Unit := do
  let (ctx, op, _) ← liftExcept (parseSourceString input sourceName
    args.allowUnregisteredDialect (verifyAfterParse := !args.disableVerifiers) start)
  let ctx ← try args.passes.run ⟨ctx, by sorry⟩ op args.disableVerifiers
            catch errMsg => throw s!"Error: {errMsg}"
  Veir.Printer.printModule ctx.raw op { printGenericOpForm := args.printGenericOpForm }

/--
  Run `processBuffer` on each chunk of `content`, printing `defaultSplitMarker` between their
  outputs. A failing chunk has its error printed and does not stop the following ones.
  Returns whether all chunks succeeded.
-/
def processInput (args : VeirOptArgs) (sourceName : String) (content : ByteArray) : IO Bool := do
  let mut succeeded := true
  for ((start, stop), i) in (splitInput content args.splitInputFile).zipIdx do
    if i > 0 then IO.println defaultSplitMarker
    let chunk := processBuffer args sourceName (content.extract 0 stop) { byteOffset := start }
    if let .error err ← chunk.run then
      IO.eprintln err
      succeeded := false
  return succeeded

def main (args : List String) : IO Unit := do
  enableExitOnPanic
  match parseArgs args with
  | .error errMsg =>
    IO.eprintln s!"Error: {errMsg}"
    IO.eprintln "Usage: veir-opt <filename> [-p=\"pass1,pass2,...\"]... [--allow-unregistered-dialect] [--disable-verifiers] [--print-op-generic] [--split-input-file[=<marker>]]"
    IO.eprintln "  -p may be repeated; passes run in the order the flags appear."
    IO.eprintln "  A pass name may be followed by boolean options: pass{opt1 opt2=false}."
    IO.eprintln "  Bare option names mean true; omitted options take their declared defaults."
    IO.eprintln "  The passes taking options are:"
    IO.eprintln passOptionsUsage
    IO.eprintln "  A pass list may also contain pass-group names, which expand in place:"
    IO.eprintln passGroupsUsage
    IO.Process.exit 1
  | .ok args =>
    match ← getFileContent args.filename with
    | .error errMsg =>
      IO.eprintln errMsg
      IO.Process.exit 1
    | .ok content =>
      unless ← processInput args (args.filename.getD "<stdin>") content do
        IO.Process.exit 1
