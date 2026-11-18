import Veir.Parser.LLVMLowering
import Veir.Input
import Veir.Printer
import Veir.IR.RootedIso

/-!
# Differential testing of the verified LLVM IR parser

Compares two ways of bringing textual LLVM IR into VeIR:

* reference: `mlir-translate --import-llvm` → `mlir-opt --mlir-print-op-generic`
  → VeIR's MLIR parser;
* new: `LLVMParserProp.parse` → `NameResolutionSketch.resolveModule`
  → `LLVMLowering.lowerModule`.

The two IR graphs are compared with `rootedIso?`, the executable form of `RootedIso`: equality
up to a renaming of operations and blocks. Both are also printed in generic form for
inspection. As an auxiliary signal, mismatching graphs are also decoded with
`LLVMLowering.reverseModule`, which forgets SSA names, constant placement and sharing,
and attributes the new path does not produce.

Usage: `lake env lean --run Tools/llvm-parser-difftest/DiffTest.lean <examples-dir> <out-dir>`
-/

open Veir LLVMParserProp NameResolutionSketch LLVMLowering

/-- Run `cmd args`, feeding `stdin`, and return its stdout or a message containing stderr.
`lake env` points `LD_LIBRARY_PATH` at Lean's LLVM, which breaks the MLIR tools, so it is unset. -/
def runProc (cmd : String) (args : Array String) (stdin : String := "") : IO (Except String String) := do
  let env : Array (String × Option String) := #[("LD_LIBRARY_PATH", none)]
  let child ← IO.Process.spawn { cmd, args, env, stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdinHandle, child) ← child.takeStdin
  stdinHandle.putStr stdin
  stdinHandle.flush
  let stdoutTask ← IO.asTask child.stdout.readToEnd .dedicated
  let stderr ← child.stderr.readToEnd
  let stdout ← IO.ofExcept stdoutTask.get
  let code ← child.wait
  return if code == 0 then .ok stdout else .error s!"{cmd} exited with {code}:\n{stderr}"

/-- Capture what `printModule` writes to stdout. -/
def printToString (ctx : WfIRContext OpCode) (root : OperationPtr) : IO String := do
  let buf ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  IO.withStdout (IO.FS.Stream.ofBuffer buf) <|
    Printer.printModule ctx.raw root { printGenericOpForm := true }
  return String.fromUTF8! (← buf.get).data

/-- Reference path: LLVM text → MLIR text (via the MLIR tools) → VeIR. -/
def referencePath (file : System.FilePath) : IO (Except String (WfIRContext OpCode × OperationPtr × String)) := do
  let mlir ← match ← runProc "mlir-translate" #["--import-llvm", file.toString] with
    | .ok s => pure s | .error e => return .error e
  let generic ← match ← runProc "mlir-opt" #["--mlir-print-op-generic", "--mlir-print-local-scope"] mlir with
    | .ok s => pure s | .error e => return .error e
  match Input.parseSourceString generic.toUTF8 file.toString with
  | .ok (ctx, root, _) => return .ok (ctx, root, generic)
  | .error e => return .error s!"VeIR MLIR parser: {e}"

/-- New path: LLVM text → VeIR, through this branch's parser, resolver and lowering. -/
def newPath (src : String) : Except String (WfIRContext OpCode × OperationPtr) := do
  let m ← (parse src).mapError (s!"parse: {reprStr ·}")
  let some r := resolveModule m | throw "resolveModule failed"
  (lowerModule r).mapError (s!"lowerModule: {·}")

inductive Outcome where
  | iso
  | mismatch (normalisedEqual : Bool)
  | referenceError (msg : String)
  | newError (msg : String)
  | bothError (ref new : String)

def Outcome.label : Outcome → String
  | .iso => "ISOMORPHIC"
  | .mismatch true => "MISMATCH (equal after reverseModule)"
  | .mismatch false => "MISMATCH (differs after reverseModule)"
  | .referenceError _ => "REFERENCE-ERROR"
  | .newError _ => "NEW-ERROR"
  | .bothError .. => "BOTH-ERROR"

/-- Compare the two paths on one file, writing both printed graphs to `outDir`. -/
def compareFile (file outDir : System.FilePath) : IO Outcome := do
  let stem := file.fileStem.getD "out"
  let src ← IO.FS.readFile file
  let ref ← referencePath file
  let new := newPath src
  match ref, new with
  | .error r, .error n => return .bothError r n
  | .error r, .ok _ => return .referenceError r
  | .ok _, .error n => return .newError n
  | .ok (rctx, rroot, generic), .ok (nctx, nroot) =>
    let refText ← printToString rctx rroot
    let newText ← printToString nctx nroot
    IO.FS.writeFile (outDir / s!"{stem}.mlir-translate.mlir") generic
    IO.FS.writeFile (outDir / s!"{stem}.reference.mlir") refText
    IO.FS.writeFile (outDir / s!"{stem}.new.mlir") newText
    if rootedIso? rctx rroot nctx nroot then return .iso
    let normalisedEqual := match reverseModule rctx rroot, reverseModule nctx nroot with
      | .ok a, .ok b => decide (a = b)
      | _, _ => false
    return .mismatch normalisedEqual

def main (args : List String) : IO UInt32 := do
  let [examples, out] := args | IO.eprintln "usage: DiffTest <examples-dir> <out-dir>"; return 2
  IO.FS.createDirAll out
  let files := ((← System.FilePath.readDir examples).map (·.path)).filter (·.extension == some "ll")
  let files := files.qsort (·.toString < ·.toString)
  let mut equal := 0
  for file in files do
    let outcome ← compareFile file out
    if let .iso := outcome then equal := equal + 1
    IO.println s!"{file.fileName.getD ""}: {outcome.label}"
    match outcome with
    | .referenceError m | .newError m => IO.println s!"    {(m.trimAsciiEnd.toString.replace "\n" "\n    ")}"
    | .bothError r n => IO.println s!"    reference: {r}\n    new: {n}"
    | _ => pure ()
  IO.println s!"\n{equal}/{files.size} isomorphic"
  return 0
