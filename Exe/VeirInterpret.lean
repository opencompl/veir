import Veir.Parser.MlirParser
import Veir.Verifier
import Veir.Interpreter.CTree.Run
import Veir.Input
import Veir.Panic

/-!
  # Veir Interpreter CLI Tool

  This file implements a simple command-line tool that reads an MLIR
  program from a file or from standard input, finds a zero-argument
  func.func or llvm.func named `main`, and then executes that function
  using the interpreter defined in `Veir.Interpreter`.
 -/

open Veir.Parser
open Veir.Input
open Veir

/-- Returns true if `op` is a viable zero-argument `@main` function. -/
private def isZeroArgMainFunc (ctx : IRContext OpCode) (op : OperationPtr) : Bool :=
  match FunctionOpInterface.getSymName? op ctx with
  | some symName =>
      String.fromUTF8! symName.value == "main" &&
        (FunctionOpInterface.getNumArguments? op ctx == some 0)
  | none =>
      false

/-- Scan the module's top-level ops for entry points. -/
partial def scanEntryPoints (ctx : IRContext OpCode) (op : Option OperationPtr)
    (entryPoints : List OperationPtr := []) : IO (List OperationPtr) := do
  match op with
  | none => return entryPoints
  | some op =>
    if op.isFunctionLike ctx then
      let entryPoints := if isZeroArgMainFunc ctx op then op :: entryPoints else entryPoints
      scanEntryPoints ctx (op.get! ctx).next entryPoints
    else
      match op.getOpType! ctx with
      | .llvm .module_flags | .llvm .mlir__global =>
        scanEntryPoints ctx (op.get! ctx).next entryPoints
      | _ =>
        IO.eprintln "Error: unsupported top-level operation; expected a function, llvm.mlir.global, or llvm.module_flags"
        IO.Process.exit 1

/-- Resolve the unique entry point of the module, if one exists. -/
def resolveEntryPoint (ctx : IRContext OpCode) (moduleOp : OperationPtr) : IO OperationPtr := do
  let region := moduleOp.getRegion! ctx 0
  let entryPoints ←
    match (region.get! ctx).firstBlock with
    | none => pure []
    | some blockPtr => scanEntryPoints ctx (blockPtr.get! ctx).firstOp
  match entryPoints with
  | [] =>
    IO.eprintln "Error: No entry point: define a zero-argument function named 'main'"
    IO.Process.exit 1
  | [mainOp] => return mainOp
  | _ =>
    IO.eprintln "Error: Multiple entry points: define exactly one zero-argument function named 'main'"
    IO.Process.exit 1

private structure Options where
  ctree : Bool := false
  fuel : Nat := 1000000
  benchmark : Option Nat := none
  warmups : Nat := 10
  inputs : List String := []

private def parseOptions (args : List String) : Except String Options := do
  let mut opts : Options := {}
  for arg in args do
    if arg == "--ctree" then
      opts := { opts with ctree := true }
    else if arg.startsWith "--fuel=" then
      let some n := (arg.drop 7).toString.toNat? | throw "invalid --fuel"
      opts := { opts with fuel := n }
    else if arg.startsWith "--warmups=" then
      let some n := (arg.drop 10).toString.toNat? | throw "invalid --warmups"
      opts := { opts with warmups := n }
    else if arg.startsWith "--benchmark=" then
      let some n := (arg.drop 12).toString.toNat? | throw "invalid --benchmark"
      if n == 0 then throw "--benchmark must be positive"
      opts := { opts with benchmark := some n }
    else
      opts := { opts with inputs := opts.inputs ++ [arg] }
  return opts

/-- Keep evaluation inside each IO invocation: every repetition starts a fresh
interpreter, including tree construction and variable/memory initialization. -/
@[noinline]
private def execute (ctree : Bool) (fuel : Nat) (ctx : WfIRContext OpCode)
    (op : OperationPtr) (h : op.InBounds ctx.raw) : IO (Interp (Array RuntimeValue)) := do
  if ctree then
    match CTreeInterpreter.run fuel (CTreeInterpreter.interpretFunction op #[] h) with
    | .error message => throw (IO.userError message)
    | .ok result => return result.map Prod.snd
  else
    return (interpretFunction op #[] MemoryState.empty h).map Prod.snd

private def successful (result : Interp (Array RuntimeValue)) : IO (Array RuntimeValue) :=
  match result with
  | .ok values => pure values
  | .ub => throw (IO.userError "benchmark triggered undefined behavior")
  | .fail => throw (IO.userError "benchmark interpretation failed")

private def timeBatch (ctree : Bool) (fuel repeats : Nat) (ctx : WfIRContext OpCode)
    (op : OperationPtr) (h : op.InBounds ctx.raw) (expected : String) : IO Float := do
  let start ← IO.monoNanosNow
  let mut last := #[]
  for _ in [:repeats] do
    last ← successful (← execute ctree fuel ctx op h)
  let finish ← IO.monoNanosNow
  if toString last != expected then throw (IO.userError "interpreter results disagree")
  return (finish - start).toFloat / repeats.toFloat / 1000.0

private def median (xs : Array Float) : Float :=
  let sorted := xs.qsort (· < ·)
  sorted[sorted.size / 2]!

/-- Seven paired batches, alternating order, after warmup. Parsing, verification,
output formatting and equality checking are outside the timed interval. -/
private def benchmark (fuel repeats warmups : Nat) (ctx : WfIRContext OpCode)
    (op : OperationPtr) (h : op.InBounds ctx.raw) : IO Unit := do
  IO.eprintln s!"Parsing and verification complete; running {warmups} warmups per backend."
  let expected := toString (← successful (← execute false fuel ctx op h))
  for _ in [:warmups] do
    for backend in [false, true] do
      let result ← successful (← execute backend fuel ctx op h)
      if toString result != expected then throw (IO.userError "interpreter results disagree")
  let mut normalTimes := #[]
  let mut ctreeTimes := #[]
  for i in [:7] do
    let order := if i % 2 == 0 then [false, true] else [true, false]
    for backend in order do
      let us ← timeBatch backend fuel repeats ctx op h expected
      IO.eprintln s!"Batch {i + 1}/7, {if backend then "CTree" else "normal"}: {us} us/run"
      if backend then ctreeTimes := ctreeTimes.push us
      else normalTimes := normalTimes.push us
  let normal := median normalTimes
  let ctree := median ctreeTimes
  IO.println s!"Program output: {expected}"
  IO.println s!"Execution only; 7 batches x {repeats} runs, {warmups} warmups per backend"
  IO.println s!"normal us/run: {normalTimes}"
  IO.println s!"ctree us/run: {ctreeTimes}"
  IO.println s!"Median normal: {normal} us/run"
  IO.println s!"Median CTree: {ctree} us/run"
  IO.println s!"CTree / normal: {ctree / normal}x"

def main (args : List String) : IO Unit := do
  enableExitOnPanic
  let opts ← match parseOptions args with
    | .ok opts => pure opts
    | .error message =>
      IO.eprintln message
      IO.Process.exit 2
  let filename ←
    match inputSourceOfArgs opts.inputs with
    | .ok filename => pure filename
    | .error errMsg =>
      IO.eprintln errMsg
      IO.eprintln "Usage: veir-interpret [--ctree] [--fuel=N] [--benchmark=N] [--warmups=N] [filename]"
      IO.eprintln "  --benchmark=N compares both interpreters, N runs per batch."
      IO.eprintln "  --warmups=N sets benchmark warmups per backend (default 10)."
      IO.eprintln "  Reads standard input if no filename is given."
      IO.Process.exit 2
  match ← parseOperation filename (allowUnregisteredDialect := true) with
  | .ok (ctx, op) =>
    match ctx.verify op with
    | .ok _ =>
      let mainOp ← resolveEntryPoint ctx.raw op
      if h : mainOp.InBounds ctx.raw then
        if let some repeats := opts.benchmark then
          benchmark opts.fuel repeats opts.warmups ctx mainOp h
        else
          match ← execute opts.ctree opts.fuel ctx mainOp h with
          | .ok results => IO.println s!"Program output: {results}"
          | .ub => IO.println "Undefined behavior"
          | .fail =>
            IO.eprintln "Error while interpreting module"
            IO.Process.exit 1
      else
        IO.eprintln "Error: entry point is out of bounds"
        IO.Process.exit 1
    | .error errMsg =>
      IO.eprintln s!"Error verifying input program: {errMsg}"
      IO.Process.exit 1
  | .error errMsg =>
    IO.eprintln s!"Error: {errMsg}"
    IO.Process.exit 1
