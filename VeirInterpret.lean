import Veir.Parser.MlirParser
import Veir.Verifier
import Veir.Interpreter.Basic
import Veir.Input
import Veir.Panic

/-!
  # Veir Interpreter CLI Tool

  This file implements a simple command-line tool that reads an MLIR program
  from a file or from standard input, finds a func.func or llvm.func named
  `main`, and executes that function using the interpreter defined in
  `Veir.Interpreter`.

  By default `main` must take no arguments. With `--memory-size N`, `main`
  instead takes one `!llvm.ptr` or `!riscv.reg` argument, backed by N bytes of
  freshly allocated poison memory.
 -/

open Veir.Parser
open Veir.Input
open Veir

/-- Returns true if `op` is a viable `@main` with `numArgs` arguments. -/
private def isMainFunc (ctx : IRContext OpCode) (op : OperationPtr) (numArgs : Nat) : Bool :=
  match FunctionOpInterface.getSymName? op ctx with
  | some symName =>
      String.fromUTF8! symName.value == "main" &&
        (FunctionOpInterface.getNumArguments? op ctx == some numArgs)
  | none =>
      false

/-- Scan the module's top-level ops for entry points. -/
partial def scanEntryPoints (ctx : IRContext OpCode) (op : Option OperationPtr)
    (numArgs : Nat) (entryPoints : List OperationPtr := []) : IO (List OperationPtr) := do
  match op with
  | none => return entryPoints
  | some op =>
    if op.isFunctionLike ctx then
      let entryPoints := if isMainFunc ctx op numArgs then op :: entryPoints else entryPoints
      scanEntryPoints ctx (op.get! ctx).next numArgs entryPoints
    else
      match op.getOpType! ctx with
      | .llvm .module_flags | .llvm .mlir__global =>
        scanEntryPoints ctx (op.get! ctx).next numArgs entryPoints
      | _ =>
        IO.eprintln "Error: unsupported top-level operation; expected a function, llvm.mlir.global, or llvm.module_flags"
        IO.Process.exit 1

/-- Resolve the unique entry point of the module, if one exists. -/
def resolveEntryPoint (ctx : IRContext OpCode) (moduleOp : OperationPtr)
    (numArgs : Nat := 0) : IO OperationPtr := do
  let region := moduleOp.getRegion! ctx 0
  let entryPoints ←
    match (region.get! ctx).firstBlock with
    | none => pure []
    | some blockPtr => scanEntryPoints ctx (blockPtr.get! ctx).firstOp numArgs
  match entryPoints with
  | [] =>
    if numArgs == 0 then
      IO.eprintln "Error: No entry point: define a zero-argument function named 'main'"
    else
      IO.eprintln s!"Error: No entry point: define a function named 'main' with {numArgs} argument(s)"
    IO.Process.exit 1
  | [mainOp] => return mainOp
  | _ =>
    if numArgs == 0 then
      IO.eprintln "Error: Multiple entry points: define exactly one zero-argument function named 'main'"
    else
      IO.eprintln s!"Error: Multiple entry points: define exactly one function named 'main' with {numArgs} argument(s)"
    IO.Process.exit 1

set_option warn.sorry false in
def runInterpreter (filename : Option String) (memorySize : Option Nat) : IO Unit := do
  match ← parseOperation filename (allowUnregisteredDialect := true) with
  | .ok (ctx, op) =>
    match ctx.verify op with
    | .ok _ =>
      let rawCtx : IRContext OpCode := ctx
      let numArgs := if memorySize.isSome then 1 else 0
      let mainOp ← resolveEntryPoint rawCtx op numArgs
      let (memory, arguments) ←
        match memorySize with
        | none => pure (MemoryState.empty, #[])
        | some size =>
          let some argType := (FunctionOpInterface.getArgumentTypes? mainOp rawCtx).bind (·[0]?)
            | IO.eprintln "Error: Could not determine the memory argument type"
              IO.Process.exit 1
          let (memory, addr) := MemoryState.empty.alloc size.toUInt64
          let argument ←
            match argType with
            | .llvmPointerType _ => pure (.addr addr)
            | .registerType _ => pure (.reg ⟨BitVec.ofNat 64 addr.toNat⟩)
            | _ =>
              IO.eprintln "Error: --memory-size requires a !llvm.ptr or !riscv.reg argument"
              IO.Process.exit 1
          pure (memory, #[argument])
      let result := bind (interpretFunction (ctx := ctx) mainOp arguments memory (by sorry))
                         (fun (_, r) => pure r)
      match result with
      | .ok results => IO.println s!"Program output: {results}"
      | .ub => IO.println "Undefined behavior"
      | .fail =>
        IO.eprintln "Error while interpreting module"
        IO.Process.exit 1
    | .error errMsg =>
      IO.eprintln s!"Error verifying input program: {errMsg}"
      IO.Process.exit 1
  | .error errMsg =>
    IO.eprintln s!"Error: {errMsg}"
    IO.Process.exit 1

/-- Consume a leading `--memory-size N` flag, returning it and the remaining
    arguments. -/
def parseMemorySizeOption (args : List String) : Except String (Option Nat × List String) :=
  match args with
  | "--memory-size" :: sizeString :: rest =>
    match sizeString.toNat? with
    | some size => .ok (some size, rest)
    | none => .error "--memory-size expects a nonnegative integer"
  | _ => .ok (none, args)

/-- Report a command-line usage error and exit. -/
private def usageError (errMsg : String) : IO α := do
  IO.eprintln errMsg
  IO.eprintln "Usage: veir-interpret [--memory-size N] [filename]"
  IO.eprintln "  Reads the program from standard input if no filename is given."
  IO.Process.exit 2

def main (args : List String) : IO Unit := do
  enableExitOnPanic
  let (memorySize, positional) ←
    match parseMemorySizeOption args with
    | .ok result => pure result
    | .error errMsg => usageError errMsg
  let filename ←
    match inputSourceOfArgs positional with
    | .ok filename => pure filename
    | .error errMsg => usageError errMsg
  runInterpreter filename memorySize
