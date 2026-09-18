import Veir.Parser.MlirParser
import Veir.Verifier
import Veir.Interpreter.Basic
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

set_option warn.sorry false in
def main (args : List String) : IO Unit := do
  enableExitOnPanic
  let filename ←
    match inputSourceOfArgs args with
    | .ok filename => pure filename
    | .error errMsg =>
      IO.eprintln errMsg
      IO.eprintln "Usage: veir-interpret [filename]"
      IO.eprintln "  Reads the program from standard input if no filename is given."
      IO.Process.exit 2
  match ← parseOperation filename (allowUnregisteredDialect := true) with
  | .ok (ctx, op) =>
    match ctx.verify op with
    | .ok _ =>
      let rawCtx : IRContext OpCode := ctx
      let mainOp ← resolveEntryPoint rawCtx op
      let result := bind (interpretFunction (ctx := ctx) mainOp #[] MemoryState.empty (by sorry))
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
