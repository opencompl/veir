import Veir.Parser.MlirParser
import Veir.Printer
import Veir.IR.Basic
import Veir.Verifier
import Veir.Interpreter.Basic
import Veir.Panic

/-!
  # Veir Interpreter CLI Tool

  This file implements a simple command-line tool that reads an MLIR
  file, finds a zero-argument func.func or llvm.func named `main`, and
  then executes that function using the interpreter defined in
  `Veir.Interpreter`.
 -/

open Veir.Parser
open Veir

def parseOperation (filename : String) : ExceptT String IO (WfIRContext OpCode × OperationPtr) := do
  let fileContent ← IO.FS.readBinFile filename
  let some (ctx, _) := WfIRContext.create OpCode
    | throw "Failed to create IR context"
  match ParserState.fromInput fileContent with
  | .ok parser =>
    let parserState := MlirParserState.fromContext ctx (allowUnregisteredDialect := true)
    match (parseOp none).run parserState parser with
    | .ok (op, state, _) =>
      return (state.ctx, op)
    | .error errMsg =>
      throw s!"Error parsing operation: {errMsg}"
  | .error errMsg =>
    throw s!"Error reading file: {errMsg}"

/-- Returns true if `op` is a viable zero-argument `@main` function. -/
private def isZeroArgMainFunc (ctx : IRContext OpCode) (op : OperationPtr) : Bool :=
  let opType := op.getOpType! ctx
  let check : (opCode : OpCode) → propertiesOf opCode → Bool
    | .llvm .func, props =>
      if let some symName := props.sym_name then
        String.fromUTF8! symName.value == "main" &&
        match props.function_type with
        | some ft =>
          match ft.val with
          | .llvmFunctionType funcType => funcType.inputs.isEmpty
          | _ => false
        | none => false
      else false
    | .func .func, props =>
      if let some symName := props.sym_name then
        String.fromUTF8! symName.value == "main" &&
        let region := op.getRegion! ctx 0
        match (region.get! ctx).firstBlock with
        | some block => block.getNumArguments! ctx == 0
        | none => false
      else false
    | _, _ => false
  check opType (op.getProperties! ctx opType)

/-- Scan the module's top-level ops for entry points. -/
partial def scanEntryPoints (ctx : IRContext OpCode) (op : Option OperationPtr)
    (entryPoints : List OperationPtr := []) : IO (List OperationPtr) := do
  match op with
  | none => return entryPoints
  | some op =>
    let opType := op.getOpType! ctx
    match opType with
    | .llvm .func | .func .func =>
      let entryPoints := if isZeroArgMainFunc ctx op then op :: entryPoints else entryPoints
      scanEntryPoints ctx (op.get! ctx).next entryPoints
    | .llvm .module_flags =>
      scanEntryPoints ctx (op.get! ctx).next entryPoints
    | _ =>
      IO.eprintln "Error: Top-level operations are disallowed; define a zero-argument function named 'main'"
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
  match args with
  | [filename] =>
    match ← parseOperation filename with
    | .ok (ctx, op) =>
      match WfIRContext.verify ctx (some op) with
      | .ok _ =>
        let rawCtx : IRContext OpCode := ctx
        let mainOp ← resolveEntryPoint rawCtx op
        let result := bind (interpretFunction (ctx := ctx) mainOp #[] MemoryState.empty (by sorry))
                           (fun (_, r) => pure r)
        match result with
        | some (.ok results) => IO.println s!"Program output: {results}"
        | some .ub => IO.println "Undefined behavior"
        | none =>
          IO.eprintln "Error while interpreting module"
          IO.Process.exit 1
      | .error errMsg =>
        IO.eprintln s!"Error verifying input program: {errMsg}"
        IO.Process.exit 1
    | .error errMsg =>
      IO.eprintln s!"Error: {errMsg}"
      IO.Process.exit 1
  | _ =>
    IO.eprintln "Wrong number of arguments."
    IO.eprintln "Usage: veir-interpret <filename>"
    IO.Process.exit 2
