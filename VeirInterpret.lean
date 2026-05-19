import Veir.Parser.MlirParser
import Veir.Printer
import Veir.IR.Basic
import Veir.Verifier
import Veir.Interpreter.Basic

/-!
  # Veir Interpreter CLI Tool

  This file implements a simple command-line tool that reads an MLIR file,
  and then executes the block of the builtin.module operation in it using
  the interpreter defined in `Veir.Interpreter`.
-/

open Veir.Parser
open Veir

def parseOperation (filename : String) : ExceptT String IO (WfIRContext OpCode × OperationPtr) := do
  let fileContent ← IO.FS.readBinFile filename
  let some (ctx, _) := WfIRContext.create OpCode
    | throw "Failed to create IR context"
  match ParserState.fromInput fileContent with
  | .ok parser =>
    match (parseOp none).run (MlirParserState.fromContext ctx) parser with
    | .ok (op, state, _) =>
      return (state.ctx, op)
    | .error errMsg =>
      throw s!"Error parsing operation: {errMsg}"
  | .error errMsg =>
    throw s!"Error reading file: {errMsg}"

/-- Returns true if `op` is an `llvm.func` with the given `name`. -/
def isFuncWithName (ctx : IRContext OpCode) (op : OperationPtr) (name : String) : Bool :=
  let opType := op.getOpType! ctx
  let check : (opCode : OpCode) → propertiesOf opCode → Bool
    | .llvm .func, props =>
      match props.sym_name with
      | none => false
      | some sym_name => String.fromUTF8! sym_name.value == name
    | _, _ => false
  check opType (op.getProperties! ctx opType)

/-- Returns true if the `llvm.func` properties describe a function with no arguments. -/
private def hasNoArgs (props : LLVMFuncProperties) : Bool :=
  match props.function_type with
  | none => false
  | some ft =>
    match ft.val with
    | .llvmFunctionType funcType => funcType.inputs.isEmpty
    | _ => false

/-- Returns true if `op` is an `llvm.func @main` with no arguments. -/
private def isZeroArgMainFunc (ctx : IRContext OpCode) (op : OperationPtr) : Bool :=
  let opType := op.getOpType! ctx
  let check : (opCode : OpCode) → propertiesOf opCode → Bool
    | .llvm .func, props => isFuncWithName ctx op "main" && hasNoArgs props
    | _, _ => false
  check opType (op.getProperties! ctx opType)

/--
  Returns true if a top-level op counts as module-level executable code for the CLI.
  Under the current execution model, any non-`llvm.func` top-level op counts.
-/
private def isTopLevelExecutableOp (ctx : IRContext OpCode) (op : OperationPtr) : Bool :=
  match op.getOpType! ctx with
  | .llvm .func => false
  | _ => true

inductive EntryPoint where
  | mainFunc (op : OperationPtr)
  | topLevel

inductive EntryPointError where
  | none
  | multiple

private structure EntryPointScan where
  mainOp? : Option OperationPtr := none
  hasMultipleMains : Bool := false
  hasTopLevelCode : Bool := false

/-- Scan the module's top-level ops for entry points. -/
partial def scanEntryPoints (ctx : IRContext OpCode) (op : Option OperationPtr)
    (scan : EntryPointScan := {}) : EntryPointScan :=
  match op with
  | none => scan
  | some op =>
    let scan :=
      if isZeroArgMainFunc ctx op then
        match scan.mainOp? with
        | none => { scan with mainOp? := some op }
        | some _ => { scan with hasMultipleMains := true }
      else if isTopLevelExecutableOp ctx op then
        { scan with hasTopLevelCode := true }
      else
        scan
    scanEntryPoints ctx (op.get! ctx).next scan

/-- Resolve the unique entry point of the module, if one exists. -/
def resolveEntryPoint (ctx : IRContext OpCode) (moduleOp : OperationPtr) : Except EntryPointError EntryPoint :=
  let region := moduleOp.getRegion! ctx 0
  match (region.get! ctx).firstBlock with
  | none => .error .none
  | some blockPtr =>
    let scan := scanEntryPoints ctx (blockPtr.get! ctx).firstOp
    if scan.hasMultipleMains || (scan.mainOp?.isSome && scan.hasTopLevelCode) then
      .error .multiple
    else
      match scan.mainOp?, scan.hasTopLevelCode with
      | some mainOp, false => .ok (.mainFunc mainOp)
      | none, true => .ok .topLevel
      | _, _ => .error .none

/-- Report an interpreter result to the CLI. Hard failures (`none`) use a generic error. -/
def reportInterpResult (result : Interp (Array RuntimeValue)) : IO Unit :=
  match result with
  | some (.ok results) => IO.println s!"Program output: {results}"
  | some .ub => IO.println "Undefined behavior"
  | none => IO.eprintln "Error while interpreting module"

set_option warn.sorry false in
def main (args : List String) : IO Unit := do
  match args with
  | [filename] =>
    match ← parseOperation filename with
    | .ok (ctx, op) =>
      match ctx.verify with
      | .ok _ =>
        let rawCtx : IRContext OpCode := ctx
        match resolveEntryPoint rawCtx op with
        | .ok (.mainFunc mainOp) =>
          let result := bind (interpretRegion rawCtx (mainOp.getRegion! rawCtx 0) InterpreterState.empty (by sorry) (by sorry))
                             (fun (_, r) => pure r)
          reportInterpResult result
        | .ok .topLevel =>
          reportInterpResult (interpretModule rawCtx op (by sorry) (by sorry))
        | .error .none =>
          IO.eprintln "Error: No entry point: define a function named 'main' or use top-level executable ops"
        | .error .multiple =>
          IO.eprintln "Error: Multiple entry points: define exactly one zero-argument function named 'main' or use only top-level executable ops"
      | .error errMsg => IO.eprintln s!"Error verifying input program: {errMsg}"
    | .error errMsg =>
      IO.eprintln s!"Error: {errMsg}"
  | _ =>
    IO.eprintln "Wrong number of arguments."
    IO.eprintln "Usage: veir-interpret <filename>"
