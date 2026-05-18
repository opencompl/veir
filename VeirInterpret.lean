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

/-- Searches the module's top-level ops for an `llvm.func @main` with no arguments. -/
partial def findMainFunc (ctx : IRContext OpCode) (moduleOp : OperationPtr) : Option OperationPtr :=
  let region := moduleOp.getRegion! ctx 0
  match (region.get! ctx).firstBlock with
  | none => none
  | some blockPtr =>
    let rec go : Option OperationPtr → Option OperationPtr
      | none => none
      | some op =>
        let isMain : (opCode : OpCode) → propertiesOf opCode → Bool
          | .llvm .func, props => isFuncWithName ctx op "main" && hasNoArgs props
          | _, _ => false
        let opType := op.getOpType! ctx
        if isMain opType (op.getProperties! ctx opType) then some op
        else go (op.get! ctx).next
    go (blockPtr.get! ctx).firstOp

set_option warn.sorry false in
def main (args : List String) : IO Unit := do
  match args with
  | [filename] =>
    match ← parseOperation filename with
    | .ok (ctx, op) =>
      match ctx.verify with
      | .ok _ =>
        let rawCtx : IRContext OpCode := ctx
        let report : Interp (Array RuntimeValue) → String → IO Unit
          | some (.ok results), _ => IO.println s!"Program output: {results}"
          | some .ub,           _ => IO.println "Undefined behavior"
          | none,             msg => IO.eprintln msg
        match findMainFunc rawCtx op with
        | some mainOp =>
          let result := bind (interpretRegion rawCtx (mainOp.getRegion! rawCtx 0) InterpreterState.empty (by sorry) (by sorry))
                             (fun (_, r) => pure r)
          report result "Error while interpreting module"
        | none =>
          report (interpretModule rawCtx op (by sorry) (by sorry))
                 "Error: No entry point: define a function named 'main' or use top-level executable ops"
      | .error errMsg => IO.eprintln s!"Error verifying input program: {errMsg}"
    | .error errMsg =>
      IO.eprintln s!"Error: {errMsg}"
  | _ =>
    IO.eprintln "Wrong number of arguments."
    IO.eprintln "Usage: veir-interpret <filename>"
