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

partial def topLevelOps (ctx : IRContext OpCode) (op : OperationPtr) : Array OperationPtr :=
  if op.getNumRegions! ctx != 1 then #[] else
  match (op.getRegion! ctx 0 |>.get! ctx).firstBlock with
  | none => #[]
  | some b =>
    let rec go (o : Option OperationPtr) : Array OperationPtr :=
      match o with
      | none => #[]
      | some o => #[o] ++ go (o.get! ctx).next
    go (b.get! ctx).firstOp

def isNonExecutableTopLevel (ctx : IRContext OpCode) (op : OperationPtr) : Bool :=
  match op.getOpType! ctx with
  | .llvm .func | .func .func | .llvm .module_flags => true
  | _ => false

def symName? (ctx : IRContext OpCode) (op : OperationPtr) : Option String :=
  match (op.get! ctx).attrs.entries.find? (·.1 == "sym_name".toUTF8) with
  | some (_, .stringAttr s) => some (String.fromUTF8! s.value)
  | _ => none

set_option warn.sorry false in
def interpretInput (ctx : IRContext OpCode) (op : OperationPtr) :
    Except String (Interp (Array RuntimeValue)) :=
  let ops := topLevelOps ctx op
  match ops.find? fun o => symName? ctx o == some "main" with
  | some m => .ok do
      let (_, r) ← interpretRegion ctx (m.getRegion! ctx 0) InterpreterState.empty
                     (by sorry) (by sorry)
      return r
  | none =>
    if !ops.isEmpty && ops.all (isNonExecutableTopLevel ctx) then
      .error "No entry point: define a function named 'main' or use top-level executable ops"
    else
      .ok (interpretModule ctx op (by sorry) (by sorry))

set_option warn.sorry false in
def main (args : List String) : IO Unit := do
  match args with
  | [filename] =>
    match ← parseOperation filename with
    | .ok (ctx, op) =>
      match ctx.verify with
      | .ok _ =>
        match interpretInput ctx op with
        | .ok interpResult =>
          match interpResult with
          | some (.ok results) => IO.println s!"Program output: {results}"
          | some .ub => IO.println "Undefined behavior"
          | none => IO.eprintln "Error while interpreting module"
        | .error errMsg => IO.eprintln s!"Error: {errMsg}"
      | .error errMsg => IO.eprintln s!"Error verifying input program: {errMsg}"
    | .error errMsg =>
      IO.eprintln s!"Error: {errMsg}"
  | _ =>
    IO.eprintln "Wrong number of arguments."
    IO.eprintln "Usage: veir-interpret <filename>"
