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

def parseOperation (filename : String) : ExceptT String IO (WfIRContext OpCode × OperationPtr × String) := do
  let fileContent ← IO.FS.readBinFile filename
  let some (ctx, _) := WfIRContext.create OpCode
    | throw "Failed to create IR context"
  match ParserState.fromInput fileContent with
  | .ok parser =>
    match (parseOp none).run (MlirParserState.fromContext ctx) parser with
    | .ok (op, state, _) =>
      return (state.ctx, op, String.fromUTF8! fileContent)
    | .error errMsg =>
      throw s!"Error parsing operation: {errMsg}"
  | .error errMsg =>
    throw s!"Error reading file: {errMsg}"

def attrGet? (attrs : DictionaryAttr) (key : String) : Option Attribute :=
  attrs.entries.find? (fun entry => entry.1 == key.toUTF8) |>.map Prod.snd

def isFunctionOp (ctx : IRContext OpCode) (op : OperationPtr) : Bool :=
  match op.getOpType! ctx with
  | .llvm .func => true
  | .func .func => true
  | _ => false

def isModuleLevelMetadataOp (ctx : IRContext OpCode) (op : OperationPtr) : Bool :=
  match op.getOpType! ctx with
  | .llvm .module_flags => true
  | _ => false

def functionEntryHasNoArgs (ctx : IRContext OpCode) (op : OperationPtr) : Bool :=
  if op.getNumRegions! ctx != 1 then
    false
  else
    match (op.getRegion! ctx 0 |>.get! ctx).firstBlock with
    | none => false
    | some block => block.getNumArguments! ctx == 0

partial def firstModuleBlockOps (ctx : IRContext OpCode) (moduleOp : OperationPtr) : Array OperationPtr :=
  if moduleOp.getNumRegions! ctx != 1 then
    #[]
  else
    let region := moduleOp.getRegion! ctx 0
    match (region.get! ctx).firstBlock with
    | none => #[]
    | some block =>
      let rec collect (op : OperationPtr) : Array OperationPtr :=
        match (op.get! ctx).next with
        | none => #[op]
        | some next => #[op] ++ collect next
      match (block.get! ctx).firstOp with
      | none => #[]
      | some firstOp => collect firstOp

def hasModuleLevelExecutableOps (ctx : IRContext OpCode) (moduleOp : OperationPtr) : Bool :=
  (firstModuleBlockOps ctx moduleOp).any fun op =>
    !isFunctionOp ctx op && !isModuleLevelMetadataOp ctx op

def isZeroArgMain (ctx : IRContext OpCode) (op : OperationPtr) : Bool :=
  if !isFunctionOp ctx op || !functionEntryHasNoArgs ctx op then
    false
  else
    match attrGet? (op.get! ctx).attrs "sym_name", attrGet? (op.get! ctx).attrs "function_type" with
    | some (.stringAttr name), some (.functionType ty) =>
      String.fromUTF8! name.value == "main" && ty.inputs.isEmpty
    | _, _ => false

def sourceMentionsMain (source : String) : Bool :=
  (source.splitOn "sym_name = \"main\"").length > 1 ||
  (source.splitOn "\"sym_name\" = \"main\"").length > 1 ||
  (source.splitOn "sym_name=\"main\"").length > 1 ||
  (source.splitOn "\"sym_name\"=\"main\"").length > 1

def findZeroArgMain (ctx : IRContext OpCode) (moduleOp : OperationPtr) (source : String) : Option OperationPtr :=
  let ops := firstModuleBlockOps ctx moduleOp
  match ops.find? (isZeroArgMain ctx) with
  | some op => some op
  | none =>
    let zeroArgFunctions := ops.filter fun op => isFunctionOp ctx op && functionEntryHasNoArgs ctx op
    if sourceMentionsMain source && zeroArgFunctions.size == 1 then
      zeroArgFunctions[0]?
    else
      none

set_option warn.sorry false in
def interpretInput (ctx : IRContext OpCode) (op : OperationPtr) (source : String) :
    Except String (Interp (Array RuntimeValue)) :=
  if hasModuleLevelExecutableOps ctx op then
    .ok (interpretModule ctx op (by sorry) (by sorry))
  else
    match findZeroArgMain ctx op source with
    | some mainOp =>
      if mainOp.getNumRegions! ctx != 1 then
        .error "Expected main() to have one region"
      else
        .ok do
          let (_state, results) ← interpretRegion ctx (mainOp.getRegion! ctx 0) InterpreterState.empty (by sorry) (by sorry)
          return results
    | none =>
      .error "Expected executable operations at module level or a zero-argument function named main()"

set_option warn.sorry false in
def main (args : List String) : IO Unit := do
  match args with
  | [filename] =>
    match ← parseOperation filename with
    | .ok (ctx, op, source) =>
      match ctx.verify with
      | .ok _ =>
        match interpretInput ctx op source with
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
