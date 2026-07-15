import Veir.Parser.MlirParser
import Veir.IR.Basic
import Veir.MIRPrinter

/-!
  # veir2mir CLI tool

  Reads an MLIR file whose `main` function has been lowered to the VeIR
  `riscv` / `riscv_cf` dialects and prints LLVM pre-register-allocation MIR.
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
    match parseTopLevelOp.run parserState parser with
    | .ok (op, state, _) =>
      return (state.ctx, op)
    | .error errMsg =>
      throw s!"Error parsing operation: {errMsg}"
  | .error errMsg =>
    throw s!"Error reading file: {errMsg}"

/-- Find the first `llvm.func` / `func.func` in the module's top block. -/
partial def findFunc (ctx : IRContext OpCode) (op : Option OperationPtr) : Option OperationPtr :=
  match op with
  | none => none
  | some op =>
    match op.getOpType! ctx with
    | .llvm .func | .func .func => some op
    | _ => findFunc ctx (op.get! ctx).next

def main (args : List String) : IO Unit := do
  match args with
  | [filename] =>
    match ← parseOperation filename with
    | .ok (ctx, moduleOp) =>
      let rawCtx : IRContext OpCode := ctx
      let region := moduleOp.getRegion! rawCtx 0
      let funcOp := match (region.get! rawCtx).firstBlock with
        | some b => findFunc rawCtx (b.get! rawCtx).firstOp
        | none => none
      match funcOp with
      | some f => Veir.MIRPrinter.printMIR rawCtx f
      | none =>
        IO.eprintln "Error: no llvm.func / func.func found in module"
        IO.Process.exit 1
    | .error errMsg =>
      IO.eprintln s!"Error: {errMsg}"
      IO.Process.exit 1
  | _ =>
    IO.eprintln "Usage: veir2mir <filename>"
    IO.Process.exit 2
