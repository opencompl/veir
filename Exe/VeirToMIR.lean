import Veir.Parser.MlirParser
import Veir.Input
import Veir.MIRPrinter

/-!
  # veir2mir CLI tool

  Reads an MLIR program from a file or from standard input, whose `main`
  function has been lowered to the VeIR `riscv` / `riscv_cf` dialects, and
  prints LLVM pre-register-allocation MIR.
-/

open Veir.Parser
open Veir.Input
open Veir

/-- Find the first function-like operation in the module's top block. -/
partial def findFunc (ctx : IRContext OpCode) (op : Option OperationPtr) : Option OperationPtr :=
  match op with
  | none => none
  | some op =>
    if op.isFunctionLike ctx then some op
    else findFunc ctx (op.get! ctx).next

def main (args : List String) : IO Unit := do
  match inputSourceOfArgs args with
  | .error errMsg =>
    IO.eprintln errMsg
    IO.eprintln "Usage: veir2mir [filename]"
    IO.eprintln "  Reads the program from standard input if no filename is given."
    IO.Process.exit 2
  | .ok filename =>
    match ← parseOperation filename (allowUnregisteredDialect := true) with
    | .ok (ctx, moduleOp) =>
      let rawCtx : IRContext OpCode := ctx
      let region := moduleOp.getRegion! rawCtx 0
      let funcOp := match (region.get! rawCtx).firstBlock with
        | some b => findFunc rawCtx (b.get! rawCtx).firstOp
        | none => none
      match funcOp with
      | some f => Veir.MIRPrinter.printMIR rawCtx f
      | none =>
        IO.eprintln "Error: no function-like operation found in module"
        IO.Process.exit 1
    | .error errMsg =>
      IO.eprintln s!"Error: {errMsg}"
      IO.Process.exit 1
