import Veir.Parser.MlirParser
import Veir.Input
import Veir.MIRPrinter

/-!
  # veir2mir CLI tool

  Reads an MLIR program from a file or from standard input, whose functions
  have been lowered to the VeIR `riscv` / `riscv_cf` dialects, and prints LLVM
  pre-register-allocation MIR for all of them.
-/

open Veir.Parser
open Veir.Input
open Veir

/-- The function-like operations in the module's top block, in order. -/
partial def findFuncs (ctx : IRContext OpCode) (op : Option OperationPtr)
    (acc : Array OperationPtr := #[]) : Array OperationPtr :=
  match op with
  | none => acc
  | some op =>
    findFuncs ctx (op.get! ctx).next (if op.isFunctionLike ctx then acc.push op else acc)

def main (args : List String) : IO Unit := do
  match inputSourceOfArgs args with
  | .error errMsg =>
    IO.eprintln errMsg
    IO.eprintln "Usage: veir2mir [filename]"
    IO.eprintln "  Reads the program from standard input if no filename is given."
    IO.Process.exit 2
  | .ok filename =>
    match ← parseSourceFile filename (allowUnregisteredDialect := true)
        (verifyAfterParse := false) with
    | .ok (ctx, moduleOp, _) =>
      let rawCtx : IRContext OpCode := ctx
      let region := moduleOp.getRegion! rawCtx 0
      let funcOps := match (region.get! rawCtx).firstBlock with
        | some b => findFuncs rawCtx (b.get! rawCtx).firstOp
        | none => #[]
      if !funcOps.any (Veir.MIRPrinter.hasBody rawCtx) then
        IO.eprintln "Error: no function with a body found in module"
        IO.Process.exit 1
      Veir.MIRPrinter.printMIR rawCtx funcOps
    | .error errMsg =>
      IO.eprintln errMsg
      IO.Process.exit 1
