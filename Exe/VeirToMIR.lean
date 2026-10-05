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
      let topOps := match (region.get! rawCtx).firstBlock with
        | some b => Veir.MIRPrinter.collectOps rawCtx (b.get! rawCtx).firstOp
        | none => #[]
      let funcOps := topOps.filter (·.isFunctionLike rawCtx)
      let globalOps := topOps.filter (·.getOpType! rawCtx == .llvm .mlir__global)
      if !funcOps.any (Veir.MIRPrinter.hasBody rawCtx) then
        IO.eprintln "Error: no function with a body found in module"
        IO.Process.exit 1
      Veir.MIRPrinter.printMIR rawCtx funcOps globalOps
    | .error errMsg =>
      IO.eprintln errMsg
      IO.Process.exit 1
