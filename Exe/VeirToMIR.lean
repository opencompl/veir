import Veir.Parser.MlirParser
import Veir.Input
import Veir.MIRPrinter

/-!
  # veir2mir CLI tool

  Reads an MLIR program from a file or from standard input, whose functions
  have been lowered to the VeIR `riscv` / `riscv_cf` dialects, and prints LLVM
  pre-register-allocation MIR for all of them, targeting riscv64 Linux with
  the lp64d ABI.

  A module that is not fully lowered is rejected: the tool prints an error and
  exits with status 1 without printing any MIR. Only functions, globals and
  `llvm.module_flags` may appear at the top level of the module.
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
    match ← parseSourceFile filename with
    | .ok (ctx, moduleOp, _) =>
      let rawCtx : IRContext OpCode := ctx
      let region := moduleOp.getRegion! rawCtx 0
      let topOps := match region.getFirstBlock! rawCtx with
        | some b => Veir.MIRPrinter.collectOps rawCtx (b.getFirstOp! rawCtx)
        | none => #[]
      let funcOps := topOps.filter (·.isFunctionLike rawCtx)
      let globalOps := topOps.filter (·.getOpType! rawCtx == .llvm .mlir__global)
      -- Module flags are metadata that the MIR does not carry; anything else at the
      -- top level, such as an alias or a comdat, would be silently lost.
      for op in topOps do
        if !op.isFunctionLike rawCtx && op.getOpType! rawCtx != .llvm .mlir__global &&
            op.getOpType! rawCtx != .llvm .module_flags then
          IO.eprintln s!"veir2mir: error: unsupported top-level operation '{Veir.MIRPrinter.opName rawCtx op}'"
          IO.Process.exit 1
      if !funcOps.any (Veir.MIRPrinter.hasBody rawCtx) then
        IO.eprintln "Error: no function with a body found in module"
        IO.Process.exit 1
      -- Buffer the output so that a rejected module prints no partial MIR.
      let buffer ← IO.mkRef {}
      try
        IO.withStdout (IO.FS.Stream.ofBuffer buffer) do
          Veir.MIRPrinter.printMIR rawCtx funcOps globalOps
      catch e =>
        IO.eprintln s!"veir2mir: error: {e}"
        IO.Process.exit 1
      (← IO.getStdout).write (← buffer.get).data
    | .error errMsg =>
      IO.eprintln errMsg
      IO.Process.exit 1
