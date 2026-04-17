import Veir.Pass
import Veir.Printer

namespace Veir

def PrintIRPass.impl (ctx : WfIRContext OpCode)
    (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do

  IO.eprintln "// -----// IR Dump //----- //"

  let stdErr ← IO.getStderr
  IO.withStdout stdErr (Printer.printModule ctx.raw op)
  return ctx

public def PrintIRPass : Pass OpCode :=
  { name := "print-ir"
    description := "Print the IR on the stderr stream."
    run := PrintIRPass.impl }
