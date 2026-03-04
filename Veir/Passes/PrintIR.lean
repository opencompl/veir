import Veir.Pass
import Veir.Printer

namespace Veir

def PrintIRPass.impl (ctx : { ctx' : IRContext OpCode // ctx'.WellFormed })
    (op : OperationPtr) (_ : op.InBounds ctx.val) :
    ExceptT String IO { ctx' : IRContext OpCode // ctx'.WellFormed } := do

  IO.eprintln "// -----// IR Dump //----- //"

  let stdErr ← IO.getStderr
  IO.withStdout stdErr (Printer.printModule ctx.val op)
  return ctx

public def PrintIRPass : Pass OpCode :=
  { name := "print-ir"
    description := "Print the IR on the stderr stream."
    run := PrintIRPass.impl }
