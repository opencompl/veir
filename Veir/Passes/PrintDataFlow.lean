module

public import Veir.Pass
public import Veir.Analysis.DataFlow.Printer

public section

namespace Veir

/--
Build a read only pass that solves a set of dataflow analyses and prints selected
facts.
-/
def mkPrintDataFlowPass
    (name description : String)
    (analyses : Array DataFlowAnalysis)
    (printers : Array DataFlowFactPrinter) : Pass OpCode :=
  { name
    description
    run := fun _ ctx op _ => do
      let some dfCtx := fixpointSolve op analyses ctx
        | throw "dataflow analyses did not converge"
      printDataFlowFacts op printers dfCtx ctx
      return ctx }

end Veir
