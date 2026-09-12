module

public import Veir.Pass
public import Veir.Analysis.DataFlow.Printer

public section

namespace Veir

/-- A dataflow analysis paired with the fact renderers used to inspect it. -/
structure PrintableDataFlowAnalysis where
  analysis : DataFlowAnalysis
  factPrinters : Array DataFlowFactPrinter

/--
Build a read-only pass that solves a set of dataflow analyses and prints selected
facts using the generic dataflow result traversal.
-/
def mkPrintDataFlowPass
    (name description : String)
    (printableAnalyses : Array PrintableDataFlowAnalysis) : Pass OpCode :=
  { name
    description
    run := fun _ ctx op _ => do
      let analyses := printableAnalyses.map (·.analysis)
      let printers := printableAnalyses.foldl (init := #[])
        fun printers analysis => printers ++ analysis.factPrinters
      let some dfCtx := fixpointSolve op analyses ctx
        | throw "dataflow analyses did not converge"
      printDataFlowFacts op printers dfCtx ctx
      return ctx }

end Veir
