import Veir.Passes.PrintDataFlow
import Veir.Analysis.DataFlow.DeadCodeAnalysis
import Veir.Analysis.DataFlow.SparseConstantPropagationAnalysis

namespace Veir

private def constantPrinter : DataFlowFactPrinter :=
  .sparse "constant" .sparseConstant

private def livenessPrinter : DataFlowFactPrinter :=
  .ofFact "liveness" .liveness #[.blockEntry, .cfgEdge] fun fact =>
    toString fact.latticeElement

/-- Run SCCP and print its constant and executable-state facts without changing the IR. -/
def PrintSCCPPass : Pass OpCode :=
  mkPrintDataFlowPass
    "print-sccp"
    "Print sparse conditional constant propagation facts."
    #[ { analysis := SparseConstantPropagationAnalysis
         factPrinters := #[constantPrinter] }
     , { analysis := DeadCodeAnalysis
         factPrinters := #[livenessPrinter] }
     ]

end Veir
