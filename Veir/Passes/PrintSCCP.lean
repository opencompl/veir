import Veir.Passes.PrintDataFlow
import Veir.Analysis.DataFlow.DeadCodeAnalysis
import Veir.Analysis.DataFlow.SparseConstantPropagationAnalysis

namespace Veir

private def constantPrinter : DataFlowFactPrinter :=
  .sparse "constant" .sparseConstant

private def livenessPrinter : DataFlowFactPrinter :=
  { name := "liveness"
    format? := fun anchor dfCtx _ =>
      match anchor with
      | .InsertPoint _ | .CFGEdge _ =>
        some (toString (dfCtx.getOrMkFact .liveness anchor).latticeElement)
      | _ => none }

/-- Run SCCP and print its constant and executable state facts without changing the IR. -/
def PrintSCCPPass : Pass OpCode :=
  mkPrintDataFlowPass
    "print-sccp"
    "Print sparse conditional constant propagation facts."
    #[SparseConstantPropagationAnalysis, DeadCodeAnalysis]
    #[constantPrinter, livenessPrinter]

end Veir
