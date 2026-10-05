module

public import Veir.Pass
public import Veir.Analysis.DataFlow.Printer
public import Veir.Analysis.DataFlow.DeadCodeAnalysis
public import Veir.Analysis.DataFlow.ModArithRangeAnalysis
public import Veir.Analysis.DataFlow.SparseConstantPropagationAnalysis

public section

namespace Veir

private def runAndPrint
    (analyses : Array DataFlowAnalysis)
    (ctx : WfIRContext OpCode)
    (op : OperationPtr) : ExceptT String IO (WfIRContext OpCode) := do
      let some dfCtx := fixpointSolve op analyses ctx
        | throw "dataflow analyses did not converge"
      printDataFlowFacts op analyses dfCtx ctx
      return ctx

/--
Solve selected dataflow analyses and print their facts after the shared solver
reaches a fixpoint. Individual analyses provide their own fact renderers.
-/
def PrintDataFlowPass : Pass OpCode :=
  { name := "print-dataflow"
    description := "Print selected dataflow analysis results."
    options := (Std.HashMap.emptyWithCapacity 2)
      |>.insert "sccp"
        { description := "Print sparse conditional constant propagation and liveness facts." }
      |>.insert "mod-arith-ranges"
        { description := "Print ModArith range-analysis facts." }
    run := fun options ctx op _ => do
      let mut analyses := #[]
      if options.getD "sccp" false then
        analyses := analyses ++ #[SparseConstantPropagationAnalysis, DeadCodeAnalysis]
      if options.getD "mod-arith-ranges" false then
        analyses := analyses.push ModArithRangeAnalysis
      if analyses.isEmpty then
        throw "select at least one analysis (sccp or mod-arith-ranges)"
      runAndPrint analyses ctx op }

end Veir
