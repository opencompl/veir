module

public import Veir.Passes.PrintDataFlow
public import Veir.Analysis.DataFlow.ModArithRangeAnalysis

namespace Veir

private def isModArithValue (value : ValuePtr) (irCtx : WfIRContext OpCode) : Bool :=
  match (value.getType! irCtx.raw).val with
  | .modArithType _ => true
  | _ => false

private def rangePrinter : DataFlowFactPrinter :=
  .sparse "mod_arith.range" .modArithRange (shouldPrint := isModArithValue)

/-- Run ModArith range analysis and print its SSA-value facts without changing the IR. -/
public def PrintModArithRangesPass : Pass OpCode :=
  mkPrintDataFlowPass
    "print-mod-arith-ranges"
    "Print inferred ranges for ModArith SSA values."
    #[{ analysis := ModArithRangeAnalysis, factPrinters := #[rangePrinter] }]

end Veir
