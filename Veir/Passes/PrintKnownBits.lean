module

public import Veir.Passes.PrintDataFlow
public import Veir.Analysis.DataFlow.KnownBitsAnalysis

namespace Veir

private def isIntegerValue (value : ValuePtr) (irCtx : WfIRContext OpCode) : Bool :=
  match (value.getType! irCtx.raw).val with
  | .integerType _ => true
  | _ => false

private def knownBitsPrinter : DataFlowFactPrinter :=
  .sparse "known_bits" .knownBits (shouldPrint := isIntegerValue)

/-- Run known-bits analysis and print its integer SSA-value facts without changing the IR. -/
public def PrintKnownBitsPass : Pass OpCode :=
  mkPrintDataFlowPass
    "print-known-bits"
    "Print inferred known bits for integer SSA values."
    #[{ analysis := KnownBitsAnalysis, factPrinters := #[knownBitsPrinter] }]

end Veir
