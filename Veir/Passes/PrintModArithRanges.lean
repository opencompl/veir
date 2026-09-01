module

public import Veir.Pass
public import Veir.Analysis.DataFlow.IntegerRangeAnalysis

namespace Veir

private def IntegerRangeLattice.format : IntegerRangeLattice → String
  | .bottom => "bottom"
  | .top => "top"
  | .interval range => s!"[{range.lower}, {range.upper}]"

private def printRange
    (label : String)
    (value : ValuePtr)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : IO Unit := do
  let .modArithType _ := (value.getType! irCtx.raw).val | return
  let range := IntegerRangeAnalysis.getRange value dfCtx
  IO.println s!"// mod_arith.range {label} = {range.format}"

private partial def printRangesRecursively
    (op : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : IO Unit := do
  let opName := String.fromUTF8! (IsOpCode.name (op.getOpType! irCtx.raw))
  for i in [0:op.getNumResults! irCtx.raw] do
    printRange s!"{opName} result {i}" (op.getResult i) dfCtx irCtx

  for regionPtr in (op.get! irCtx.raw).regions do
    let region := regionPtr.get! irCtx.raw
    let mut maybeBlock := region.firstBlock
    while let some block := maybeBlock do
      for i in [0:block.getNumArguments! irCtx.raw] do
        printRange s!"block argument {i}" (block.getArgument i) dfCtx irCtx

      let mut maybeOp := (block.get! irCtx.raw).firstOp
      while let some nestedOp := maybeOp do
        printRangesRecursively nestedOp dfCtx irCtx
        maybeOp := (nestedOp.get! irCtx.raw).next
      maybeBlock := (block.get! irCtx.raw).next

private def PrintModArithRangesPass.impl
    (ctx : WfIRContext OpCode)
    (op : OperationPtr)
    (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) := do
  let some dfCtx := fixpointSolve op #[IntegerRangeAnalysis] ctx
    | throw "ModArith range analysis did not converge"
  printRangesRecursively op dfCtx ctx
  return ctx

/-- Run ModArith range analysis and print its SSA-value facts without changing the IR. -/
public def PrintModArithRangesPass : Pass OpCode :=
  { name := "print-mod-arith-ranges"
    description := "Print inferred ranges for ModArith SSA values."
    run := fun _ => PrintModArithRangesPass.impl }

end Veir
