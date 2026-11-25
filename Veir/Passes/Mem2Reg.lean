module

public import Veir.Pass
import Veir.Passes.Mem2Reg.Basic
import Veir.PatternRewriter.Basic

namespace Veir
namespace Mem2Reg

/-- Promote supported allocations in a `func.func` body. Collect candidates
before erasure, then check each against the context left by earlier promotions. -/
private def promoteFunction (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode) := do
  if op.getOpType! ctx.raw != .func .func then return ctx
  let some function := FunctionOp.of? op ctx.raw | return ctx
  let some entry := function.getEntryBlock? | return ctx
  let region := function.getFunctionBody!
  let mut allocations := #[]
  let mut next := entry.getFirstOp! ctx.raw
  while let some op := next do
    if op.getOpType! ctx.raw == .llvm .alloca then
      allocations := allocations.push op
    next := op.getNextOp! ctx.raw
  let mut ctx := ctx
  for allocation in allocations do
    if allocation.InBounds ctx.raw then
      let (_, promoted) ← promoteSingleBlock? ctx region allocation
      ctx := promoted
  return ctx

def Mem2RegPass.impl (ctx : WfIRContext OpCode) (op : OperationPtr)
    (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) := do
  let functions := if op.isFunctionLike ctx.raw then #[op]
    else collectNestedFunctions ctx.raw op
  let mut ctx := ctx
  for function in functions do
    let some promoted := promoteFunction ctx function
      | throw "Error while promoting allocations"
    ctx := promoted
  return ctx

end Mem2Reg

public def Mem2RegPass : Pass OpCode :=
  { name := "mem2reg"
    description := "Promote initialised scalar allocations in single-block func.func bodies."
    run := fun _ => Mem2Reg.Mem2RegPass.impl }

end Veir
