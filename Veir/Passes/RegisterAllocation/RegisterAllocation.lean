module

public import Veir.Pass
public import Veir.Passes.RegisterAllocation.RegisterAllocator

namespace Veir


def RegisterAllocationPass.impl (ctx : WfIRContext OpCode) (op : OperationPtr)
    (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) := do
    -- `op` is the module: one region, one block, whose ops are the functions.
    let region := (op.getRegions! ctx.raw)[0]!
    let some body := region.getFirstBlock! ctx.raw | return ctx
    let mut entries : Array BlockPtr := #[]
    let mut f? := body.getFirstOp! ctx.raw
    while let some f := f? do
        f? := f.getNextOp! ctx.raw
        let some funcOp := FunctionOp.of? f ctx.raw | continue
        let some entry := funcOp.getEntryBlock? | continue
        if (entry.getNextBlock! ctx.raw).isSome then
            throw "register allocation requires a single-block function"
        if entry.getNumArguments! ctx.raw != 0 then
            throw "register allocation does not support block arguments"
        if funcOp.getNumArguments != 0 then
            throw "register allocation does not support function arguments"
        if funcOp.getNumResults != 0 then
            throw "register allocation does not support function return values"
        entries := entries.push entry
    let mut ctx := ctx
    for entry in entries do
        ctx ← allocateBlock ctx entry
    return ctx

public def RegisterAllocationPass : Pass OpCode :=
  { name := "register-allocation-riscv64"
    description := "Assign RV64 registers in sibling single-block riscv functions with no arguments or return values."
    run := fun _ => RegisterAllocationPass.impl }
