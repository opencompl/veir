module

public import Veir.Pass
public import Veir.Passes.RegisterAllocation.RegisterAllocator

namespace Veir


/--
Assign registers to the functions of the module `op`.

The shape of module this accepts, from the outside in:

- a *single region*, holding
- a *single block*, the module body, with *no block arguments*, holding
- *sibling functions*, each with *no input arguments* and *no return values*, whose
  body is a *single block* with *no nested regions* in it.

Anything else is rejected rather than worked around.

Operations in the module body that are not function are passed over, as are function
declarations, which have no body to allocate.

Every function is checked before any is rewritten, so the pass either allocates all of them
or leaves the module untouched.
-/
def RegisterAllocationPass.impl (ctx : WfIRContext OpCode) (op : OperationPtr)
    (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) := do
    if op.getNumRegions! ctx.raw != 1 then
        throw "register allocation expects a module with a single region"
    let region := (op.getRegions! ctx.raw)[0]!
    let some body := region.getFirstBlock! ctx.raw | return ctx
    if (body.getNextBlock! ctx.raw).isSome then
        throw "register allocation expects a module body with a single block"
    if body.getNumArguments! ctx.raw != 0 then
        throw "register allocation does not support block arguments"
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
        match checkBlockAllocatable ctx entry with
        | .error e => throw e
        | .ok _ => pure ()
        entries := entries.push entry
    let mut ctx := ctx
    for entry in entries do
        ctx ← allocateBlock ctx entry
    return ctx

public def RegisterAllocationPass : Pass OpCode :=
  { name := "register-allocation-riscv64"
    description := "Assign RV64 virtual registers in single-block riscv functions with no arguments or return values."
    run := fun _ => RegisterAllocationPass.impl }
