module

public import Veir.Pass
public import Veir.Passes.RegisterAllocation.RegisterAllocator

namespace Veir


/--
The entry blocks of the functions in the module `op`, or an error naming the first
constraint `op` breaks.

The shape of module this accepts, from the outside in:

- a *single region*, holding
- a *single block*, the module body, with *no block arguments*, holding
- *sibling functions*, each with *no input arguments* and *no return values*, whose body is
  a *single block* with *no nested regions* in it.

Anything else is rejected rather than worked around.

Operations in the module body that are not function are passed over, as are function
declarations, which have no body to allocate.
-/
def RegisterAllocationPass.allocatableBlocks (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Except String (Array BlockPtr) := do
    if op.getNumRegions! ctx.raw != 1 then
        throw "register allocation expects a module with a single region"
    let region := (op.getRegions! ctx.raw)[0]!
    let some body := region.getFirstBlock! ctx.raw | return #[]
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
        if funcOp.getNumResults != 0 then
            throw "register allocation does not support function return values"
        -- scan for nested regions inside each operation
        let mut inner? := entry.getFirstOp! ctx.raw
        while let some inner := inner? do
            inner? := inner.getNextOp! ctx.raw
            if inner.getNumRegions! ctx.raw != 0 then
                throw "register allocation does not support operations with nested regions"
        entries := entries.push entry
    return entries

/--
Assign registers to the functions of the module `op`.

Every function is collected and checked by `allocatableBlocks` before any is rewritten, so
the pass either allocates all of them or leaves the module untouched.
-/
def RegisterAllocationPass.impl (ctx : WfIRContext OpCode) (op : OperationPtr)
    (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) := do
    let entries ← RegisterAllocationPass.allocatableBlocks ctx op
    let mut ctx := ctx
    for entry in entries do
        ctx ← allocateBlock ctx entry
    return ctx

public def RegisterAllocationPass : Pass OpCode :=
  { name := "register-allocation-riscv64"
    description := "Assign RV64 virtual registers in single-block riscv functions with no arguments or return values."
    run := fun _ => RegisterAllocationPass.impl }
