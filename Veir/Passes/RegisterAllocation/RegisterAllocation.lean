module

public import Veir.Pass
import Veir.Passes.RegisterAllocation.RegisterAllocator
import Veir.Passes.RegisterAllocation.Helper

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
    let some block ← getModuleBlock ctx op | return #[]
    let mut entries : Array BlockPtr := #[]
    let mut f? := block.getFirstOp! ctx.raw
    while let some f := f? do
        f? := f.getNextOp! ctx.raw
        let some fctBlock ← getFunctionEntry ctx f | continue
        entries := entries.push fctBlock
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
