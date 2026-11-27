module

public import Veir.Pass
import Veir.Passes.RegisterAllocation.RegisterAllocator
import Veir.Passes.RegisterAllocation.Helper

namespace Veir


/--
Assign registers to the functions of the module `op`.

Every function is collected and checked by `allocatableBlocks` before any is rewritten, so
the pass either allocates all of them or leaves the module untouched.
-/
def RegisterAllocationPass.impl (ctx : WfIRContext OpCode) (op : OperationPtr)
    (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) := do
    let entries ← allocatableBlocks ctx op
    let mut ctx := ctx
    for entry in entries do
        ctx ← allocateBlock ctx entry
    return ctx

public def RegisterAllocationPass : Pass OpCode :=
  { name := "register-allocation-riscv64"
    description := "Assign RV64 virtual registers in single-block riscv functions with no arguments or return values."
    run := fun _ => RegisterAllocationPass.impl }
