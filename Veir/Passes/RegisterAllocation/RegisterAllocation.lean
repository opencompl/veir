module

public import Veir.Pass
import Veir.Passes.RegisterAllocation.RegisterAllocator
import Veir.Passes.RegisterAllocation.RegisterPhysicalRename
import Veir.Passes.RegisterAllocation.Helper

namespace Veir


/--
Assign registers to the functions of the module `op`, with virtual-only (`physical := false`)
or physical output (`physical := true`).

Every function is collected and checked by `allocatableFunctions` (`Helper.lean`) before any is
rewritten, so unsupported function shapes are rejected before allocation starts.
-/
def RegisterAllocationPass.impl (physical : Bool) (ctx : WfIRContext OpCode) (op : OperationPtr)
    (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) := do
    let funcs ← allocatableFunctions ctx op
    let mut ctx := ctx
    for (_, entry) in funcs do
        let (allocated, values) ← allocateBlock ctx entry (collectValues := physical)
        ctx := allocated
        if physical then
            ctx ← renameToPhysicalRegisters ctx values
    return ctx

public def RegisterAllocationPass : Pass OpCode :=
  { name := "register-allocation-riscv64"
    description := "Assign RV64 registers in single-block, call-free riscv functions with at most 8 arguments and 2 results."
    options := .ofList [
      ("physical", { description := "Allocate physical registers instead of virtual registers." })]
    run := fun options => RegisterAllocationPass.impl (options.getD "physical" false) }
