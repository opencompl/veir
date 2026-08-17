module

public import Veir.IR.Basic

/-!
# SideEffectInterfaces

This file provides support for querying the side effects of operations.

Also see:
https://mlir.llvm.org/docs/Rationale/SideEffectsAndSpeculation/
https://github.com/llvm/llvm-project/blob/main/mlir/include/mlir/Interfaces/SideEffectInterfaces.td
-/

namespace Veir

public section

/--
  What memory effects may this operation have?

  NOTE: An operation with no memory effects is not necessarily speculatable: it
        may still have undefined behavior or fail to terminate. MLIR models
        these properties separately with `ConditionallySpeculatable`; Veir does
        not support this interface yet.

  TODO: recursively walk regions to get a less conservative answer
-/
def OperationPtr.getEffects {OpInfo : Type} [HasOpInfo OpInfo]
    (op : OperationPtr) (ctx : IRContext OpInfo) : MemoryEffects :=
  if op.getNumRegions! ctx != 0 then .unknown else
  let opType := op.getOpType! ctx
  HasOpInfo.getEffects opType (op.getProperties! ctx opType)

end

end Veir
