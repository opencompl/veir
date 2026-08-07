module

public import Veir.IR.Basic

/-!
# SideEffectInterfaces

This file provides support for querying the side effects of operations.

Also see:
https://github.com/llvm/llvm-project/blob/main/mlir/include/mlir/Interfaces/SideEffectInterfaces.td
-/

namespace Veir

public section

/--
  May this operation read memory?

  TODO: recursively walk regions to get a less conservative answer
-/
def OperationPtr.readsMemory {OpInfo : Type} [HasOpInfo OpInfo]
    (op : OperationPtr) (ctx : IRContext OpInfo) : Bool :=
  if op.getNumRegions! ctx != 0 then true else
  let opType := op.getOpType! ctx
  HasOpInfo.readsMemory opType (op.getProperties! ctx opType)

/--
  May this operation write memory?

  TODO: recursively walk regions to get a less conservative answer
-/
def OperationPtr.writesMemory {OpInfo : Type} [HasOpInfo OpInfo]
    (op : OperationPtr) (ctx : IRContext OpInfo) : Bool :=
  if op.getNumRegions! ctx != 0 then true else
  let opType := op.getOpType! ctx
  HasOpInfo.writesMemory opType (op.getProperties! ctx opType)

end

end Veir
