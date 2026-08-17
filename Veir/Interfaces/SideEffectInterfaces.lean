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
  Does this operation have effects that make it ineligible for
  transformations that add / remove / rearrange instructions?

  NOTE: ¬ hasSideEffects does not imply that an operation is safe to
        speculate. For that we also need it to never trigger immediate
        UB. We'll have to deal with this later on.

  NOTE: this interface is deprecated and will be removed
-/
def OperationPtr.hasSideEffects {OpInfo : Type} [HasOpInfo OpInfo]
    (op : OperationPtr) (ctx : IRContext OpInfo) : Bool :=
  let opType := op.getOpType! ctx
  HasOpInfo.hasSideEffects opType (op.getProperties! ctx opType)

/--
  What memory effects may this operation have?

  TODO: recursively walk regions to get a less conservative answer
-/
def OperationPtr.getEffects {OpInfo : Type} [HasOpInfo OpInfo]
    (op : OperationPtr) (ctx : IRContext OpInfo) : MemoryEffects :=
  if op.getNumRegions! ctx != 0 then .unknown else
  let opType := op.getOpType! ctx
  HasOpInfo.getEffects opType (op.getProperties! ctx opType)

/--
  Whether this operation is known to have no memory effects. This
  does not imply that the operation is safe to speculate: it may still
  affect control flow or trigger immediate undefined behavior.
-/
def OperationPtr.isMemoryIndependent {OpInfo : Type} [HasOpInfo OpInfo]
    (op : OperationPtr) (ctx : IRContext OpInfo) : Bool :=
  op.getEffects ctx == .none

end

end Veir
