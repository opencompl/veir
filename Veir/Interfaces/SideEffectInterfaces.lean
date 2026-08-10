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
  Does this operation have effects that make it ineligible for
  transformations that add / remove / rearrange instructions?

  NOTE: ¬ hasSideEffects does not imply that an operation is safe to
        speculate. For that we also need it to never trigger immediate
        UB. We'll have to deal with this later on.

  Also see:
  https://mlir.llvm.org/docs/Rationale/SideEffectsAndSpeculation/
-/
def OperationPtr.hasSideEffects {OpInfo : Type} [HasOpInfo OpInfo]
    (op : OperationPtr) (ctx : IRContext OpInfo) : Bool :=
  let opType := op.getOpType! ctx
  HasOpInfo.hasSideEffects opType (op.getProperties! ctx opType)

/--
  What memory effects may this operation have?

  Upstream, an operation carrying regions reports the effects of the operations
  nested inside them when it has the `HasRecursiveMemoryEffects` trait, and is
  otherwise assumed to have unknown effects. We have neither the trait nor the
  recursive walk, so any operation with a region is treated conservatively.

  TODO: recursively walk regions to get a less conservative answer
-/
def OperationPtr.getEffects {OpInfo : Type} [HasOpInfo OpInfo]
    (op : OperationPtr) (ctx : IRContext OpInfo) : Array EffectInstance :=
  if op.getNumRegions! ctx != 0 then #[.read, .write] else
  let opType := op.getOpType! ctx
  HasOpInfo.getEffects opType (op.getProperties! ctx opType)

/-- May this operation read memory? -/
def OperationPtr.readsMemory {OpInfo : Type} [HasOpInfo OpInfo]
    (op : OperationPtr) (ctx : IRContext OpInfo) : Bool :=
  hasEffect (op.getEffects ctx) .read

/-- May this operation write memory? -/
def OperationPtr.writesMemory {OpInfo : Type} [HasOpInfo OpInfo]
    (op : OperationPtr) (ctx : IRContext OpInfo) : Bool :=
  hasEffect (op.getEffects ctx) .write

end

end Veir
