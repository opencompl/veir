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
  HasDialectOpInfo.hasSideEffects opType (op.getProperties! ctx opType)

/--
  Does this operation read memory?

  An operation that carries regions reads memory whenever anything nested
  inside it does, and `HasDialectOpInfo.readsMemory` sees only an opcode and
  its properties, so it cannot answer for the nested operations. Such an
  operation is therefore reported conservatively rather than being asked.

  This mirrors MLIR's `isMemoryEffectFree`, which reports an operation as
  having effects unless it either declares them through
  `MemoryEffectOpInterface` or opts into a walk of its regions through
  `HasRecursiveMemoryEffects`. No opcode opts into that walk here yet, so the
  conservative answer is the only one available.
-/
def OperationPtr.readsMemory {OpInfo : Type} [HasOpInfo OpInfo]
    (op : OperationPtr) (ctx : IRContext OpInfo) : Bool :=
  if op.getNumRegions! ctx != 0 then true else
  let opType := op.getOpType! ctx
  HasDialectOpInfo.readsMemory opType (op.getProperties! ctx opType)

/--
  Does this operation write memory?

  This does not imply a complete overwrite of any particular location.

  Operations carrying regions are reported conservatively, for the reason
  given on `OperationPtr.readsMemory`.
-/
def OperationPtr.writesMemory {OpInfo : Type} [HasOpInfo OpInfo]
    (op : OperationPtr) (ctx : IRContext OpInfo) : Bool :=
  if op.getNumRegions! ctx != 0 then true else
  let opType := op.getOpType! ctx
  HasDialectOpInfo.writesMemory opType (op.getProperties! ctx opType)

end

end Veir
