module

public import Veir.IR.Basic

/-!
# SideEffectInterfaces

This file provides support for querying the side effects of operations.

There are two questions to ask, and they are not the same one:

* `hasSideEffects` — may this operation be deleted, moved, or duplicated?
  A non-volatile load answers `false`: reading memory does not prevent
  removing a load whose result is unused. This is the predicate DCE and CSE
  want.
* `isMemoryEffectFree` — may this operation be *executed* somewhere other
  than where it stands, in particular at compile time against a memory that
  is not the program's? A load answers `false` whether or not it is volatile.
  This is the predicate constant folding and data-flow analyses want.

The second implies the first. Reaching for `hasSideEffects` when the question
was really the second one is how a folder ends up evaluating a load against an
empty memory and miscompiling.

We track only whether an operation reads memory, which is all the above
requires. MLIR additionally distinguishes writes from allocations and frees,
attaches effects to individual values, and treats speculatability (freedom
from undefined behaviour) as a third axis; `isPure` there is
`isMemoryEffectFree` plus speculatability. We have none of that, so this is
deliberately not called `isPure`.

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
  Is an operation with this opcode and these properties free of memory
  effects, i.e. does it neither read nor write memory and have no other
  effect that would make it ineligible to be moved?

  Such an operation computes a function of its operands alone, so it may be
  executed anywhere its operands are available — including at compile time,
  against a memory that is not the program's.

  Note that this is strictly stronger than `¬ hasSideEffects`, which permits
  reading operations.
-/
def isMemoryEffectFree {OpInfo : Type} [HasOpInfo OpInfo] (opType : OpInfo)
    (props : HasOpInfo.propertiesOf opType) : Bool :=
  !HasOpInfo.hasSideEffects opType props && !HasOpInfo.readsMemory opType

/-- `isMemoryEffectFree` for an operation in the IR. -/
def OperationPtr.isMemoryEffectFree {OpInfo : Type} [HasOpInfo OpInfo]
    (op : OperationPtr) (ctx : IRContext OpInfo) : Bool :=
  let opType := op.getOpType! ctx
  Veir.isMemoryEffectFree opType (op.getProperties! ctx opType)

end

end Veir
