module

public import Veir.Interfaces.SideEffectInterfaces

/-!
# DeadCodeInterfaces

This file provides support for identifying trivially dead operations.
-/

namespace Veir

public section

/--
An operation is trivially dead when it has no regions, none of its results have
uses, it neither writes nor allocates memory, and it does not terminate its block.

Reading memory alone does not keep an operation alive, so a non-volatile load
whose results are unused is dead. Allocation is retained because the interpreter
observes the final memory, including allocated blocks and the next fresh address.

-/
abbrev OperationPtr.isTriviallyDead {OpInfo : Type} [HasOpInfo OpInfo]
    (op : OperationPtr) (ctx : IRContext OpInfo) : Prop :=
  op.getNumRegions! ctx = 0
    ∧ !op.hasUses! ctx
    ∧ !(op.getEffects ctx).writes
    ∧ !(op.getEffects ctx).allocates
    ∧ !HasOpInfo.isTerminator (op.getOpType! ctx)

end

end Veir
