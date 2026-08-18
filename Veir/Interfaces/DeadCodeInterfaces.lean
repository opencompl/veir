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
uses, it writes no memory, and it does not terminate its block.

This mirrors MLIR's `wouldOpBeTriviallyDead`. Note that neither reading nor
allocating memory keeps an operation alive: a non-volatile load and an `alloca`
whose results are unused are both dead.

-/
abbrev OperationPtr.isTriviallyDead {OpInfo : Type} [HasOpInfo OpInfo]
    (op : OperationPtr) (ctx : IRContext OpInfo) : Prop :=
  op.getNumRegions! ctx = 0
    ∧ !op.hasUses! ctx
    ∧ !(op.getEffects ctx).writes
    ∧ !HasOpInfo.isTerminator (op.getOpType! ctx)

end

end Veir
