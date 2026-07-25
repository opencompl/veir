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
uses, and it has no side effects.
-/
def OperationPtr.isTriviallyDead {OpInfo : Type} [HasOpInfo OpInfo]
    (op : OperationPtr) (ctx : IRContext OpInfo) : Prop :=
  op.getNumRegions! ctx = 0
    ∧ !op.hasUses! ctx
    ∧ !op.hasSideEffects ctx

theorem OperationPtr.isTriviallyDead_iff {OpInfo : Type} [HasOpInfo OpInfo]
    (op : OperationPtr) (ctx : IRContext OpInfo) :
    op.isTriviallyDead ctx ↔
      op.getNumRegions! ctx = 0
        ∧ !op.hasUses! ctx
        ∧ !op.hasSideEffects ctx := by
  rfl

instance {OpInfo : Type} [HasOpInfo OpInfo] (op : OperationPtr) (ctx : IRContext OpInfo) :
    Decidable (op.isTriviallyDead ctx) :=
  decidable_of_iff _ (OperationPtr.isTriviallyDead_iff op ctx).symm

end

end Veir
