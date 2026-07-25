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
abbrev OperationPtr.isTriviallyDead {OpInfo : Type} [HasOpInfo OpInfo]
    (op : OperationPtr) (ctx : IRContext OpInfo) : Prop :=
  op.getNumRegions! ctx = 0
    ∧ !op.hasUses! ctx
    ∧ !op.hasSideEffects ctx

end

end Veir
