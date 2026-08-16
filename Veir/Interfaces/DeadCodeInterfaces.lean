module

public import Veir.Interfaces.SideEffectInterfaces
public import Veir.GlobalOpInfo

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

TODO: this is specialised to `OpCode` only because the terminator query lives
on `OpCode` rather than on `HasOpInfo`. Moving it into the class would let this
go back to being generic over any operation-info type.
-/
abbrev OperationPtr.isTriviallyDead
    (op : OperationPtr) (ctx : IRContext OpCode) : Prop :=
  op.getNumRegions! ctx = 0
    ∧ !op.hasUses! ctx
    ∧ !(op.getEffects ctx).writes
    ∧ !(op.getOpType! ctx).isTerminator

end

end Veir
