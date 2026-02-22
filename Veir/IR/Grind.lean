module

public import Veir.IR.Fields
import Veir.IR.Basic

namespace Veir

variable {opInfo : Type} [OpInfo opInfo]
variable {ctx : IRContext opInfo}

public section

attribute [local grind =] Option.maybe_def

@[grind =_]
theorem OpOperandPtr.maybe_elim (ptr : OpOperandPtr) :
    (some ptr).maybe OpOperandPtr.InBounds ctx ↔ ptr.InBounds ctx := by
  grind

@[grind =_]
theorem BlockOperandPtr.maybe_elim (ptr : BlockOperandPtr) :
    (some ptr).maybe BlockOperandPtr.InBounds ctx ↔ ptr.InBounds ctx := by
  grind

@[grind =_]
theorem BlockArgumentPtr.maybe_elim (ptr : BlockArgumentPtr) :
    (some ptr).maybe BlockArgumentPtr.InBounds ctx ↔ ptr.InBounds ctx := by
  grind

@[grind =_]
theorem OperationPtr.maybe_elim (ptr : OperationPtr) :
    (some ptr).maybe OperationPtr.InBounds ctx ↔ ptr.InBounds ctx := by
  grind

@[grind =_]
theorem BlockPtr.maybe_elim (ptr : BlockPtr) :
    (some ptr).maybe BlockPtr.InBounds ctx ↔ ptr.InBounds ctx := by
  grind

@[grind =_]
theorem RegionPtr.maybe_elim (ptr : RegionPtr) :
    (some ptr).maybe RegionPtr.InBounds ctx ↔ ptr.InBounds ctx := by
  grind

@[grind =_]
theorem OpResultPtr.maybe_elim (ptr : OpResultPtr) :
    (some ptr).maybe OpResultPtr.InBounds ctx ↔ ptr.InBounds ctx := by
  grind

@[grind =_]
theorem ValuePtr.maybe_elim (ptr : ValuePtr) :
    (some ptr).maybe ValuePtr.InBounds ctx ↔ ptr.InBounds ctx := by
  grind

@[grind =_]
theorem IRContext.maybe₁_elim (ctx : IRContext opInfo) :
    (some ctx).maybe₁ IRContext.FieldsInBounds ↔ ctx.FieldsInBounds := by
  grind [Option.maybe₁_def]
