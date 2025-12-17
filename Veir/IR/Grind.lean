module

public import Veir.IR.Fields
import all Veir.IR.Basic

namespace Mlir

public section

namespace OpResult.FieldsInBounds
attribute [grind .] firstUse_inBounds owner_inBounds
end OpResult.FieldsInBounds

namespace BlockArgument.FieldsInBounds
attribute [grind .] firstUse_inBounds owner_inBounds
end BlockArgument.FieldsInBounds

namespace OpOperand.FieldsInBounds
attribute [grind .] nextUse_inBounds back_inBounds owner_inBounds value_inBounds
end OpOperand.FieldsInBounds

namespace BlockOperand.FieldsInBounds
attribute [grind .] nextUse_inBounds back_inBounds owner_inBounds value_inBounds
end BlockOperand.FieldsInBounds

namespace Operation.FieldsInBounds
attribute [grind .]
  results_inBounds prev_inBounds next_inBounds parent_inBounds
  blockOperands_inBounds regions_inBounds operands_inBounds
end Operation.FieldsInBounds

namespace Block.FieldsInBounds
attribute [grind .]
  firstUse_inBounds prev_inBounds next_inBounds parent_inBounds firstOp_inBounds
  lastOp_inBounds arguments_inBounds
end Block.FieldsInBounds

namespace Region.FieldsInBounds
attribute [grind .] firstBlock_inBounds lastBlock_inBounds parent_inBounds
end Region.FieldsInBounds

namespace IRContext.FieldsInBounds
attribute [grind .] topLevelOp_inBounds operations_inBounds blocks_inBounds regions_inBounds
end IRContext.FieldsInBounds


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
theorem IRContext.maybe₁_elim (ctx : IRContext) :
    (some ctx).maybe₁ IRContext.FieldsInBounds ↔ ctx.FieldsInBounds := by
  grind [Option.maybe₁_def]
