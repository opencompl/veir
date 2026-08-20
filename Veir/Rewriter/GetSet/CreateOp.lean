module

public import Veir.Rewriter.Basic

import all Veir.Rewriter.Basic
import Veir.Rewriter.WfRewriter.GetSetTactic

import Veir.Rewriter.GetSet.Operands
import Veir.Rewriter.GetSet.BlockOperands
import Veir.Rewriter.GetSet.InsertOp
import Veir.Rewriter.GetSet.Results
import Veir.Rewriter.GetSet.Regions

public section

/-
 - The getters we consider are:
 - * BlockPtr.get! optionally replaced by the following special cases:
 -   * Block.firstUse
 -   * Block.prev
 -   * Block.next
 -   * Block.parent
 -   * Block.firstOp
 -   * Block.lastOp
 - * OperationPtr.get! optionally replaced by the following special cases:
 -   * Operation.prev
 -   * Operation.next
 -   * Operation.parent
 -   * OperationPtr.getOpType!
 -   * Operation.attrs
 - * OperationPtr.getProperties!
 - * OperationPtr.getNumResults!
 - * OpResultPtr.get!
 - * OperationPtr.getNumOperands!
 - * OpOperandPtr.get! optionally replaced by the following special case:
 - * OperationPtr.getOperands!
 - * OperationPtr.getNumSuccessors!
 - * BlockOperandPtr.get!
 - * OperationPtr.getSuccessor!
 - * OperationPtr.getSuccessors!
 - * OperationPtr.getNumRegions!
 - * OperationPtr.getRegion!
 - * BlockOperandPtrPtr.get!
 - * BlockPtr.getNumArguments!
 - * BlockArgumentPtr.get!
 - * RegionPtr.get! with optionally special cases for:
 -   * firstBlock
 -   * lastBlock
 -   * parent
 - * ValuePtr.getFirstUse!
 - * ValuePtr.getType!
 - * OpOperandPtrPtr.get!
 -/

namespace Veir

variable {OpInfo} [HasOpInfo OpInfo]
variable {ctx : IRContext OpInfo}
variable {Dialect : Type} [HasOpInfo Dialect] [HasDialect OpInfo Dialect]
variable {dialectOpType : Dialect}
variable {CreateDialect : Type} [HasOpInfo CreateDialect]
  [HasDialect OpInfo CreateDialect]
variable {opType : CreateDialect}
variable {properties : propertiesOf opType}
section Rewriter.createEmptyOp

variable {op : OperationPtr}

attribute [local grind] Rewriter.createEmptyOp

@[simp, simp_getset]
theorem BlockPtr.firstUse!_createEmptyOp {block : BlockPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    (block.get! ctx').firstUse = (block.get! ctx).firstUse := by
  grind

grind_pattern BlockPtr.firstUse!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), (block.get! ctx').firstUse

@[simp, simp_getset]
theorem BlockPtr.prev!_createEmptyOp {block : BlockPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    (block.get! ctx').prev = (block.get! ctx).prev := by
  grind

grind_pattern BlockPtr.prev!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), (block.get! ctx').prev

@[simp, simp_getset]
theorem BlockPtr.next!_createEmptyOp {block : BlockPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    (block.get! ctx').next = (block.get! ctx).next := by
  grind

grind_pattern BlockPtr.next!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), (block.get! ctx').next

@[simp, simp_getset]
theorem BlockPtr.parent!_createEmptyOp {block : BlockPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    (block.get! ctx').parent = (block.get! ctx).parent := by
  grind

grind_pattern BlockPtr.parent!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), (block.get! ctx').parent

@[simp, simp_getset]
theorem BlockPtr.firstOp!_createEmptyOp {block : BlockPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    (block.get! ctx').firstOp = (block.get! ctx).firstOp := by
  grind

grind_pattern BlockPtr.firstOp!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), (block.get! ctx').firstOp

@[simp, simp_getset]
theorem BlockPtr.lastOp!_createEmptyOp {block : BlockPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    (block.get! ctx').lastOp = (block.get! ctx).lastOp := by
  grind

grind_pattern BlockPtr.lastOp!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), (block.get! ctx').lastOp

@[simp_getset]
theorem OperationPtr.prev!_createEmptyOp {operation : OperationPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    (operation.get! ctx').prev =
    if operation = op then none else (operation.get! ctx).prev := by
  grind [Operation.empty]

grind_pattern OperationPtr.prev!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), (operation.get! ctx').prev

@[simp_getset]
theorem OperationPtr.next!_createEmptyOp {operation : OperationPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    (operation.get! ctx').next =
    if operation = op then none else (operation.get! ctx).next := by
  grind [Operation.empty]

grind_pattern OperationPtr.next!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), (operation.get! ctx').next

@[simp_getset]
theorem OperationPtr.parent!_createEmptyOp {operation : OperationPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    (operation.get! ctx').parent =
    if operation = op then none else (operation.get! ctx).parent := by
  grind [Operation.empty]

grind_pattern OperationPtr.parent!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), (operation.get! ctx').parent

@[simp_getset]
theorem OperationPtr.getOpType!_createEmptyOp {operation : OperationPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operation.getOpType! ctx' =
    if operation = op then ofDialect OpInfo opType else operation.getOpType! ctx := by
  grind [Operation.empty]

grind_pattern OperationPtr.getOpType!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operation.getOpType! ctx'

@[simp_getset]
theorem OperationPtr.attrs!_createEmptyOp {operation : OperationPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    (operation.get! ctx').attrs =
    if operation = op then DictionaryAttr.empty else (operation.get! ctx).attrs := by
  grind [Operation.empty]

grind_pattern OperationPtr.attrs!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), (operation.get! ctx').attrs

@[simp_getset]
theorem OperationPtr.getProperties!_createEmptyOp {operation : OperationPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operation.getProperties! ctx' dialectOpType =
    if operation = op then
      if h : ofDialect OpInfo opType = ofDialect OpInfo dialectOpType then
        HasDialect.properties_eq_of_ofDialect_eq h ▸ properties
      else default
    else
      operation.getProperties! ctx dialectOpType := by
  grind [Operation.empty]

grind_pattern OperationPtr.getProperties!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op),
    operation.getProperties! ctx' dialectOpType

@[simp_getset]
theorem OperationPtr.getNumResults!_createEmptyOp {operation : OperationPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operation.getNumResults! ctx' =
    if operation = op then 0 else operation.getNumResults! ctx := by
  grind [Operation.empty]

grind_pattern OperationPtr.getNumResults!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operation.getNumResults! ctx'

@[simp, simp_getset]
theorem OpResultPtr.get!_createEmptyOp {opResult : OpResultPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    opResult.get! ctx' = opResult.get! ctx := by
  grind

grind_pattern OpResultPtr.get!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), opResult.get! ctx'

@[simp_getset]
theorem OperationPtr.getNumOperands!_createEmptyOp {operation : OperationPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operation.getNumOperands! ctx' =
    if operation = op then 0 else operation.getNumOperands! ctx := by
  grind

grind_pattern OperationPtr.getNumOperands!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operation.getNumOperands! ctx'

@[simp, simp_getset]
theorem OpOperandPtr.get!_createEmptyOp {operand : OpOperandPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operand.get! ctx' = operand.get! ctx := by
  grind

grind_pattern OpOperandPtr.get!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operand.get! ctx'

@[simp_getset]
theorem OperationPtr.getOperands!_createEmptyOp {operation : OperationPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operation.getOperands! ctx' =
    if operation = op then #[] else operation.getOperands! ctx := by
  grind

grind_pattern OperationPtr.getOperands!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operation.getOperands! ctx'

@[simp_getset]
theorem OperationPtr.getNumSuccessors!_createEmptyOp {operation : OperationPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operation.getNumSuccessors! ctx' =
    if operation = op then 0 else operation.getNumSuccessors! ctx := by
  grind

grind_pattern OperationPtr.getNumSuccessors!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operation.getNumSuccessors! ctx'

@[simp, simp_getset]
theorem BlockOperandPtr.get!_createEmptyOp {operand : BlockOperandPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operand.get! ctx' = operand.get! ctx := by
  grind

grind_pattern BlockOperandPtr.get!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operand.get! ctx'

@[simp, simp_getset]
theorem OperationPtr.getSuccessor!_createEmptyOp {operation : OperationPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operation.getSuccessor! ctx' index = operation.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def]

grind_pattern OperationPtr.getSuccessor!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operation.getSuccessor! ctx' index

@[simp_getset]
theorem OperationPtr.getSuccessors!_createEmptyOp {operation : OperationPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operation.getSuccessors! ctx' =
    if operation = op then #[] else operation.getSuccessors! ctx := by
  intro h
  simp only [OperationPtr.getSuccessors!_def, OperationPtr.getSuccessor!_createEmptyOp h,
    OperationPtr.getNumSuccessors!_createEmptyOp h]
  by_cases heq : operation = op <;> simp [heq]

grind_pattern OperationPtr.getSuccessors!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operation.getSuccessors! ctx'

@[simp_getset]
theorem OperationPtr.getNumRegions!_createEmptyOp {operation : OperationPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operation.getNumRegions! ctx' =
    if operation = op then 0 else operation.getNumRegions! ctx := by
  grind

grind_pattern OperationPtr.getNumRegions!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operation.getNumRegions! ctx'

@[simp, simp_getset]
theorem OperationPtr.getRegion!_createEmptyOp {operation : OperationPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operation.getRegion! ctx' idx = operation.getRegion! ctx idx := by
  grind

grind_pattern OperationPtr.getRegion!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operation.getRegion! ctx' idx

@[simp, simp_getset]
theorem BlockOperandPtrPtr.get!_createEmptyOp {operandPtr : BlockOperandPtrPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operandPtr.get! ctx' = operandPtr.get! ctx := by
  grind

grind_pattern BlockOperandPtrPtr.get!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operandPtr.get! ctx'

@[simp, simp_getset]
theorem BlockPtr.getNumArguments!_createEmptyOp {block : BlockPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    block.getNumArguments! ctx' = block.getNumArguments! ctx := by
  grind

grind_pattern BlockPtr.getNumArguments!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), block.getNumArguments! ctx'

@[simp, simp_getset]
theorem BlockArgumentPtr.get!_createEmptyOp {blockArg : BlockArgumentPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    blockArg.get! ctx' = blockArg.get! ctx := by
  grind

grind_pattern BlockArgumentPtr.get!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), blockArg.get! ctx'

@[simp, simp_getset]
theorem RegionPtr.firstBlock!_createEmptyOp {region : RegionPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    (region.get! ctx').firstBlock = (region.get! ctx).firstBlock := by
  grind

grind_pattern RegionPtr.firstBlock!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), (region.get! ctx').firstBlock

@[simp, simp_getset]
theorem RegionPtr.lastBlock!_createEmptyOp {region : RegionPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    (region.get! ctx').lastBlock = (region.get! ctx).lastBlock := by
  grind

grind_pattern RegionPtr.lastBlock!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), (region.get! ctx').lastBlock

@[simp, simp_getset]
theorem RegionPtr.parent!_createEmptyOp {region : RegionPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    (region.get! ctx').parent = (region.get! ctx).parent := by
  grind

grind_pattern RegionPtr.parent!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), (region.get! ctx').parent

@[simp, simp_getset]
theorem ValuePtr.getFirstUse!_createEmptyOp {value : ValuePtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    value.getFirstUse! ctx' = value.getFirstUse! ctx := by
  grind

grind_pattern ValuePtr.getFirstUse!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), value.getFirstUse! ctx'

@[simp, simp_getset]
theorem ValuePtr.getType!_createEmptyOp {value : ValuePtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    value.getType! ctx' = value.getType! ctx := by
  grind

grind_pattern ValuePtr.getType!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), value.getType! ctx'

@[simp, simp_getset]
theorem OpOperandPtrPtr.get!_createEmptyOp {opOperandPtr : OpOperandPtrPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    opOperandPtr.get! ctx' = opOperandPtr.get! ctx := by
  grind

grind_pattern OpOperandPtrPtr.get!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), opOperandPtr.get! ctx'

end Rewriter.createEmptyOp

/-! ## `Rewriter.createOp` -/

section Rewriter.createOp

variable {newOp : OperationPtr}

attribute [local grind] Rewriter.createOp

/-
BlockPtr.firstUse!_createOp is too complex to be expressed, and should not be needed in practice,
as we should reason at a higher-level abstraction at this point.
-/

@[simp, grind =>, simp_getset]
theorem BlockPtr.prev!_createOp {block : BlockPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    (block.get! ctx').prev = (block.get! ctx).prev := by
  simp only [Rewriter.createOp]
  split; simp; next ctx₁ newOpPtr hCreateEmpty =>
  split; simp; next rename_i ctx₂ hInitRegions =>
  split
  next insertPoint =>
    split; simp; next ctx₃ hInsert =>
    simp only [Option.some.injEq, Prod.mk.injEq, and_imp]; intro rfl rfl
    simp_getset
  · simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
    intro rfl rfl
    simp_getset

@[simp, grind =>, simp_getset]
theorem BlockPtr.next!_createOp {block : BlockPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    (block.get! ctx').next = (block.get! ctx).next := by
  simp only [Rewriter.createOp]
  split; simp; next ctx₁ newOpPtr hCreateEmpty =>
  split; simp; next rename_i ctx₂ hInitRegions =>
  split
  next insertPoint =>
    split; simp; next ctx₃ hInsert =>
    simp only [Option.some.injEq, Prod.mk.injEq, and_imp]; intro rfl rfl
    simp_getset
  · simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
    intro rfl rfl
    simp_getset

@[simp, grind =>, simp_getset]
theorem BlockPtr.parent!_createOp {block : BlockPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    (block.get! ctx').parent = (block.get! ctx).parent := by
  simp only [Rewriter.createOp]
  split; simp; next ctx₁ newOpPtr hCreateEmpty =>
  split; simp; next rename_i ctx₂ hInitRegions =>
  split
  next insertPoint =>
    split; simp; next ctx₃ hInsert =>
    simp only [Option.some.injEq, Prod.mk.injEq, and_imp]; intro rfl rfl
    simp_getset
  · simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
    intro rfl rfl
    simp_getset

@[grind =>, simp_getset]
theorem BlockPtr.firstOp!_createOp {block : BlockPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    (block.get! ctx').firstOp =
    match insertionPoint with
    | some ip =>
      if ip.block! ctx = block ∧ ip.prev! ctx = none then some newOp
      else (block.get! ctx).firstOp
    | none => (block.get! ctx).firstOp := by
  simp only [Rewriter.createOp]
  split; simp; next ctx₁ newOpPtr hCreateEmpty =>
  split; simp; next rename_i ctx₂ hInitRegions =>
  split
  next insertPoint =>
    split; simp; next ctx₃ hInsert =>
    simp only [Option.some.injEq, Prod.mk.injEq, and_imp]; intro rfl rfl
    simp_getset
    cases insertPoint
    case before op =>
      simp only [InsertPoint.block!_before_eq, InsertPoint.prev!_before_eq]
      simp_getset
      by_cases hop : op = newOpPtr
      · subst newOpPtr
        grind
      · simp [hop]
    case atEnd block =>
      simp only [InsertPoint.block!_atEnd_eq, Option.some.injEq, InsertPoint.prev_atEnd_eq]
      grind
  · simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
    intro rfl rfl
    simp_getset

@[grind =>, simp_getset]
theorem BlockPtr.lastOp!_createOp {block : BlockPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    (block.get! ctx').lastOp =
    match insertionPoint with
    | some ip =>
      if ip.block! ctx = block ∧ ip.next = none then some newOp
      else (block.get! ctx).lastOp
    | none => (block.get! ctx).lastOp := by
  simp only [Rewriter.createOp]
  split; simp; next ctx₁ newOpPtr hCreateEmpty =>
  split; simp; next rename_i ctx₂ hInitRegions =>
  split
  next insertPoint =>
    split; simp; next ctx₃ hInsert =>
    simp only [Option.some.injEq, Prod.mk.injEq, and_imp]; intro rfl rfl
    simp_getset
    cases insertPoint
    case before op =>
      simp only [InsertPoint.block!_before_eq]
      simp_getset
      by_cases hop : op = newOpPtr
      · subst newOpPtr
        grind
      · simp [hop]
    case atEnd block => simp
  · simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
    intro rfl rfl
    simp_getset

@[grind =>, simp_getset]
theorem OperationPtr.prev!_createOp {operation : OperationPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    (operation.get! ctx').prev =
    match insertionPoint with
    | some ip =>
      if operation = newOp then ip.prev! ctx
      else if operation = ip.next then some newOp
      else (operation.get! ctx).prev
    | none =>
      if operation = newOp then none else (operation.get! ctx).prev := by
  simp only [Rewriter.createOp]
  split; simp; next ctx₁ newOpPtr hCreateEmpty =>
  split; simp; next rename_i ctx₂ hInitRegions =>
  split
  next insertPoint =>
    split; simp; next ctx₃ hInsert =>
    simp only [Option.some.injEq, Prod.mk.injEq, and_imp]; intro rfl rfl
    simp_getset
    cases insertPoint
    case before op =>
      simp only [InsertPoint.next_before_eq, Option.some.injEq, InsertPoint.prev!_before_eq]
      simp_getset
      by_cases hop : op = newOpPtr; grind
      simp only [hop, ↓reduceIte]
      by_cases hop' : operation = op; simp_all
      simp only [hop', ↓reduceIte]
      by_cases hop'' : operation = newOpPtr <;> simp_all
    case atEnd block =>
      simp only [InsertPoint.next_atEnd_eq, reduceCtorEq, ↓reduceIte, InsertPoint.prev_atEnd_eq,
        BlockPtr.lastOp!_initBlockOperands, BlockPtr.lastOp!_initOpOperands]
      by_cases hop : operation = newOpPtr <;> simp_all
      simp_getset
  · simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
    intro rfl rfl
    simp_getset

@[grind =>, simp_getset]
theorem OperationPtr.next!_createOp {operation : OperationPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    (operation.get! ctx').next =
    match insertionPoint with
    | some ip =>
      if operation = newOp then ip.next
      else if operation = ip.prev! ctx then some newOp
      else (operation.get! ctx).next
    | none =>
      if operation = newOp then none else (operation.get! ctx).next := by
  simp only [Rewriter.createOp]
  split; simp; next ctx₁ newOpPtr hCreateEmpty =>
  split; simp; next rename_i ctx₂ hInitRegions =>
  split
  next insertPoint =>
    split; simp; next ctx₃ hInsert =>
    simp only [Option.some.injEq, Prod.mk.injEq, and_imp]; intro rfl rfl
    simp_getset
    cases insertPoint
    case before op =>
      simp only [InsertPoint.prev!_before_eq, prev!_initBlockOperands, prev!_initOpOperands,
        InsertPoint.next_before_eq]
      simp_getset
      by_cases hop : op = newOpPtr
      · subst newOpPtr
        simp only [↓reduceIte, reduceCtorEq]
        by_cases hop' : operation = op; simp [hop', ↓reduceIte]
        simp only [hop', ↓reduceIte, right_eq_ite_iff]
        grind
      · simp only [hop, ↓reduceIte]
        by_cases hop' : some operation = (op.get! ctx).prev
        · simp only [hop', ↓reduceIte, right_eq_ite_iff, Option.some.injEq]
          grind
        · simp only [hop', ↓reduceIte]
          by_cases hop'' : operation = newOpPtr <;> simp_all
    case atEnd block =>
      simp only [InsertPoint.prev_atEnd_eq, BlockPtr.lastOp!_initBlockOperands,
        BlockPtr.lastOp!_initOpOperands, InsertPoint.next_atEnd_eq]
      by_cases hop : some operation = (block.get! ctx₂).lastOp; grind
      simp only [hop, ↓reduceIte]
      by_cases hop' : operation = newOpPtr; simp_all
      simp only [hop', ↓reduceIte, right_eq_ite_iff]
      grind
  · simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
    intro rfl rfl
    simp_getset

@[grind =>, simp_getset]
theorem OperationPtr.parent!_createOp {operation : OperationPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    (operation.get! ctx').parent =
    if operation = newOp then
      match insertionPoint with
      | some ip => ip.block! ctx
      | none => none
    else (operation.get! ctx).parent := by
  simp only [Rewriter.createOp]
  split; simp; next ctx₁ newOpPtr hCreateEmpty =>
  split; simp; next rename_i ctx₂ hInitRegions =>
  split
  next insertPoint =>
    split; simp; next ctx₃ hInsert =>
    simp only [Option.some.injEq, Prod.mk.injEq, and_imp]; intro rfl rfl
    simp_getset
    cases insertPoint
    case before op =>
      simp only [InsertPoint.block!_before_eq, parent!_initBlockOperands, parent!_initOpOperands]
      simp_getset
      by_cases hop : operation = newOpPtr
      · simp only [hop, ↓reduceIte, ite_eq_right_iff]
        grind
      · simp only [hop, ↓reduceIte]
    case atEnd block =>
      simp only [InsertPoint.block!_atEnd_eq]
      by_cases hop : operation = newOpPtr <;> simp [hop]
  · simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
    intro rfl rfl
    simp_getset

@[grind =>, simp_getset]
theorem OperationPtr.getOpType!_createOp {operation : OperationPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    operation.getOpType! ctx' =
    if operation = newOp then ofDialect OpInfo opType else operation.getOpType! ctx := by
  simp only [Rewriter.createOp]
  split; simp; next ctx₁ newOpPtr hCreateEmpty =>
  split; simp; next rename_i ctx₂ hInitRegions =>
  split
  next insertPoint =>
    split; simp; next ctx₃ hInsert =>
    simp only [Option.some.injEq, Prod.mk.injEq, and_imp]; intro rfl rfl
    simp_getset
  · simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
    intro rfl rfl
    simp_getset

@[grind =>, simp_getset]
theorem OperationPtr.attrs!_createOp {operation : OperationPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    (operation.get! ctx').attrs =
    if operation = newOp then DictionaryAttr.empty else (operation.get! ctx).attrs := by
  simp only [Rewriter.createOp]
  split; simp; next ctx₁ newOpPtr hCreateEmpty =>
  split; simp; next rename_i ctx₂ hInitRegions =>
  split
  next insertPoint =>
    split; simp; next ctx₃ hInsert =>
    simp only [Option.some.injEq, Prod.mk.injEq, and_imp]; intro rfl rfl
    simp_getset
  · simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
    intro rfl rfl
    simp_getset

@[grind =>, simp_getset]
theorem OperationPtr.getProperties!_createOp {operation : OperationPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    operation.getProperties! ctx' dialectOpType =
    if operation = newOp then
      if h : ofDialect OpInfo opType = ofDialect OpInfo dialectOpType then
        HasDialect.properties_eq_of_ofDialect_eq h ▸ properties
      else default
    else
      operation.getProperties! ctx dialectOpType := by
  simp only [Rewriter.createOp]
  split; simp; next ctx₁ newOpPtr hCreateEmpty =>
  split; simp; next rename_i ctx₂ hInitRegions =>
  split
  next insertPoint =>
    split; simp; next ctx₃ hInsert =>
    simp only [Option.some.injEq, Prod.mk.injEq, and_imp]; intro rfl rfl
    simp_getset
  · simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
    intro rfl rfl
    simp_getset

@[grind =>, simp_getset]
theorem OperationPtr.getNumResults!_createOp {operation : OperationPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    operation.getNumResults! ctx' =
    if operation = newOp then resultTypes.size else operation.getNumResults! ctx := by
  simp only [Rewriter.createOp]
  split; simp; next ctx₁ newOpPtr hCreateEmpty =>
  split; simp; next rename_i ctx₂ hInitRegions =>
  split
  next insertPoint =>
    split; simp; next ctx₃ hInsert =>
    simp only [Option.some.injEq, Prod.mk.injEq, and_imp]; intro rfl rfl
    simp_getset
    by_cases hop : operation = newOpPtr <;> simp [hop]
  · simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
    intro rfl rfl
    simp_getset
    by_cases hop : operation = newOpPtr <;> simp [hop]

/-
OpResultPtr.get!_createOp is too complex to be expressed, and should not be needed in practice,
as we should reason at a higher-level abstraction at this point.
-/

@[grind =>, simp_getset]
theorem OperationPtr.getNumOperands!_createOp {operation : OperationPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    operation.getNumOperands! ctx' =
    if operation = newOp then operands.size else operation.getNumOperands! ctx := by
  simp only [Rewriter.createOp]
  split; simp; next ctx₁ newOpPtr hCreateEmpty =>
  split; simp; next rename_i ctx₂ hInitRegions =>
  split
  next insertPoint =>
    split; simp; next ctx₃ hInsert =>
    simp only [Option.some.injEq, Prod.mk.injEq, and_imp]; intro rfl rfl
    simp_getset
    by_cases hop : operation = newOpPtr <;> simp [hop]
  · simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
    intro rfl rfl
    simp_getset
    by_cases hop : operation = newOpPtr <;> simp [hop]

/-
OpOperandPtr.get!_createOp is too complex to be expressed, and should not be needed in practice,
as we should reason at a higher-level abstraction at this point.
-/

@[grind =>, simp_getset]
theorem OperationPtr.getOperands!_createOp {operation : OperationPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    operation.getOperands! ctx' =
    if operation = newOp then operands else operation.getOperands! ctx := by
  simp only [Rewriter.createOp]
  split; simp; next ctx₁ newOpPtr hCreateEmpty =>
  split; simp; next rename_i ctx₂ hInitRegions =>
  split
  next insertPoint =>
    split; simp; next ctx₃ hInsert =>
    simp only [Option.some.injEq, Prod.mk.injEq, and_imp]; intro rfl rfl
    simp_getset
    by_cases hop : operation = newOpPtr <;> simp [hop]
  · simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
    intro rfl rfl
    simp_getset
    by_cases hop : operation = newOpPtr <;> simp [hop]

@[grind =>, simp_getset]
theorem OperationPtr.getNumSuccessors!_createOp {operation : OperationPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    operation.getNumSuccessors! ctx' =
    if operation = newOp then blockOperands.size else operation.getNumSuccessors! ctx := by
  simp only [Rewriter.createOp]
  split; simp; next ctx₁ newOpPtr hCreateEmpty =>
  split; simp; next rename_i ctx₂ hInitRegions =>
  split
  next insertPoint =>
    split; simp; next ctx₃ hInsert =>
    simp only [Option.some.injEq, Prod.mk.injEq, and_imp]; intro rfl rfl
    simp_getset
    by_cases hop : operation = newOpPtr <;> simp [hop]
  · simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
    intro rfl rfl
    simp_getset
    by_cases hop : operation = newOpPtr <;> simp [hop]

/-
BlockOperandPtr.get!_createOp is too complex to be expressed, and should not be needed in practice,
as we should reason at a higher-level abstraction at this point.
-/

@[grind =>, simp_getset]
theorem OperationPtr.getSuccessor!_createOp {operation : OperationPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    operation.getSuccessor! ctx' index =
    if operation = newOp then blockOperands[index]!
    else operation.getSuccessor! ctx index := by
  simp only [Rewriter.createOp]
  split; simp; next ctx₁ newOpPtr hCreateEmpty =>
  split; simp; next rename_i ctx₂ hInitRegions =>
  split
  next insertPoint =>
    split; simp; next ctx₃ hInsert =>
    simp only [Option.some.injEq, Prod.mk.injEq, and_imp]; intro rfl rfl
    simp_getset
    by_cases hop : operation = newOpPtr <;> simp [hop]
  · simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
    intro rfl rfl
    simp_getset
    by_cases hop : operation = newOpPtr <;> simp [hop]

@[grind =>, simp_getset]
theorem OperationPtr.getSuccessors!_createOp {operation : OperationPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    operation.getSuccessors! ctx' =
    if operation = newOp then blockOperands else operation.getSuccessors! ctx := by
  simp only [Rewriter.createOp]
  split; simp; next ctx₁ newOpPtr hCreateEmpty =>
  split; simp; next rename_i ctx₂ hInitRegions =>
  split
  next insertPoint =>
    split; simp; next ctx₃ hInsert =>
    simp only [Option.some.injEq, Prod.mk.injEq, and_imp]; intro rfl rfl
    simp_getset
    by_cases hop : operation = newOpPtr <;> simp [hop]
  · simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
    intro rfl rfl
    simp_getset
    by_cases hop : operation = newOpPtr <;> simp [hop]

@[grind =>, simp_getset]
theorem OperationPtr.getNumRegions!_createOp {operation : OperationPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    operation.getNumRegions! ctx' =
    if operation = newOp then regions.size else operation.getNumRegions! ctx := by
  simp only [Rewriter.createOp]
  split; simp; next ctx₁ newOpPtr hCreateEmpty =>
  split; simp; next rename_i ctx₂ hInitRegions =>
  split
  next insertPoint =>
    split; simp; next ctx₃ hInsert =>
    simp only [Option.some.injEq, Prod.mk.injEq, and_imp]; intro rfl rfl
    simp_getset
    by_cases hop : operation = newOpPtr; rotate_left; simp [hop]
    subst newOpPtr; simp only [↓reduceIte, Nat.zero_add]
    rw [← OperationPtr.getNumRegions!_eq_getNumRegions (by grind)]
    simp_getset
    simp
  · simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
    intro rfl rfl
    simp_getset
    by_cases hop : operation = newOpPtr; rotate_left; simp [hop]
    rw [← OperationPtr.getNumRegions!_eq_getNumRegions (by grind)]
    simp only [hop, ↓reduceIte, getNumRegions!_initOpResults, Nat.zero_add]
    simp_getset
    simp

@[grind =>, simp_getset]
theorem OperationPtr.getRegion!_createOp {operation : OperationPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    operation.getRegion! ctx' idx =
    if _ : operation = newOp ∧ idx < regions.size then regions[idx]
    else operation.getRegion! ctx idx := by
  simp only [Rewriter.createOp]
  split; simp; next ctx₁ newOpPtr hCreateEmpty =>
  split; simp; next rename_i ctx₂ hInitRegions =>
  split
  next insertPoint =>
    split; simp; next ctx₃ hInsert =>
    simp only [Option.some.injEq, Prod.mk.injEq, and_imp]; intro rfl rfl
    simp_getset
    by_cases hop : operation = newOpPtr <;> simp [hop]
  · simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
    intro rfl rfl
    simp_getset
    by_cases hop : operation = newOpPtr <;> simp [hop]

/-
BlockOperandPtrPtr.get!_createOp is too complex to be expressed, and should not be needed in practice,
as we should reason at a higher-level abstraction at this point.
-/

@[simp, grind =>, simp_getset]
theorem BlockPtr.getNumArguments!_createOp {block : BlockPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    block.getNumArguments! ctx' = block.getNumArguments! ctx := by
  simp only [Rewriter.createOp]
  split; simp; next ctx₁ newOpPtr hCreateEmpty =>
  split; simp; next rename_i ctx₂ hInitRegions =>
  split
  next insertPoint =>
    split; simp; next ctx₃ hInsert =>
    simp only [Option.some.injEq, Prod.mk.injEq, and_imp]; intro rfl rfl
    simp_getset
  · simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
    intro rfl rfl
    simp_getset

/-
BlockArgumentPtr.get!_createOp is too complex to be expressed, and should not be needed in practice,
as we should reason at a higher-level abstraction at this point.
-/

@[simp, grind =>, simp_getset]
theorem RegionPtr.firstBlock!_createOp {region : RegionPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    (region.get! ctx').firstBlock = (region.get! ctx).firstBlock := by
  simp only [Rewriter.createOp]
  split; simp; next ctx₁ newOpPtr hCreateEmpty =>
  split; simp; next rename_i ctx₂ hInitRegions =>
  split
  next insertPoint =>
    split; simp; next ctx₃ hInsert =>
    simp only [Option.some.injEq, Prod.mk.injEq, and_imp]; intro rfl rfl
    simp_getset
  · simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
    intro rfl rfl
    simp_getset

@[simp, grind =>, simp_getset]
theorem RegionPtr.lastBlock!_createOp {region : RegionPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    (region.get! ctx').lastBlock = (region.get! ctx).lastBlock := by
  simp only [Rewriter.createOp]
  split; simp; next ctx₁ newOpPtr hCreateEmpty =>
  split; simp; next rename_i ctx₂ hInitRegions =>
  split
  next insertPoint =>
    split; simp; next ctx₃ hInsert =>
    simp only [Option.some.injEq, Prod.mk.injEq, and_imp]; intro rfl rfl
    simp_getset
  · simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
    intro rfl rfl
    simp_getset

@[simp, grind =>, simp_getset]
theorem RegionPtr.parent!_createOp {region : RegionPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    (region.get! ctx').parent =
    if region ∈ regions then some newOp else (region.get! ctx).parent := by
  simp only [Rewriter.createOp]
  split; simp; next ctx₁ newOpPtr hCreateEmpty =>
  split; simp; next rename_i ctx₂ hInitRegions =>
  split
  next insertPoint =>
    split; simp; next ctx₃ hInsert =>
    simp only [Option.some.injEq, Prod.mk.injEq, and_imp]; intro rfl rfl
    simp_getset
    rw [←OperationPtr.getNumRegions!_eq_getNumRegions (by grind)]
    simp_getset
    simp only [↓reduceIte, Nat.zero_le, true_and]
    congr
    have := Array.exists_mem_iff_exists_getElem (xs := regions) (P := fun r => r = region)
    simp only [exists_eq_right] at this
    simp [this]
  · simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
    intro rfl rfl
    simp_getset
    rw [←OperationPtr.getNumRegions!_eq_getNumRegions (by grind)]
    simp_getset
    simp only [↓reduceIte, Nat.zero_le, true_and]
    congr
    have := Array.exists_mem_iff_exists_getElem (xs := regions) (P := fun r => r = region)
    simp only [exists_eq_right] at this
    simp [this]

/-
ValuePtr.getFirstUse!_createOp is too complex to be expressed, and should not be needed in practice,
as we should reason at a higher-level abstraction at this point.
-/

@[grind =>, simp_getset]
theorem ValuePtr.getType!_createOp {value : ValuePtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    value.getType! ctx' =
    match value with
    | .opResult opRes =>
      if _ : opRes.op = newOp ∧ opRes.index < resultTypes.size then
        resultTypes[opRes.index]
      else value.getType! ctx
    | .blockArgument _ => value.getType! ctx := by
  simp only [Rewriter.createOp]
  split; simp; next ctx₁ newOpPtr hCreateEmpty =>
  split; simp; next rename_i ctx₂ hInitRegions =>
  split
  next insertPoint =>
    split; simp; next ctx₃ hInsert =>
    simp only [Option.some.injEq, Prod.mk.injEq, and_imp]; intro rfl rfl
    simp_getset
    simp only [↓reduceIte, Nat.zero_le, and_true]
    cases value <;> simp
  next =>
    simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
    intro rfl rfl
    simp_getset
    cases value <;> simp

/-
OpOperandPtrPtr.get!_createOp is too complex to be expressed, and should not be needed in practice,
as we should reason at a higher-level abstraction at this point.
-/

end Rewriter.createOp

/- replaceValue? -/

@[simp, grind ., simp_getset]
theorem OperationPtr.getNumOperands_iff_replaceValue?
    (hctx' : Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some ctx') :
    OperationPtr.getNumOperands op ctx' h_op =
    OperationPtr.getNumOperands op ctx (by grind) := by
  grind [OpOperandPtr.inBounds_if_operand_size_eq]

/--
`createOp` allocates a new operation with its results, operands, and block operands. Thus, the
only new pointers that are in bounds in the new context and not in the old one are the operation
itself, its results, its operands, its block operands, and the links to them.
-/
@[grind =>, simp_getset]
theorem Rewriter.createOp_inBounds (ptr : GenericPtr)
    (h : createOp ctx opType resultTypes operands blockOperands regions props ip h₁ h₂ h₃ h₄ h₅ = some (newCtx, newOp)) :
    ptr.InBounds newCtx ↔
    match ptr with
    | .opResult resPtr
    | .value (.opResult resPtr)
    | .opOperandPtr (.valueFirstUse (.opResult resPtr)) =>
      if resPtr.op = newOp then resPtr.index < resultTypes.size else resPtr.InBounds ctx
    | .opOperand operandPtr
    | .opOperandPtr (.operandNextUse operandPtr) =>
      if operandPtr.op = newOp then operandPtr.index < operands.size else operandPtr.InBounds ctx
    | .blockOperand blockOperandPtr
    | .blockOperandPtr (.blockOperandNextUse blockOperandPtr) =>
      if blockOperandPtr.op = newOp then
        blockOperandPtr.index < blockOperands.size
      else
        blockOperandPtr.InBounds ctx
    | _ => ptr.InBounds ctx ∨ ptr = .operation newOp := by
  simp only [createOp] at h
  split at h; simp at h
  rename_i ctx₁ newOpPtr hnew
  split at h; simp at h
  rename_i ctx₂ hreg
  split at h
  · split at h; simp at h; rename_i ctx₂ hctx₂
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h₁, h₂⟩ := h
    subst h₁ h₂
    simp only [insertOp_inBounds_mono _ hctx₂, Rewriter.initBlockOperands_inBounds]
    simp_getset
    simp only [↓reduceIte, Nat.zero_add]
    cases ptr <;> simp only [← initOpRegions_inBounds hreg, initOpResults_inBounds,
        Rewriter.createEmptyOp_genericPtr_mono _ hnew]
    case opResult => simp_getset; simp
    case opOperand => simp
    case blockOperand => simp
    case blockOperandPtr opPtr => cases opPtr <;> simp
    case value ptr =>
      cases ptr
      · simp_getset; simp
      · simp
    case opOperandPtr opPtr =>
      rcases opPtr with _ | ⟨_ | _⟩
      · simp
      · simp_getset; simp
      · simp
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h₁, h₂⟩ := h
    subst h₁ h₂
    simp only [Rewriter.initBlockOperands_inBounds]
    simp_getset
    simp only [↓reduceIte, Nat.zero_add]
    cases ptr <;> simp only [← initOpRegions_inBounds hreg, initOpResults_inBounds,
        Rewriter.createEmptyOp_genericPtr_mono _ hnew]
    case opResult => simp_getset; simp
    case opOperand => simp
    case blockOperand => simp
    case blockOperandPtr opPtr => cases opPtr <;> simp
    case value ptr =>
      cases ptr
      · simp_getset; simp
      · simp
    case opOperandPtr opPtr =>
      rcases opPtr with _ | ⟨_ | _⟩
      · simp
      · simp_getset; simp
      · simp

end Veir
