import Veir.Rewriter.Basic
import Veir.Rewriter.LinkedList.GetSet
import Veir.ForLean

/-
 - The getters we consider are:
 - * IRContext.topLevelOp
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
 -   * Operation.opType
 -   * Operation.attrs
 -   * Operation.properties
 - * OperationPtr.getNumResults!
 - * OpResultPtr.get!
 - * OperationPtr.getNumOperands!
 - * OpOperandPtr.get! optionally replaced by the following special case:
 - * OperationPtr.getNumSuccessors!
 - * BlockOperandPtr.get!
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

section Rewriter.insertOp?

unseal Rewriter.insertOp?

attribute [local grind] Rewriter.insertOp?

@[grind .]
theorem Rewriter.insertOp?_inBounds_mono (ptr : GenericPtr)
    (heq : insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx) :
    ptr.InBounds ctx ↔ ptr.InBounds newCtx := by
  simp only [insertOp?] at heq
  grind

@[grind .]
theorem Rewriter.insertOp?_fieldsInBounds_mono
    (heq : insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx) :
    ctx.FieldsInBounds → newCtx.FieldsInBounds := by
  simp only [insertOp?] at heq
  grind

@[simp]
theorem IRContext.topLevelOp_insertOp? :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    newCtx.topLevelOp = ctx.topLevelOp := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern IRContext.topLevelOp_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, newCtx.topLevelOp

@[simp]
theorem BlockPtr.firstUse!_insertOp? {block : BlockPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    (block.get! newCtx).firstUse = (block.get! ctx).firstUse := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern BlockPtr.firstUse!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, (block.get! newCtx).firstUse

@[simp]
theorem BlockPtr.prev!_insertOp? {block : BlockPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    (block.get! newCtx).prev = (block.get! ctx).prev := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern BlockPtr.prev!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, (block.get! newCtx).prev

@[simp]
theorem BlockPtr.next!_insertOp? {block : BlockPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    (block.get! newCtx).next = (block.get! ctx).next := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern BlockPtr.next!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, (block.get! newCtx).next

@[simp]
theorem BlockPtr.parent!_insertOp? {block : BlockPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    (block.get! newCtx).parent = (block.get! ctx).parent := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern BlockPtr.parent!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, (block.get! newCtx).parent

theorem BlockPtr.firstOp!_insertOp? {block : BlockPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    (block.get! newCtx).firstOp =
    if ip.block! ctx = block ∧ ip.prev! ctx = none then
      some newOp
    else
      (block.get! ctx).firstOp := by
  simp only [Rewriter.insertOp?]
  split
  · split
    · grind
    · grind [InsertPoint.block!, InsertPoint.prev!]
  · grind [InsertPoint.block!, InsertPoint.prev!]

grind_pattern BlockPtr.firstOp!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, (block.get! newCtx).firstOp

theorem BlockPtr.lastOp!_insertOp? {block : BlockPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    (block.get! newCtx).lastOp =
    if ip.block! ctx = block ∧ ip.next = none then
      some newOp
    else
      (block.get! ctx).lastOp := by
  simp only [Rewriter.insertOp?]
  grind (splits := 20)

grind_pattern BlockPtr.lastOp!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, (block.get! newCtx).lastOp

theorem OperationPtr.prev!_insertOp? {operation : OperationPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    (operation.get! newCtx).prev =
    if operation = ip.next then
      some newOp
    else if operation = newOp then
      ip.prev! ctx
    else
      (operation.get! ctx).prev := by
  simp only [Rewriter.insertOp?]
  grind [InsertPoint.next, InsertPoint.prev!]

grind_pattern OperationPtr.prev!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, (operation.get! newCtx).prev

theorem OperationPtr.next!_insertOp? {operation : OperationPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    (operation.get! newCtx).next =
    if operation = ip.prev! ctx then
      some newOp
    else if operation = newOp then
      ip.next
    else
      (operation.get! ctx).next := by
  simp only [Rewriter.insertOp?]
  grind [InsertPoint.next, InsertPoint.prev!]

grind_pattern OperationPtr.next!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, (operation.get! newCtx).next

theorem OperationPtr.parent!_insertOp? {operation : OperationPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    (operation.get! newCtx).parent =
    if operation = newOp then
      ip.block! ctx
    else
      (operation.get! ctx).parent := by
  simp only [Rewriter.insertOp?]
  grind (gen := 10)

grind_pattern OperationPtr.parent!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, (operation.get! newCtx).parent

@[simp]
theorem OperationPtr.opType!_insertOp? {operation : OperationPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    (operation.get! newCtx).opType = (operation.get! ctx).opType := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern OperationPtr.opType!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, (operation.get! newCtx).opType

@[simp]
theorem OperationPtr.attrs!_insertOp? {operation : OperationPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    (operation.get! newCtx).attrs = (operation.get! ctx).attrs := by
  grind

grind_pattern OperationPtr.attrs!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, (operation.get! newCtx).attrs

@[simp]
theorem OperationPtr.properties!_insertOp? {operation : OperationPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    (operation.get! newCtx).properties = (operation.get! ctx).properties := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern OperationPtr.properties!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, (operation.get! newCtx).properties

@[simp]
theorem OperationPtr.getNumResults!_insertOp? {operation : OperationPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operation.getNumResults! newCtx = operation.getNumResults! ctx := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern OperationPtr.getNumResults!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, operation.getNumResults! newCtx

@[simp]
theorem OpResultPtr.get!_insertOp? {opResult : OpResultPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    opResult.get! newCtx = opResult.get! ctx := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern OpResultPtr.get!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, opResult.get! newCtx

@[simp]
theorem OperationPtr.getNumOperands!_insertOp? {operation : OperationPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operation.getNumOperands! newCtx = operation.getNumOperands! ctx := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern OperationPtr.getNumOperands!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, operation.getNumOperands! newCtx

@[simp]
theorem OpOperandPtr.get!_insertOp? {operand : OpOperandPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operand.get! newCtx = operand.get! ctx := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern OpOperandPtr.get!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, operand.get! newCtx

@[simp]
theorem OperationPtr.getNumSuccessors!_insertOp? {operation : OperationPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operation.getNumSuccessors! newCtx = operation.getNumSuccessors! ctx := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern OperationPtr.getNumSuccessors!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, operation.getNumSuccessors! newCtx

@[simp]
theorem BlockOperandPtr.get!_insertOp? {operand : BlockOperandPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operand.get! newCtx = operand.get! ctx := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern BlockOperandPtr.get!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, operand.get! newCtx

@[simp]
theorem OperationPtr.getNumRegions!_insertOp? {operation : OperationPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operation.getNumRegions! newCtx = operation.getNumRegions! ctx := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern OperationPtr.getNumRegions!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, operation.getNumRegions! newCtx

@[simp]
theorem OperationPtr.getRegion!_insertOp? {operation : OperationPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operation.getRegion! newCtx = operation.getRegion! ctx := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern OperationPtr.getRegion!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, operation.getRegion! newCtx

@[simp]
theorem BlockOperandPtrPtr.get!_insertOp? {operandPtr : BlockOperandPtrPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operandPtr.get! newCtx = operandPtr.get! ctx := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern BlockOperandPtrPtr.get!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, operandPtr.get! newCtx

@[simp]
theorem BlockPtr.getNumArguments!_insertOp? {block : BlockPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    block.getNumArguments! newCtx = block.getNumArguments! ctx := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern BlockPtr.getNumArguments!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, block.getNumArguments! newCtx

@[simp]
theorem BlockArgumentPtr.get!_insertOp? {blockArg : BlockArgumentPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    blockArg.get! newCtx = blockArg.get! ctx := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern BlockArgumentPtr.get!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, blockArg.get! newCtx

@[simp]
theorem RegionPtr.get!_insertOp? {region : RegionPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    region.get! newCtx = region.get! ctx := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern RegionPtr.get!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, region.get! newCtx

@[simp]
theorem ValuePtr.getFirstUse!_insertOp? {value : ValuePtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    value.getFirstUse! newCtx = value.getFirstUse! ctx := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern ValuePtr.getFirstUse!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, value.getFirstUse! newCtx

theorem ValuePtr.getType!_insertOp? {value : ValuePtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    value.getType! newCtx = value.getType! ctx := by
  grind

grind_pattern ValuePtr.getType!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, value.getType! newCtx

@[simp]
theorem OpOperandPtrPtr.get!_insertOp? {opOperandPtr : OpOperandPtrPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    opOperandPtr.get! newCtx = opOperandPtr.get! ctx := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern OpOperandPtrPtr.get!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, opOperandPtr.get! newCtx

end Rewriter.insertOp?

section Rewriter.detachOp

variable {op : OperationPtr}

attribute [local grind] Rewriter.detachOp

@[simp, grind =]
theorem IRContext.topLevelOp_detachOp :
    (Rewriter.detachOp ctx op' h₁ h₂ h₃).topLevelOp =
    ctx.topLevelOp := by
  grind

@[simp, grind =]
theorem BlockPtr.firstUse!_detachOp {block : BlockPtr} :
    (block.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃)).firstUse = (block.get! ctx).firstUse := by
  grind

@[simp, grind =]
theorem BlockPtr.prev!_detachOp {block : BlockPtr} :
    (block.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃)).prev = (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_detachOp {block : BlockPtr} :
    (block.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃)).next = (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_detachOp {block : BlockPtr} :
    (block.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃)).parent = (block.get! ctx).parent := by
  grind

@[grind =]
theorem BlockPtr.firstOp!_detachOp {block : BlockPtr} :
    (block.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃)).firstOp =
    if (op'.get! ctx).prev = none ∧ block = (op'.get! ctx).parent then
      (op'.get! ctx).next
    else
      (block.get! ctx).firstOp := by
  grind

@[grind =]
theorem BlockPtr.lastOp!_detachOp {block : BlockPtr} :
    (block.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃)).lastOp =
    if (op'.get! ctx).next = none ∧ block = (op'.get! ctx).parent then
      (op'.get! ctx).prev
    else
      (block.get! ctx).lastOp := by
  grind

@[grind =]
theorem OperationPtr.prev!_detachOp {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃)).prev =
    if operation = (op'.get! ctx).next then
      (op'.get! ctx).prev
    else
      (operation.get! ctx).prev := by
  grind

@[grind =]
theorem OperationPtr.next!_detachOp {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃)).next =
    if operation = (op'.get! ctx).prev then
      (op'.get! ctx).next
    else
      (operation.get! ctx).next := by
  grind

@[grind =]
theorem OperationPtr.parent!_detachOp {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃)).parent =
    if operation = op' then none else (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_detachOp {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃)).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_detachOp {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃)).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.properties!_detachOp {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃)).properties =
    (operation.get! ctx).properties := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_detachOp {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_detachOp {opResult : OpResultPtr} :
    opResult.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_detachOp {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.detachOp ctx op' h₁ h₂ h₃) = operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_detachOp {opOperand : OpOperandPtr} :
    opOperand.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃) = opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_detachOp {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_detachOp {blockOperand : BlockOperandPtr} :
    blockOperand.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_detachOp {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_detachOp {operation : OperationPtr} :
    operation.getRegion! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    operation.getRegion! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_detachOp {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_detachOp {block : BlockPtr} :
    block.getNumArguments! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_detachOp {blockArg : BlockArgumentPtr} :
    blockArg.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_detachOp {region : RegionPtr} :
    region.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_detachOp {value : ValuePtr} :
    value.getFirstUse! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_detachOp {value : ValuePtr} :
    value.getType! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_detachOp {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃) = opOperandPtr.get! ctx := by
  grind

end Rewriter.detachOp

section Rewriter.insertBlock?

unseal Rewriter.insertBlock?

attribute [local grind] Rewriter.insertBlock?


@[grind .]
theorem Rewriter.insertBlock?_inBounds_mono (ptr : GenericPtr)
    (heq : insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx) :
    ptr.InBounds ctx ↔ ptr.InBounds newCtx := by
  simp only [insertBlock?] at heq
  grind

@[grind .]
theorem Rewriter.insertBlock?_fieldsInBounds_mono
    (heq : insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx) :
    ctx.FieldsInBounds → newCtx.FieldsInBounds := by
  simp only [insertBlock?] at heq
  grind

@[simp]
theorem IRContext.topLevelOp_insertBlock? :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    newCtx.topLevelOp = ctx.topLevelOp := by
  simp only [Rewriter.insertBlock?]
  split
  · grind
  · grind

grind_pattern IRContext.topLevelOp_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, newCtx.topLevelOp

@[simp]
theorem BlockPtr.firstUse!_insertBlock? {block : BlockPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    (block.get! newCtx).firstUse = (block.get! ctx).firstUse := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern BlockPtr.firstUse!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, (block.get! newCtx).firstUse

theorem BlockPtr.prev!_insertBlock? {block : BlockPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    (block.get! newCtx).prev =
      if block = ip.next then
        some newBlock
      else if block = newBlock then
        ip.prev! ctx
      else
        (block.get! ctx).prev := by
  simp only [Rewriter.insertBlock?]
  grind [BlockInsertPoint.next, BlockInsertPoint.prev!]

grind_pattern BlockPtr.prev!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, (block.get! newCtx).prev

theorem BlockPtr.next!_insertBlock? {block : BlockPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    (block.get! newCtx).next =
      if block = ip.prev! ctx then
        some newBlock
      else if block = newBlock then
        ip.next
      else
        (block.get! ctx).next := by
  simp only [Rewriter.insertBlock?]
  grind [BlockInsertPoint.next, BlockInsertPoint.prev!]

grind_pattern BlockPtr.next!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, (block.get! newCtx).next

theorem BlockPtr.parent!_insertBlock? {block : BlockPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    (block.get! newCtx).parent =
      if block = newBlock then
        ip.region! ctx
      else
      (block.get! ctx).parent := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern BlockPtr.parent!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, (block.get! newCtx).parent

@[simp]
theorem BlockPtr.firstOp!_insertBlock? {block : BlockPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    (block.get! newCtx).firstOp = (block.get! ctx).firstOp := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern BlockPtr.firstOp!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, (block.get! newCtx).firstOp

@[simp]
theorem BlockPtr.lastOp!_insertBlock? {block : BlockPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    (block.get! newCtx).lastOp = (block.get! ctx).lastOp := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern BlockPtr.lastOp!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, (block.get! newCtx).lastOp

@[simp]
theorem OperationPtr.get!_insertBlock? {operation : OperationPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.get! newCtx = operation.get! ctx := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern OperationPtr.get!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.get! newCtx

@[simp]
theorem OperationPtr.getNumResults!_insertBlock? {operation : OperationPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.getNumResults! newCtx = operation.getNumResults! ctx := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern OperationPtr.getNumResults!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getNumResults! newCtx

@[simp]
theorem OpResultPtr.get!_insertBlock? {opResult : OpResultPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    opResult.get! newCtx = opResult.get! ctx := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern OpResultPtr.get!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, opResult.get! newCtx

@[simp]
theorem OperationPtr.getNumOperands!_insertBlock? {operation : OperationPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.getNumOperands! newCtx = operation.getNumOperands! ctx := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern OperationPtr.getNumOperands!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getNumOperands! newCtx

@[simp]
theorem OpOperandPtr.get!_insertBlock? {operand : OpOperandPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operand.get! newCtx = operand.get! ctx := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern OpOperandPtr.get!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, operand.get! newCtx

@[simp]
theorem OperationPtr.getNumSuccessors!_insertBlock? {operation : OperationPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.getNumSuccessors! newCtx = operation.getNumSuccessors! ctx := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern OperationPtr.getNumSuccessors!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getNumSuccessors! newCtx

@[simp]
theorem BlockOperandPtr.get!_insertBlock? {operand : BlockOperandPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operand.get! newCtx = operand.get! ctx := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern BlockOperandPtr.get!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, operand.get! newCtx

@[simp]
theorem OperationPtr.getNumRegions!_insertBlock? {operation : OperationPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.getNumRegions! newCtx = operation.getNumRegions! ctx := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern OperationPtr.getNumRegions!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getNumRegions! newCtx

@[simp]
theorem OperationPtr.getRegion!_insertBlock? {operation : OperationPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.getRegion! newCtx = operation.getRegion! ctx := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern OperationPtr.getRegion!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getRegion! newCtx

@[simp]
theorem BlockOperandPtrPtr.get!_insertBlock? {operandPtr : BlockOperandPtrPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operandPtr.get! newCtx = operandPtr.get! ctx := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern BlockOperandPtrPtr.get!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, operandPtr.get! newCtx

@[simp]
theorem BlockPtr.getNumArguments!_insertBlock? {block : BlockPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    block.getNumArguments! newCtx = block.getNumArguments! ctx := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern BlockPtr.getNumArguments!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, block.getNumArguments! newCtx

@[simp]
theorem BlockArgumentPtr.get!_insertBlock? {blockArg : BlockArgumentPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    blockArg.get! newCtx = blockArg.get! ctx := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern BlockArgumentPtr.get!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, blockArg.get! newCtx

theorem RegionPtr.firstBlock!_insertBlock? {region : RegionPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    (region.get! newCtx).firstBlock =
      if ip.region! ctx = region ∧ ip.prev! ctx = none then
        some newBlock
      else
        (region.get! ctx).firstBlock := by
  simp only [Rewriter.insertBlock?]
  split
  · split
    · grind
    · grind [InsertPoint.block!, InsertPoint.prev!]
  · grind [InsertPoint.block!, InsertPoint.prev!]

grind_pattern RegionPtr.firstBlock!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, (region.get! newCtx).firstBlock

theorem RegionPtr.lastBlock!_insertBlock? {region : RegionPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    (region.get! newCtx).lastBlock =
      if ip.region! ctx = region ∧ ip.next = none then
        some newBlock
      else
        (region.get! ctx).lastBlock := by
  simp only [Rewriter.insertBlock?]
  split
  · split
    · grind
    · grind [InsertPoint.block!, InsertPoint.prev!]
  · grind [InsertPoint.block!, InsertPoint.prev!]

grind_pattern RegionPtr.lastBlock!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, (region.get! newCtx).lastBlock

@[simp]
theorem RegionPtr.parent!_insertBlock? {region : RegionPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    (region.get! newCtx).parent = (region.get! ctx).parent := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern RegionPtr.parent!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, (region.get! newCtx).parent

@[simp]
theorem ValuePtr.getFirstUse!_insertBlock? {value : ValuePtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    value.getFirstUse! newCtx = value.getFirstUse! ctx := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern ValuePtr.getFirstUse!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, value.getFirstUse! newCtx

@[simp]
theorem ValuePtr.getType!_insertBlock? {value : ValuePtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    value.getType! newCtx = value.getType! ctx := by
  grind

grind_pattern ValuePtr.getType!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, value.getType! newCtx

@[simp]
theorem OpOperandPtrPtr.get!_insertBlock? {opOperandPtr : OpOperandPtrPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    opOperandPtr.get! newCtx = opOperandPtr.get! ctx := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern OpOperandPtrPtr.get!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, opOperandPtr.get! newCtx

end Rewriter.insertBlock?


/- replaceUse -/

@[simp, grind .]
theorem BlockOperandPtr.get_replaceUse {bop : BlockOperandPtr} {hbop} :
    bop.get (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) hbop =
    bop.get ctx (by grind) := by
  unfold Rewriter.replaceUse
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp_replaceUse {b : BlockPtr} {hb} :
    (b.get (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) hb).firstOp =
    (b.get ctx (by grind)).firstOp := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem BlockPtr.getLastOp_replaceUse {b : BlockPtr} {hb} :
    (b.get (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) hb).lastOp =
    (b.get ctx (by grind)).lastOp := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem BlockPtr.getNext_replaceUse {b : BlockPtr} {hb} :
    (b.get (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) hb).next =
    (b.get ctx (by grind)).next := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem BlockPtr.getPrev_replaceUse {b : BlockPtr} {hb} :
    (b.get (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) hb).prev =
    (b.get ctx (by grind)).prev := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem BlockPtr.getParent_replaceUse {b : BlockPtr} {hb} :
    (b.get (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) hb).parent =
    (b.get ctx (by grind)).parent := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem OperationPtr.getParent_replaceUse {op : OperationPtr} {hop} :
    (op.get (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) hop).parent =
    (op.get ctx (by grind)).parent := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem OperationPtr.getNext_replaceUse {op : OperationPtr} {hop} :
    (op.get (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) hop).next =
    (op.get ctx (by grind)).next := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem OperationPtr.getPrev_replaceUse {op : OperationPtr} {hop} :
    (op.get (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) hop).prev =
    (op.get ctx (by grind)).prev := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem OperationPtr.getNumOperands_replaceUse :
    OperationPtr.getNumOperands op (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) hop =
    OperationPtr.getNumOperands op ctx (by grind) := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem OpOperandPtr.owner_replaceUse :
    (OpOperandPtr.get opr (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) hop).owner =
    (OpOperandPtr.get opr ctx (by grind)).owner := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_replaceUse :
    OperationPtr.getNumSuccessors! op (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    OperationPtr.getNumSuccessors! op ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem BlockOperandPtr.get!_replaceUse :
    BlockOperandPtr.get! bop (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    BlockOperandPtr.get! bop ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem OperationPtr.getNumResults_replaceUse :
    OperationPtr.getNumResults! op (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    OperationPtr.getNumResults! op ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem OpResultPtr.owner_replaceUse :
    (OpResultPtr.get opr (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) hopr).owner =
    (OpResultPtr.get opr ctx (by grind)).owner := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem OpResultPtr.index_replaceUse :
    (OpResultPtr.get opr (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) hopr).index =
    (OpResultPtr.get opr ctx (by grind)).index := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem OperationPtr.getRegions_replaceUse :
    OperationPtr.getRegion! op (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    OperationPtr.getRegion! op ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem BlockPtr.getNumArguments_replaceUse :
    BlockPtr.getNumArguments! block (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    BlockPtr.getNumArguments! block ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem BlockArgumentPtr.owner!_replaceUse :
    (BlockArgumentPtr.get! arg (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn)).owner =
    (BlockArgumentPtr.get! arg ctx).owner := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem BlockArgumentPtr.index!_replaceUse :
    (BlockArgumentPtr.get! arg (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn)).index =
    (BlockArgumentPtr.get! arg ctx).index := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem RegionPtr.get_replaceUse :
    RegionPtr.get reg (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) hreg =
    RegionPtr.get reg ctx (by grind) := by
  grind [Rewriter.replaceUse]

/- replaceValue? -/

@[simp, grind .]
theorem OperationPtr.getNumOperands_iff_replaceValue?
    (hctx' : Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some ctx') :
    OperationPtr.getNumOperands op ctx' h_op =
    OperationPtr.getNumOperands op ctx (by grind) := by
  grind [OpOperandPtr.inBounds_if_operand_size_eq]

@[grind .]
theorem Rewriter.createOp_inBounds_mono (ptr : GenericPtr)
    (heq : createOp ctx opType numResults operands numRegions props ip h₁ h₂ h₃ = some (newCtx, newOp)) :
    ptr.InBounds ctx → ptr.InBounds newCtx := by
  simp [createOp] at heq
  split at heq
  · grind
  · split at heq
    · grind
    · split at heq
      · split at heq <;> grind
      · grind

@[grind .]
theorem Rewriter.createOp_fieldsInBounds
    (heq : createOp ctx opType numResults operands numRegions props ip h₁ h₂ h₃ = some (newCtx, newOp)) :
    ctx.FieldsInBounds → newCtx.FieldsInBounds := by
  intros hx
  simp [createOp] at heq
  split at heq
  · grind
  · split at heq
    · grind
    · split at heq
      · split at heq <;> grind
      · grind
