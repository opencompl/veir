import Veir.Rewriter.Basic
import Veir.Rewriter.LinkedList.GetSet
import Veir.ForLean

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
 -   * Operation.opType
 -   * Operation.attrs
 - * OperationPtr.getProperties!
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

variable {opInfo} [OpInfo opInfo]
variable {ctx : IRContext opInfo}

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
  grind

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
theorem OperationPtr.getProperties!_insertOp? {operation : OperationPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operation.getProperties! newCtx opCode = operation.getProperties! ctx opCode := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern OperationPtr.getProperties!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, operation.getProperties! newCtx opCode

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

namespace Rewriter.unsetParentAndNeighbors

attribute [local grind] Rewriter.unsetParentAndNeighbors

@[simp, grind =]
theorem BlockPtr.firstUse!_unsetParentAndNeighbors {block : BlockPtr} :
    (block.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn)).firstUse = (block.get! ctx).firstUse := by
  grind

@[simp, grind =]
theorem BlockPtr.prev!_unsetParentAndNeighbors {block : BlockPtr} :
    (block.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn)).prev = (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_unsetParentAndNeighbors {block : BlockPtr} :
    (block.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn)).next = (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_unsetParentAndNeighbors {block : BlockPtr} :
    (block.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn)).parent = (block.get! ctx).parent := by
  grind

@[grind =]
theorem BlockPtr.firstOp!_unsetParentAndNeighbors {block : BlockPtr} :
    (block.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn)).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[grind =]
theorem BlockPtr.lastOp!_unsetParentAndNeighbors {block : BlockPtr} :
    (block.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn)).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[grind =]
theorem OperationPtr.prev!_unsetParentAndNeighbors {operation : OperationPtr} :
    (operation.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn)).prev =
    if operation = op' then
      none
    else
      (operation.get! ctx).prev := by
  grind

@[grind =]
theorem OperationPtr.next!_unsetParentAndNeighbors {operation : OperationPtr} :
    (operation.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn)).next =
    if operation = op' then
      none
    else
      (operation.get! ctx).next := by
  grind

@[grind =]
theorem OperationPtr.parent!_unsetParentAndNeighbors {operation : OperationPtr} :
    (operation.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn)).parent =
    if operation = op' then none else (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_unsetParentAndNeighbors {operation : OperationPtr} :
    (operation.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn)).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_unsetParentAndNeighbors {operation : OperationPtr} :
    (operation.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn)).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_unsetParentAndNeighbors {operation : OperationPtr} :
    operation.getProperties! (Rewriter.unsetParentAndNeighbors ctx op' hIn) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_unsetParentAndNeighbors {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_unsetParentAndNeighbors {opResult : OpResultPtr} :
    opResult.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_unsetParentAndNeighbors {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.unsetParentAndNeighbors ctx op' hIn) = operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_unsetParentAndNeighbors {opOperand : OpOperandPtr} :
    opOperand.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn) = opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_unsetParentAndNeighbors {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_unsetParentAndNeighbors {blockOperand : BlockOperandPtr} :
    blockOperand.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_unsetParentAndNeighbors {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_unsetParentAndNeighbors {operation : OperationPtr} :
    operation.getRegion! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    operation.getRegion! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_unsetParentAndNeighbors {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_unsetParentAndNeighbors {block : BlockPtr} :
    block.getNumArguments! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_unsetParentAndNeighbors {blockArg : BlockArgumentPtr} :
    blockArg.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_unsetParentAndNeighbors {region : RegionPtr} :
    region.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_unsetParentAndNeighbors {value : ValuePtr} :
    value.getFirstUse! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_unsetParentAndNeighbors {value : ValuePtr} :
    value.getType! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_unsetParentAndNeighbors {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn) = opOperandPtr.get! ctx := by
  grind

end Rewriter.unsetParentAndNeighbors

section Rewriter.detachOp

variable {op : OperationPtr}

attribute [local grind] Rewriter.detachOp

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
    else if operation = op' then
      none
    else
      (operation.get! ctx).prev := by
  grind

@[grind =]
theorem OperationPtr.next!_detachOp {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃)).next =
    if operation = (op'.get! ctx).prev then
      (op'.get! ctx).next
    else if operation = op' then
      none
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
theorem OperationPtr.getProperties!_detachOp {operation : OperationPtr} :
    operation.getProperties! (Rewriter.detachOp ctx op' h₁ h₂ h₃) opCode =
    operation.getProperties! ctx opCode := by
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
  simp only [Rewriter.insertBlock?]
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

section Rewriter.detachOpIfAttached

variable {op : OperationPtr}

attribute [local grind] Rewriter.detachOpIfAttached

@[simp, grind =]
theorem BlockPtr.firstUse!_detachOpIfAttached {block : BlockPtr} :
    (block.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp)).firstUse = (block.get! ctx).firstUse := by
  grind

@[simp, grind =]
theorem BlockPtr.prev!_detachOpIfAttached {block : BlockPtr} :
    (block.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp)).prev = (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_detachOpIfAttached {block : BlockPtr} :
    (block.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp)).next = (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_detachOpIfAttached {block : BlockPtr} :
    (block.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp)).parent = (block.get! ctx).parent := by
  grind

@[grind =]
theorem BlockPtr.firstOp!_detachOpIfAttached {block : BlockPtr} :
    (block.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp)).firstOp =
    if (op'.get! ctx).prev = none ∧ block = (op'.get! ctx).parent then
      (op'.get! ctx).next
    else
      (block.get! ctx).firstOp := by
  grind

@[grind =]
theorem BlockPtr.lastOp!_detachOpIfAttached {block : BlockPtr} :
    (block.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp)).lastOp =
    if (op'.get! ctx).next = none ∧ block = (op'.get! ctx).parent then
      (op'.get! ctx).prev
    else
      (block.get! ctx).lastOp := by
  grind

@[grind =]
theorem OperationPtr.prev!_detachOpIfAttached {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp)).prev =
    if (op'.get! ctx).parent ≠ none ∧ operation = (op'.get! ctx).next then
      (op'.get! ctx).prev
    else if (op'.get! ctx).parent ≠ none ∧ operation = op' then
      none
    else
      (operation.get! ctx).prev := by
  grind

@[grind =]
theorem OperationPtr.next!_detachOpIfAttached {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp)).next =
    if (op'.get! ctx).parent ≠ none ∧ operation = (op'.get! ctx).prev then
      (op'.get! ctx).next
    else if (op'.get! ctx).parent ≠ none ∧ operation = op' then
      none
    else
      (operation.get! ctx).next := by
  grind

@[grind =]
theorem OperationPtr.parent!_detachOpIfAttached {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp)).parent =
    if operation = op' then none else (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_detachOpIfAttached {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp)).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_detachOpIfAttached {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp)).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_detachOpIfAttached {operation : OperationPtr} :
    operation.getProperties! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_detachOpIfAttached {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_detachOpIfAttached {opResult : OpResultPtr} :
    opResult.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_detachOpIfAttached {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) = operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_detachOpIfAttached {opOperand : OpOperandPtr} :
    opOperand.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) = opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_detachOpIfAttached {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_detachOpIfAttached {blockOperand : BlockOperandPtr} :
    blockOperand.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_detachOpIfAttached {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_detachOpIfAttached {operation : OperationPtr} :
    operation.getRegion! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    operation.getRegion! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_detachOpIfAttached {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_detachOpIfAttached {block : BlockPtr} :
    block.getNumArguments! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_detachOpIfAttached {blockArg : BlockArgumentPtr} :
    blockArg.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_detachOpIfAttached {region : RegionPtr} :
    region.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_detachOpIfAttached {value : ValuePtr} :
    value.getFirstUse! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_detachOpIfAttached {value : ValuePtr} :
    value.getType! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_detachOpIfAttached {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) = opOperandPtr.get! ctx := by
  grind

end Rewriter.detachOpIfAttached

section Rewriter.detachOperands.loop

variable {op : OperationPtr}

attribute [local grind] Rewriter.detachOperands.loop

@[simp, grind =]
theorem BlockPtr.firstUse!_detachOperands_loop {block : BlockPtr} :
    (block.get! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex)).firstUse = (block.get! ctx).firstUse := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

@[simp, grind =]
theorem BlockPtr.prev!_detachOperands_loop {block : BlockPtr} :
    (block.get! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex)).prev = (block.get! ctx).prev := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

@[simp, grind =]
theorem BlockPtr.next!_detachOperands_loop {block : BlockPtr} :
    (block.get! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex)).next = (block.get! ctx).next := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

@[simp, grind =]
theorem BlockPtr.parent!_detachOperands_loop {block : BlockPtr} :
    (block.get! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex)).parent = (block.get! ctx).parent := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

@[grind =]
theorem BlockPtr.firstOp!_detachOperands_loop {block : BlockPtr} :
    (block.get! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex)).firstOp =
    (block.get! ctx).firstOp := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

@[grind =]
theorem BlockPtr.lastOp!_detachOperands_loop {block : BlockPtr} :
    (block.get! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex)).lastOp =
    (block.get! ctx).lastOp := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

@[grind =]
theorem OperationPtr.prev!_detachOperands_loop {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex)).prev =
    (operation.get! ctx).prev := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

@[grind =]
theorem OperationPtr.next!_detachOperands_loop {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex)).next =
    (operation.get! ctx).next := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

@[grind =]
theorem OperationPtr.parent!_detachOperands_loop {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex)).parent =
    (operation.get! ctx).parent := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

@[simp, grind =]
theorem OperationPtr.opType!_detachOperands_loop {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex)).opType =
    (operation.get! ctx).opType := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

@[simp, grind =]
theorem OperationPtr.attrs!_detachOperands_loop {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex)).attrs =
    (operation.get! ctx).attrs := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

@[simp, grind =]
theorem OperationPtr.getProperties!_detachOperands_loop {operation : OperationPtr} :
    operation.getProperties! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) opCode =
    operation.getProperties! ctx opCode := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_detachOperands_loop {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) =
    operation.getNumResults! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

-- The theorem `OpResultPtr.get!_detachOperands_loop` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.OpChain` directly.

@[simp, grind =]
theorem OperationPtr.getNumOperands!_detachOperands_loop {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) = operation.getNumOperands! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

-- The theorem `OpOperandPtr.get!_detachOperands_loop` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.OpChain` directly.

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_detachOperands_loop {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) =
    operation.getNumSuccessors! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

@[simp, grind =]
theorem BlockOperandPtr.get!_detachOperands_loop {blockOperand : BlockOperandPtr} :
    blockOperand.get! (Rewriter.detachOperands.loop ctx op' index' hCtx hOp hIndex) =
    blockOperand.get! ctx := by
  induction index' generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_detachOperands_loop {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) =
    operation.getNumRegions! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

@[simp, grind =]
theorem OperationPtr.getRegion!_detachOperands_loop {operation : OperationPtr} :
    operation.getRegion! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) i =
    operation.getRegion! ctx i := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_detachOperands_loop {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) =
    blockOperandPtr.get! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_detachOperands_loop {block : BlockPtr} :
    block.getNumArguments! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) =
    block.getNumArguments! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

-- The theorem `BlockArgumentPtr.get!_detachOperands_loop` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.OpChain` directly.

@[simp, grind =]
theorem RegionPtr.get!_detachOperands_loop {region : RegionPtr} :
    region.get! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) =
    region.get! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

-- The theorem `ValuePtr.getFirstUse!_detachOperands_loop` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.OpChain` directly.

@[simp, grind =]
theorem ValuePtr.getType!_detachOperands_loop {value : ValuePtr} :
    value.getType! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) =
    value.getType! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

-- The theorem `OpOperandPtr.getFirstUse!_detachOperands_loop` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.OpChain` directly.

end Rewriter.detachOperands.loop

section Rewriter.detachOperands

variable {op : OperationPtr}

attribute [local grind] Rewriter.detachOperands

@[simp, grind =]
theorem BlockPtr.firstUse!_detachOperands {block : BlockPtr} :
    (block.get! (Rewriter.detachOperands ctx op' hCtx hOp)).firstUse = (block.get! ctx).firstUse := by
  grind

@[simp, grind =]
theorem BlockPtr.prev!_detachOperands {block : BlockPtr} :
    (block.get! (Rewriter.detachOperands ctx op' hCtx hOp)).prev = (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_detachOperands {block : BlockPtr} :
    (block.get! (Rewriter.detachOperands ctx op' hCtx hOp)).next = (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_detachOperands {block : BlockPtr} :
    (block.get! (Rewriter.detachOperands ctx op' hCtx hOp)).parent = (block.get! ctx).parent := by
  grind

@[grind =]
theorem BlockPtr.firstOp!_detachOperands {block : BlockPtr} :
    (block.get! (Rewriter.detachOperands ctx op' hCtx hOp)).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[grind =]
theorem BlockPtr.lastOp!_detachOperands {block : BlockPtr} :
    (block.get! (Rewriter.detachOperands ctx op' hCtx hOp)).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[grind =]
theorem OperationPtr.prev!_detachOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOperands ctx op' hCtx hOp)).prev =
    (operation.get! ctx).prev := by
  grind

@[grind =]
theorem OperationPtr.next!_detachOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOperands ctx op' hCtx hOp)).next =
    (operation.get! ctx).next := by
  grind

@[grind =]
theorem OperationPtr.parent!_detachOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOperands ctx op' hCtx hOp)).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_detachOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOperands ctx op' hCtx hOp)).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_detachOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOperands ctx op' hCtx hOp)).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_detachOperands {operation : OperationPtr} :
    operation.getProperties! (Rewriter.detachOperands ctx op' hCtx hOp) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_detachOperands {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.detachOperands ctx op' hCtx hOp) =
    operation.getNumResults! ctx := by
  grind

-- The theorem `OpResultPtr.get!_detachOperands` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.OpChain` directly.

@[simp, grind =]
theorem OperationPtr.getNumOperands!_detachOperands {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.detachOperands ctx op' hCtx hOp) = operation.getNumOperands! ctx := by
  grind

-- The theorem `OpOperandPtr.get!_detachOperands` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.OpChain` directly.

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_detachOperands {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.detachOperands ctx op' hCtx hOp) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_detachOperands {blockOperand : BlockOperandPtr} :
    blockOperand.get! (Rewriter.detachOperands ctx op' hCtx hOp) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_detachOperands {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.detachOperands ctx op' hCtx hOp) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_detachOperands {operation : OperationPtr} :
    operation.getRegion! (Rewriter.detachOperands ctx op' hCtx hOp) i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_detachOperands {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (Rewriter.detachOperands ctx op' hCtx hOp) =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_detachOperands {block : BlockPtr} :
    block.getNumArguments! (Rewriter.detachOperands ctx op' hCtx hOp) =
    block.getNumArguments! ctx := by
  grind

-- The theorem `BlockArgumentPtr.get!_detachOperands` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.OpChain` directly.

@[simp, grind =]
theorem RegionPtr.get!_detachOperands {region : RegionPtr} :
    region.get! (Rewriter.detachOperands ctx op' hCtx hOp) =
    region.get! ctx := by
  grind

-- The theorem `ValuePtr.getFirstUse!_detachOperands` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.OpChain` directly.

@[simp, grind =]
theorem ValuePtr.getType!_detachOperands {value : ValuePtr} :
    value.getType! (Rewriter.detachOperands ctx op' hCtx hOp) =
    value.getType! ctx := by
  grind

-- The theorem `OpOperandPtr.getFirstUse!_detachOperands` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.OpChain` directly.

end Rewriter.detachOperands

section Rewriter.detachBlockOperands.loop

variable {op : OperationPtr}

attribute [local grind] Rewriter.detachBlockOperands.loop

-- The theorem `BlockPtr.firstUse!_detachBlockOperands_loop` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.DefUse` directly.

@[simp, grind =]
theorem BlockPtr.prev!_detachBlockOperands_loop {block : BlockPtr} :
    (block.get! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex)).prev = (block.get! ctx).prev := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =]
theorem BlockPtr.next!_detachBlockOperands_loop {block : BlockPtr} :
    (block.get! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex)).next = (block.get! ctx).next := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =]
theorem BlockPtr.parent!_detachBlockOperands_loop {block : BlockPtr} :
    (block.get! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex)).parent = (block.get! ctx).parent := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[grind =]
theorem BlockPtr.firstOp!_detachBlockOperands_loop {block : BlockPtr} :
    (block.get! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex)).firstOp =
    (block.get! ctx).firstOp := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[grind =]
theorem BlockPtr.lastOp!_detachBlockOperands_loop {block : BlockPtr} :
    (block.get! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex)).lastOp =
    (block.get! ctx).lastOp := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[grind =]
theorem OperationPtr.prev!_detachBlockOperands_loop {operation : OperationPtr} :
    (operation.get! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex)).prev =
    (operation.get! ctx).prev := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[grind =]
theorem OperationPtr.next!_detachBlockOperands_loop {operation : OperationPtr} :
    (operation.get! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex)).next =
    (operation.get! ctx).next := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[grind =]
theorem OperationPtr.parent!_detachBlockOperands_loop {operation : OperationPtr} :
    (operation.get! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex)).parent =
    (operation.get! ctx).parent := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =]
theorem OperationPtr.opType!_detachBlockOperands_loop {operation : OperationPtr} :
    (operation.get! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex)).opType =
    (operation.get! ctx).opType := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =]
theorem OperationPtr.attrs!_detachBlockOperands_loop {operation : OperationPtr} :
    (operation.get! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex)).attrs =
    (operation.get! ctx).attrs := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =]
theorem OperationPtr.getProperties!_detachBlockOperands_loop {operation : OperationPtr} :
    operation.getProperties! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) opCode =
    operation.getProperties! ctx opCode := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_detachBlockOperands_loop {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) =
    operation.getNumResults! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =]
theorem OpResultPtr.get!_detachBlockOperands_loop {opResult : OpResultPtr} :
    opResult.get! (Rewriter.detachBlockOperands.loop ctx op' idx hCtx hOp hIdx) =
    opResult.get! ctx := by
  induction idx generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_detachBlockOperands_loop {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) = operation.getNumOperands! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =]
theorem OpOperandPtr.get!_detachBlockOperands_loop {opOperand : OpOperandPtr} :
    opOperand.get! (Rewriter.detachBlockOperands.loop ctx op' idx hCtx hOp hIdx) =
    opOperand.get! ctx := by
  induction idx generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_detachBlockOperands_loop {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) =
    operation.getNumSuccessors! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

-- The theorem `BlockOperandPtr.getFirstUse!_detachBlockOperands_loop` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.DefUse` directly.

@[simp, grind =]
theorem OperationPtr.getNumRegions!_detachBlockOperands_loop {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) =
    operation.getNumRegions! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =]
theorem OperationPtr.getRegion!_detachBlockOperands_loop {operation : OperationPtr} :
    operation.getRegion! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) i =
    operation.getRegion! ctx i := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

-- The theorem `BlockOperandPtrPtr.getFirstUse!_detachBlockOperands_loop` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.DefUse` directly.

@[simp, grind =]
theorem BlockPtr.getNumArguments!_detachBlockOperands_loop {block : BlockPtr} :
    block.getNumArguments! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) =
    block.getNumArguments! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_detachBlockOperands_loop {blockArg : BlockArgumentPtr} :
    blockArg.get! (Rewriter.detachBlockOperands.loop ctx op' idx hCtx hOp hIdx) =
    blockArg.get! ctx := by
  induction idx generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =]
theorem RegionPtr.get!_detachBlockOperands_loop {region : RegionPtr} :
    region.get! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) =
    region.get! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_detachBlockOperands_loop {value : ValuePtr} :
    value.getFirstUse! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) =
    value.getFirstUse! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =]
theorem ValuePtr.getType!_detachBlockOperands_loop {value : ValuePtr} :
    value.getType! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) =
    value.getType! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_detachBlockOperands_loop {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) =
    opOperandPtr.get! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

end Rewriter.detachBlockOperands.loop

section Rewriter.detachBlockOperands

variable {op : OperationPtr}

attribute [local grind] Rewriter.detachBlockOperands

-- The theorem `BlockPtr.firstUse!_detachBlockOperands` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.DefUse` directly.

@[simp, grind =]
theorem BlockPtr.prev!_detachBlockOperands {block : BlockPtr} :
    (block.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp)).prev = (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_detachBlockOperands {block : BlockPtr} :
    (block.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp)).next = (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_detachBlockOperands {block : BlockPtr} :
    (block.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp)).parent = (block.get! ctx).parent := by
  grind

@[grind =]
theorem BlockPtr.firstOp!_detachBlockOperands {block : BlockPtr} :
    (block.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp)).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[grind =]
theorem BlockPtr.lastOp!_detachBlockOperands {block : BlockPtr} :
    (block.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp)).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[grind =]
theorem OperationPtr.prev!_detachBlockOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp)).prev =
    (operation.get! ctx).prev := by
  grind

@[grind =]
theorem OperationPtr.next!_detachBlockOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp)).next =
    (operation.get! ctx).next := by
  grind

@[grind =]
theorem OperationPtr.parent!_detachBlockOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp)).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_detachBlockOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp)).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_detachBlockOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp)).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_detachBlockOperands {operation : OperationPtr} :
    operation.getProperties! (Rewriter.detachBlockOperands ctx op' hCtx hOp) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_detachBlockOperands {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_detachBlockOperands {opResult : OpResultPtr} :
    opResult.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_detachBlockOperands {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.detachBlockOperands ctx op' hCtx hOp) = operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_detachBlockOperands {opOperand : OpOperandPtr} :
    opOperand.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_detachBlockOperands {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    operation.getNumSuccessors! ctx := by
  grind

-- The theorem `BlockOperandPtr.get!_detachBlockOperands` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.DefUse` directly.

@[simp, grind =]
theorem OperationPtr.getNumRegions!_detachBlockOperands {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_detachBlockOperands {operation : OperationPtr} :
    operation.getRegion! (Rewriter.detachBlockOperands ctx op' hCtx hOp) i =
    operation.getRegion! ctx i := by
  grind

-- The theorem `BlockOperandPtrPtr.get!_detachBlockOperands` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.DefUse` directly.

@[simp, grind =]
theorem BlockPtr.getNumArguments!_detachBlockOperands {block : BlockPtr} :
    block.getNumArguments! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_detachBlockOperands {blockArg : BlockArgumentPtr} :
    blockArg.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_detachBlockOperands {region : RegionPtr} :
    region.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_detachBlockOperands {value : ValuePtr} :
    value.getFirstUse! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_detachBlockOperands {value : ValuePtr} :
    value.getType! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    value.getType! ctx := by
  grind

theorem OpOperandPtrPtr.get!_detachBlockOperands {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    opOperandPtr.get! ctx := by
  grind

end Rewriter.detachBlockOperands

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
theorem OperationPtr.getNumRegions_replaceUse :
    OperationPtr.getNumRegions! op (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    OperationPtr.getNumRegions! op ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem OperationPtr.getRegions_replaceUse :
    OperationPtr.getRegion! op (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    OperationPtr.getRegion! op ctx := by
  grind (instances := 2000) [Rewriter.replaceUse] -- TODO: instance threshold reached when adding lemmas for Region.allocEmpty

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
  grind (instances := 2000) [Rewriter.replaceUse]  -- TODO: instance threshold reached when adding lemmas for Region.allocEmpty

/-! ## `Rewriter.initOpResults` -/

section Rewriter.initOpResults

variable {op : OperationPtr}

attribute [local grind] Rewriter.initOpResults

@[simp, grind =]
theorem BlockPtr.get!_initOpResults {block : BlockPtr} :
    block.get! (Rewriter.initOpResults ctx op types index hop hidx) = block.get! ctx := by
  fun_induction Rewriter.initOpResults <;> grind


@[simp, grind =]
theorem OperationPtr.prev!_initOpResults {operation : OperationPtr} :
    (operation.get! (Rewriter.initOpResults ctx op types index hop hidx)).prev =
    (operation.get! ctx).prev := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =]
theorem OperationPtr.next!_initOpResults {operation : OperationPtr} :
    (operation.get! (Rewriter.initOpResults ctx op types index hop hidx)).next =
    (operation.get! ctx).next := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =]
theorem OperationPtr.parent!_initOpResults {operation : OperationPtr} :
    (operation.get! (Rewriter.initOpResults ctx op types index hop hidx)).parent =
    (operation.get! ctx).parent := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =]
theorem OperationPtr.opType!_initOpResults {operation : OperationPtr} :
    (operation.get! (Rewriter.initOpResults ctx op types index hop hidx)).opType =
    (operation.get! ctx).opType := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =]
theorem OperationPtr.attrs!_initOpResults {operation : OperationPtr} :
    (operation.get! (Rewriter.initOpResults ctx op types index hop hidx)).attrs =
    (operation.get! ctx).attrs := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =]
theorem OperationPtr.getProperties!_initOpResults {operation : OperationPtr} :
    operation.getProperties! (Rewriter.initOpResults ctx op types index hop hidx) opCode =
    operation.getProperties! ctx opCode := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_initOpResults {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.initOpResults ctx op types index hop hidx) =
    if operation = op then op.getNumResults! ctx + (types.size - index) else operation.getNumResults! ctx := by
  fun_induction Rewriter.initOpResults <;> grind

@[local grind =]
theorem OpResultPtr.get!_initOpResults {opResult : OpResultPtr} {index : Nat} {hidx} :
    opResult.get! (Rewriter.initOpResults ctx op types index hop hidx) =
    if h : opResult.op = op ∧ opResult.index < types.size ∧ op.getNumResults! ctx ≤ opResult.index then
      { type := types[opResult.index], firstUse := none, index := opResult.index, owner := op }
    else opResult.get! ctx := by
  fun_induction Rewriter.initOpResults <;> grind

@[grind =]
theorem OpResultPtr.type!_initOpResults {opResult : OpResultPtr} {index : Nat} {hidx} :
    (opResult.get! (Rewriter.initOpResults ctx op types index hop hidx)).type =
    if h : opResult.op = op ∧ opResult.index < types.size ∧ op.getNumResults! ctx ≤ opResult.index then
      types[opResult.index]
    else (opResult.get! ctx).type := by
  grind

@[grind =]
theorem OpResultPtr.firstUse!_initOpResults {opResult : OpResultPtr} {index : Nat} {hidx} :
    (opResult.get! (Rewriter.initOpResults ctx op types index hop hidx)).firstUse =
    if opResult.op = op ∧ opResult.index < types.size ∧ op.getNumResults! ctx ≤ opResult.index then none
    else (opResult.get! ctx).firstUse := by
  grind

@[grind =]
theorem OpResultPtr.index!_initOpResults {opResult : OpResultPtr} {index : Nat} {hidx} :
    (opResult.get! (Rewriter.initOpResults ctx op types index hop hidx)).index =
    if opResult.op = op ∧ opResult.index < types.size ∧ op.getNumResults! ctx ≤ opResult.index then
      opResult.index
    else (opResult.get! ctx).index := by
  grind

@[grind =]
theorem OpResultPtr.owner!_initOpResults {opResult : OpResultPtr} {index : Nat} {hidx} :
    (opResult.get! (Rewriter.initOpResults ctx op types index hop hidx)).owner =
    if opResult.op = op ∧ opResult.index < types.size ∧ op.getNumResults! ctx ≤ opResult.index then op
    else (opResult.get! ctx).owner := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_initOpResults {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.initOpResults ctx op types index hop hidx) = operation.getNumOperands! ctx := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =]
theorem OpOperandPtr.get!_initOpResults {opOperand : OpOperandPtr} {index} {hidx} :
    opOperand.get! (Rewriter.initOpResults ctx op types index hop hidx) = opOperand.get! ctx := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_initOpResults {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.initOpResults ctx op types index hop hidx) =
    operation.getNumSuccessors! ctx := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =]
theorem BlockOperandPtr.get!_initOpResults {blockOperand : BlockOperandPtr} {index} {hidx} :
    blockOperand.get! (Rewriter.initOpResults ctx op types index hop hidx) =
    blockOperand.get! ctx := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_initOpResults {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.initOpResults ctx op types index hop hidx) =
    operation.getNumRegions! ctx := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =]
theorem OperationPtr.getRegion!_initOpResults {operation : OperationPtr} :
    operation.getRegion! (Rewriter.initOpResults ctx op types index hop hidx) =
    operation.getRegion! ctx := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_initOpResults {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (Rewriter.initOpResults ctx op types index hop hidx) =
    blockOperandPtr.get! ctx := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_initOpResults {block : BlockPtr} :
    block.getNumArguments! (Rewriter.initOpResults ctx op types index hop hidx) =
    block.getNumArguments! ctx := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_initOpResults {blockArg : BlockArgumentPtr} {index} {hidx} :
    blockArg.get! (Rewriter.initOpResults ctx op types index hop hidx) =
    blockArg.get! ctx := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =]
theorem RegionPtr.get!_initOpResults {region : RegionPtr} :
    region.get! (Rewriter.initOpResults ctx op types index hop hidx) =
    region.get! ctx := by
  fun_induction Rewriter.initOpResults <;> grind

@[grind =]
theorem ValuePtr.getFirstUse!_initOpResults {value : ValuePtr} :
    value.getFirstUse! (Rewriter.initOpResults ctx op types index hop hidx) =
    match value with
    | .opResult opRes =>
      if opRes.op = op ∧ opRes.index < types.size ∧ op.getNumResults! ctx ≤ opRes.index then
        none
      else value.getFirstUse! ctx
    | _ => value.getFirstUse! ctx := by
  fun_induction Rewriter.initOpResults <;> grind -- TODO: slow!

@[grind =]
theorem ValuePtr.getType!_initOpResults {value : ValuePtr} :
    value.getType! (Rewriter.initOpResults ctx op types index hop hidx) =
    match value with
    | .opResult opRes =>
      if _ : opRes.op = op ∧ opRes.index < types.size ∧ op.getNumResults! ctx ≤ opRes.index then
        types[opRes.index]
      else value.getType! ctx
    | _ => value.getType! ctx := by
  fun_induction Rewriter.initOpResults
  · grind
  · cases value <;> grind

@[grind =]
theorem OpOperandPtrPtr.get!_initOpResults {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.initOpResults ctx op types index hop hidx) =
    match opOperandPtr with
    | .valueFirstUse (.opResult opRes) =>
      if _ : opRes.op = op ∧ opRes.index < types.size ∧ op.getNumResults! ctx ≤ opRes.index then none
      else (opRes.get! ctx).firstUse
    | _ => opOperandPtr.get! ctx := by
  cases opOperandPtr
  · grind
  · simp only [get!_valueFirstUse_eq, ValuePtr.getFirstUse!_initOpResults, dite_eq_ite]; grind

end Rewriter.initOpResults

/-! ## `Rewriter.initOpRegions` -/

section Rewriter.initOpRegions

variable {op : OperationPtr}

attribute [local grind] Rewriter.initOpRegions

@[simp, grind =]
theorem BlockPtr.get!_initOpRegions {block : BlockPtr} :
    block.get! (Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄) = block.get! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind


@[simp, grind =]
theorem OperationPtr.prev!_initOpRegions {operation : OperationPtr} :
    (operation.get! (Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄)).prev =
    (operation.get! ctx).prev := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =]
theorem OperationPtr.next!_initOpRegions {operation : OperationPtr} :
    (operation.get! (Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄)).next =
    (operation.get! ctx).next := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =]
theorem OperationPtr.parent!_initOpRegions {operation : OperationPtr} :
    (operation.get! (Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄)).parent =
    (operation.get! ctx).parent := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =]
theorem OperationPtr.opType!_initOpRegions {operation : OperationPtr} :
    (operation.get! (Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄)).opType =
    (operation.get! ctx).opType := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =]
theorem OperationPtr.attrs!_initOpRegions {operation : OperationPtr} :
    (operation.get! (Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄)).attrs =
    (operation.get! ctx).attrs := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =]
theorem OperationPtr.getProperties!_initOpRegions {operation : OperationPtr} :
    operation.getProperties! (Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄) opCode =
    operation.getProperties! ctx opCode := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_initOpRegions {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄) =
    operation.getNumOperands! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =]
theorem OpResultPtr.get!_initOpRegions {opResult : OpResultPtr} {index : Nat} {h₄} :
    opResult.get! (Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄) =
    opResult.get! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =]
theorem OpOperandPtr.get!_initOpRegions {opOperand : OpOperandPtr} {index} {h₄} :
    opOperand.get! (Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄) = opOperand.get! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_initOpRegions {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄) =
    operation.getNumSuccessors! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =]
theorem BlockOperandPtr.get!_initOpRegions {blockOperand : BlockOperandPtr} {index} {h₄} :
    blockOperand.get! (Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄) =
    blockOperand.get! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[grind =]
theorem OperationPtr.getNumRegions!_initOpRegions {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄) =
    if operation = op then op.getNumRegions! ctx + (regions.size - index) else operation.getNumRegions! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =]
theorem OperationPtr.getRegion!_initOpRegions {operation : OperationPtr} :
    operation.getRegion! (Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄) idx =
    if _ : operation = op ∧ idx ≥ op.getNumRegions! ctx ∧ idx < regions.size then regions[idx]
    else operation.getRegion! ctx idx := by
  fun_induction Rewriter.initOpRegions <;> grind (splits := 15)

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_initOpRegions {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄) =
    blockOperandPtr.get! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_initOpRegions {block : BlockPtr} :
    block.getNumArguments! (Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄) =
    block.getNumArguments! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_initOpRegions {blockArg : BlockArgumentPtr} {index} {h₄} :
    blockArg.get! (Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄) =
    blockArg.get! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =]
theorem RegionPtr.firstBlock!_initOpRegions {region : RegionPtr} :
    (region.get! (Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄)).firstBlock =
    (region.get! ctx).firstBlock := by
  fun_induction Rewriter.initOpRegions <;> grind (instances := 5000)

@[simp, grind =]
theorem RegionPtr.lastBlock!_initOpRegions {region : RegionPtr} :
    (region.get! (Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄)).lastBlock =
    (region.get! ctx).lastBlock := by
  fun_induction Rewriter.initOpRegions <;> grind (instances := 5000)

theorem RegionPtr.parent!_initOpRegions_gen {region : RegionPtr} :
    (region.get! (Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄)).parent =
    if ∃ (i : Nat) (_ : i < regions.size), index ≤ i ∧ regions[i] = region then some op else (region.get! ctx).parent := by
  fun_induction Rewriter.initOpRegions
  · grind (instances := 5000) (gen := 100)
  · simp_all +zetaDelta only
    split <;> split <;> grind (instances := 5000)

@[grind =]
theorem RegionPtr.parent!_initOpRegions {region : RegionPtr} :
    (region.get! (Rewriter.initOpRegions ctx op regions 0 h₁ h₂ h₃ h₄)).parent =
    if region ∈ regions then some op else (region.get! ctx).parent := by
  rw [parent!_initOpRegions_gen]
  congr
  grind [Array.mem_iff_getElem]

@[simp, grind =]
theorem ValuePtr.getFirstUse!_initOpRegions {value : ValuePtr} :
    value.getFirstUse! (Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄) =
    value.getFirstUse! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =]
theorem ValuePtr.getType!_initOpRegions {value : ValuePtr} :
    value.getType! (Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄) =
    value.getType! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_initOpRegions {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄) =
    opOperandPtr.get! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

end Rewriter.initOpRegions

/- replaceValue? -/

@[simp, grind .]
theorem OperationPtr.getNumOperands_iff_replaceValue?
    (hctx' : Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some ctx') :
    OperationPtr.getNumOperands op ctx' h_op =
    OperationPtr.getNumOperands op ctx (by grind) := by
  grind [OpOperandPtr.inBounds_if_operand_size_eq]

@[grind .]
theorem Rewriter.createOp_inBounds_mono (ptr : GenericPtr)
    (heq : createOp ctx opType numResults operands blockOperands regions props ip h₁ h₂ h₃ h₄ h₅ = some (newCtx, newOp)) :
    ptr.InBounds ctx → ptr.InBounds newCtx := by
  simp only [createOp] at heq
  split at heq; grind
  split at heq
  · split at heq; grind
    intros hptr
    rename_i h
    simp at heq
    have ⟨_, _⟩ := heq
    subst newOp
    subst newCtx
    rw [←Rewriter.insertOp?_inBounds_mono ptr h]
    grind
  · grind (ematch := 10)

@[grind .]
theorem Rewriter.createOp_fieldsInBounds
    (heq : createOp ctx opType numResults operands blockOperands numRegions props ip h₁ h₂ h₃ h₄ h₅ = some (newCtx, newOp)) :
    ctx.FieldsInBounds → newCtx.FieldsInBounds := by
  simp only [createOp] at heq
  split at heq; grind
  split at heq
  · split at heq
    · grind
    · grind
  · grind
