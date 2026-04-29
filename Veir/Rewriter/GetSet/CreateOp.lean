module

public import Veir.IR.Basic
public import Veir.Rewriter.Basic

import all Veir.Rewriter.Basic

import Veir.Rewriter.LinkedList.GetSet
import Veir.ForLean
import Veir.IR.DeallocLemmas
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
 -   * Operation.opType
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
section Rewriter.createEmptyOp

variable {op : OperationPtr}

attribute [local grind] Rewriter.createEmptyOp

@[simp]
theorem BlockPtr.firstUse!_createEmptyOp {block : BlockPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    (block.get! ctx').firstUse = (block.get! ctx).firstUse := by
  grind

grind_pattern BlockPtr.firstUse!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), (block.get! ctx').firstUse

@[simp]
theorem BlockPtr.prev!_createEmptyOp {block : BlockPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    (block.get! ctx').prev = (block.get! ctx).prev := by
  grind

grind_pattern BlockPtr.prev!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), (block.get! ctx').prev

@[simp]
theorem BlockPtr.next!_createEmptyOp {block : BlockPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    (block.get! ctx').next = (block.get! ctx).next := by
  grind

grind_pattern BlockPtr.next!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), (block.get! ctx').next

@[simp]
theorem BlockPtr.parent!_createEmptyOp {block : BlockPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    (block.get! ctx').parent = (block.get! ctx).parent := by
  grind

grind_pattern BlockPtr.parent!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), (block.get! ctx').parent

@[simp]
theorem BlockPtr.firstOp!_createEmptyOp {block : BlockPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    (block.get! ctx').firstOp = (block.get! ctx).firstOp := by
  grind

grind_pattern BlockPtr.firstOp!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), (block.get! ctx').firstOp

@[simp]
theorem BlockPtr.lastOp!_createEmptyOp {block : BlockPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    (block.get! ctx').lastOp = (block.get! ctx).lastOp := by
  grind

grind_pattern BlockPtr.lastOp!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), (block.get! ctx').lastOp

theorem OperationPtr.prev!_createEmptyOp {operation : OperationPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    (operation.get! ctx').prev =
    if operation = op then none else (operation.get! ctx).prev := by
  grind [Operation.empty]

grind_pattern OperationPtr.prev!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), (operation.get! ctx').prev

theorem OperationPtr.next!_createEmptyOp {operation : OperationPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    (operation.get! ctx').next =
    if operation = op then none else (operation.get! ctx).next := by
  grind [Operation.empty]

grind_pattern OperationPtr.next!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), (operation.get! ctx').next

theorem OperationPtr.parent!_createEmptyOp {operation : OperationPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    (operation.get! ctx').parent =
    if operation = op then none else (operation.get! ctx).parent := by
  grind [Operation.empty]

grind_pattern OperationPtr.parent!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), (operation.get! ctx').parent

theorem OperationPtr.opType!_createEmptyOp {operation : OperationPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    (operation.get! ctx').opType =
    if operation = op then opType else (operation.get! ctx).opType := by
  grind [Operation.empty]

grind_pattern OperationPtr.opType!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), (operation.get! ctx').opType

theorem OperationPtr.attrs!_createEmptyOp {operation : OperationPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    (operation.get! ctx').attrs =
    if operation = op then DictionaryAttr.empty else (operation.get! ctx).attrs := by
  grind [Operation.empty]

grind_pattern OperationPtr.attrs!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), (operation.get! ctx').attrs

theorem OperationPtr.getProperties!_createEmptyOp {operation : OperationPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operation.getProperties! ctx' opType = if operation = op then properties else operation.getProperties! ctx opType := by
  grind [Operation.empty]

grind_pattern OperationPtr.getProperties!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operation.getProperties! ctx' opType

theorem OperationPtr.getNumResults!_createEmptyOp {operation : OperationPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operation.getNumResults! ctx' =
    if operation = op then 0 else operation.getNumResults! ctx := by
  grind [Operation.empty]

grind_pattern OperationPtr.getNumResults!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operation.getNumResults! ctx'

@[simp]
theorem OpResultPtr.get!_createEmptyOp {opResult : OpResultPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    opResult.get! ctx' = opResult.get! ctx := by
  grind

grind_pattern OpResultPtr.get!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), opResult.get! ctx'

theorem OperationPtr.getNumOperands!_createEmptyOp {operation : OperationPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operation.getNumOperands! ctx' =
    if operation = op then 0 else operation.getNumOperands! ctx := by
  grind

grind_pattern OperationPtr.getNumOperands!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operation.getNumOperands! ctx'

@[simp]
theorem OpOperandPtr.get!_createEmptyOp {operand : OpOperandPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operand.get! ctx' = operand.get! ctx := by
  grind

grind_pattern OpOperandPtr.get!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operand.get! ctx'

theorem OperationPtr.getOperands!_createEmptyOp {operation : OperationPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operation.getOperands! ctx' =
    if operation = op then #[] else operation.getOperands! ctx := by
  grind

grind_pattern OperationPtr.getOperands!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operation.getOperands! ctx'

theorem OperationPtr.getNumSuccessors!_createEmptyOp {operation : OperationPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operation.getNumSuccessors! ctx' =
    if operation = op then 0 else operation.getNumSuccessors! ctx := by
  grind

grind_pattern OperationPtr.getNumSuccessors!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operation.getNumSuccessors! ctx'

@[simp]
theorem BlockOperandPtr.get!_createEmptyOp {operand : BlockOperandPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operand.get! ctx' = operand.get! ctx := by
  grind

grind_pattern BlockOperandPtr.get!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operand.get! ctx'

@[simp]
theorem OperationPtr.getSuccessor!_createEmptyOp {operation : OperationPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operation.getSuccessor! ctx' index = operation.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def]

grind_pattern OperationPtr.getSuccessor!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operation.getSuccessor! ctx' index

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

theorem OperationPtr.getNumRegions!_createEmptyOp {operation : OperationPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operation.getNumRegions! ctx' =
    if operation = op then 0 else operation.getNumRegions! ctx := by
  grind

grind_pattern OperationPtr.getNumRegions!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operation.getNumRegions! ctx'

@[simp]
theorem OperationPtr.getRegion!_createEmptyOp {operation : OperationPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operation.getRegion! ctx' idx = operation.getRegion! ctx idx := by
  grind

grind_pattern OperationPtr.getRegion!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operation.getRegion! ctx' idx

@[simp]
theorem BlockOperandPtrPtr.get!_createEmptyOp {operandPtr : BlockOperandPtrPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operandPtr.get! ctx' = operandPtr.get! ctx := by
  grind

grind_pattern BlockOperandPtrPtr.get!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operandPtr.get! ctx'

@[simp]
theorem BlockPtr.getNumArguments!_createEmptyOp {block : BlockPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    block.getNumArguments! ctx' = block.getNumArguments! ctx := by
  grind

grind_pattern BlockPtr.getNumArguments!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), block.getNumArguments! ctx'

@[simp]
theorem BlockArgumentPtr.get!_createEmptyOp {blockArg : BlockArgumentPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    blockArg.get! ctx' = blockArg.get! ctx := by
  grind

grind_pattern BlockArgumentPtr.get!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), blockArg.get! ctx'

@[simp]
theorem RegionPtr.firstBlock!_createEmptyOp {region : RegionPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    (region.get! ctx').firstBlock = (region.get! ctx).firstBlock := by
  grind

grind_pattern RegionPtr.firstBlock!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), (region.get! ctx').firstBlock

@[simp]
theorem RegionPtr.lastBlock!_createEmptyOp {region : RegionPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    (region.get! ctx').lastBlock = (region.get! ctx).lastBlock := by
  grind

grind_pattern RegionPtr.lastBlock!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), (region.get! ctx').lastBlock

@[simp]
theorem RegionPtr.parent!_createEmptyOp {region : RegionPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    (region.get! ctx').parent = (region.get! ctx).parent := by
  grind

grind_pattern RegionPtr.parent!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), (region.get! ctx').parent

@[simp]
theorem ValuePtr.getFirstUse!_createEmptyOp {value : ValuePtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    value.getFirstUse! ctx' = value.getFirstUse! ctx := by
  grind

grind_pattern ValuePtr.getFirstUse!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), value.getFirstUse! ctx'

@[simp]
theorem ValuePtr.getType!_createEmptyOp {value : ValuePtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    value.getType! ctx' = value.getType! ctx := by
  grind

grind_pattern ValuePtr.getType!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), value.getType! ctx'

@[simp]
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

@[simp, grind =>]
theorem BlockPtr.prev!_createOp {block : BlockPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    (block.get! ctx').prev = (block.get! ctx).prev := by
  grind (gen := 20)

@[simp, grind =>]
theorem BlockPtr.next!_createOp {block : BlockPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    (block.get! ctx').next = (block.get! ctx).next := by
  grind (gen := 20)

@[simp, grind =>]
theorem BlockPtr.parent!_createOp {block : BlockPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    (block.get! ctx').parent = (block.get! ctx).parent := by
  grind (gen := 20)

@[grind =>]
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
  grind (gen := 20) [cases InsertPoint]

@[grind =>]
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
  grind (gen := 20) [cases InsertPoint]

@[grind =>]
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
  grind (gen := 20) [cases InsertPoint]

@[grind =>]
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
  grind (gen := 20) (splits := 20) [cases InsertPoint]

@[grind =>]
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
  grind (gen := 20) [cases InsertPoint, Operation.empty]

@[grind =>]
theorem OperationPtr.opType!_createOp {operation : OperationPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    (operation.get! ctx').opType =
    if operation = newOp then opType else (operation.get! ctx).opType := by
  simp only [Rewriter.createOp]
  grind (gen := 20)

@[grind =>]
theorem OperationPtr.attrs!_createOp {operation : OperationPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    (operation.get! ctx').attrs =
    if operation = newOp then DictionaryAttr.empty else (operation.get! ctx).attrs := by
  simp only [Rewriter.createOp]
  grind (gen := 20)

@[grind =>]
theorem OperationPtr.getProperties!_createOp {operation : OperationPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    operation.getProperties! ctx' opType =
    if operation = newOp then properties else operation.getProperties! ctx opType := by
  simp only [Rewriter.createOp]
  grind (gen := 20)

@[grind =>]
theorem OperationPtr.getNumResults!_createOp {operation : OperationPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    operation.getNumResults! ctx' =
    if operation = newOp then resultTypes.size else operation.getNumResults! ctx := by
  simp only [Rewriter.createOp]
  grind (gen := 20)

/-
OpResultPtr.get!_createOp is too complex to be expressed, and should not be needed in practice,
as we should reason at a higher-level abstraction at this point.
-/

@[grind =>]
theorem OperationPtr.getNumOperands!_createOp {operation : OperationPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    operation.getNumOperands! ctx' =
    if operation = newOp then operands.size else operation.getNumOperands! ctx := by
  simp only [Rewriter.createOp]
  grind (gen := 20)

/-
OpOperandPtr.get!_createOp is too complex to be expressed, and should not be needed in practice,
as we should reason at a higher-level abstraction at this point.
-/

@[grind =>]
theorem OperationPtr.getOperands!_createOp {operation : OperationPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    operation.getOperands! ctx' =
    if operation = newOp then operands else operation.getOperands! ctx := by
  simp only [Rewriter.createOp]
  grind (gen := 20)

@[grind =>]
theorem OperationPtr.getNumSuccessors!_createOp {operation : OperationPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    operation.getNumSuccessors! ctx' =
    if operation = newOp then blockOperands.size else operation.getNumSuccessors! ctx := by
  grind (gen := 20)

/-
BlockOperandPtr.get!_createOp is too complex to be expressed, and should not be needed in practice,
as we should reason at a higher-level abstraction at this point.
-/

@[grind =>]
theorem OperationPtr.getSuccessor!_createOp {operation : OperationPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    operation.getSuccessor! ctx' index =
    if operation = newOp then blockOperands[index]!
    else operation.getSuccessor! ctx index := by
  simp only [Rewriter.createOp]
  grind (gen := 20)

@[grind =>]
theorem OperationPtr.getSuccessors!_createOp {operation : OperationPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    operation.getSuccessors! ctx' =
    if operation = newOp then blockOperands else operation.getSuccessors! ctx := by
  grind (gen := 20)

@[grind =>]
theorem OperationPtr.getNumRegions!_createOp {operation : OperationPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    operation.getNumRegions! ctx' =
    if operation = newOp then regions.size else operation.getNumRegions! ctx := by
  grind (gen := 20)

@[grind =>]
theorem OperationPtr.getRegion!_createOp {operation : OperationPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    operation.getRegion! ctx' idx =
    if _ : operation = newOp ∧ idx < regions.size then regions[idx]
    else operation.getRegion! ctx idx := by
  grind (gen := 20)

/-
BlockOperandPtrPtr.get!_createOp is too complex to be expressed, and should not be needed in practice,
as we should reason at a higher-level abstraction at this point.
-/

@[simp, grind =>]
theorem BlockPtr.getNumArguments!_createOp {block : BlockPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    block.getNumArguments! ctx' = block.getNumArguments! ctx := by
  grind (gen := 20)

/-
BlockArgumentPtr.get!_createOp is too complex to be expressed, and should not be needed in practice,
as we should reason at a higher-level abstraction at this point.
-/

@[simp, grind =>]
theorem RegionPtr.firstBlock!_createOp {region : RegionPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    (region.get! ctx').firstBlock = (region.get! ctx).firstBlock := by
  grind (gen := 20)

@[simp, grind =>]
theorem RegionPtr.lastBlock!_createOp {region : RegionPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    (region.get! ctx').lastBlock = (region.get! ctx).lastBlock := by
  grind (gen := 20)

@[simp, grind =>]
theorem RegionPtr.parent!_createOp {region : RegionPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    (region.get! ctx').parent =
    if region ∈ regions then some newOp else (region.get! ctx).parent := by
  grind (gen := 20)

/-
ValuePtr.getFirstUse!_createOp is too complex to be expressed, and should not be needed in practice,
as we should reason at a higher-level abstraction at this point.
-/

@[grind =>]
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
  grind (gen := 20)

/-
OpOperandPtrPtr.get!_createOp is too complex to be expressed, and should not be needed in practice,
as we should reason at a higher-level abstraction at this point.
-/

end Rewriter.createOp

/- replaceValue? -/

@[simp, grind .]
theorem OperationPtr.getNumOperands_iff_replaceValue?
    (hctx' : Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some ctx') :
    OperationPtr.getNumOperands op ctx' h_op =
    OperationPtr.getNumOperands op ctx (by grind) := by
  grind [OpOperandPtr.inBounds_if_operand_size_eq]

@[grind →]
theorem IRContext.create_fieldsInBounds {op: OperationPtr} (h : IRContext.create OpInfo = some (ctx, op)) :
    ctx.FieldsInBounds ∧ op.InBounds ctx := by
  simp only [IRContext.create] at h
  constructor <;> grind (gen := 10)

end Veir
