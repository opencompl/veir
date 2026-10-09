module

public import Veir.Rewriter.Basic

import all Veir.Rewriter.Basic
import all Veir.IR.Basic
import all Veir.IR.GetSet
import all Veir.Rewriter.LinkedList.GetSet
import Veir.Rewriter.WfRewriter.GetSetTactic


public section

namespace Veir

variable {OpInfo} [HasOpInfo OpInfo]

-- Relate the getters to the fields of the underlying structures.
attribute [local grind _=_]
  OperationPtr.getNextOp!_def OperationPtr.getPrevOp!_def OperationPtr.getParent!_def
  OperationPtr.getAttributes!_def OpOperandPtr.getNextUse!_def OpOperandPtr.getBack!_def
  OpOperandPtr.getOwner!_def OpOperandPtr.getValue!_def BlockOperandPtr.getNextUse!_def
  BlockOperandPtr.getBack!_def BlockOperandPtr.getOwner!_def BlockOperandPtr.getValue!_def
  OpResultPtr.getType!_def OpResultPtr.getFirstUse!_def OpResultPtr.getOwner!_def
  BlockPtr.getParent!_def BlockPtr.getFirstUse!_def BlockPtr.getFirstOp!_def
  BlockPtr.getLastOp!_def BlockPtr.getNextBlock!_def BlockPtr.getPrevBlock!_def
  BlockArgumentPtr.getType!_def BlockArgumentPtr.getFirstUse!_def
  BlockArgumentPtr.getIndex!_def BlockArgumentPtr.getLoc!_def
  BlockArgumentPtr.getOwner!_def RegionPtr.getParent!_def RegionPtr.getFirstBlock!_def
  RegionPtr.getLastBlock!_def OpResultPtr.getIndex!_def
variable {ctx : IRContext OpInfo}
section Rewriter.insertBlock

unseal Rewriter.insertBlock

attribute [local grind] Rewriter.insertBlock

@[simp, simp_getset]
theorem BlockPtr.firstUse!_insertBlock {block : BlockPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    block.getFirstUse! newCtx = block.getFirstUse! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern BlockPtr.firstUse!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, block.getFirstUse! newCtx

@[simp_getset]
theorem BlockPtr.prev!_insertBlock {block : BlockPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    block.getPrevBlock! newCtx =
      if block = ip.next then
        some newBlock
      else if block = newBlock then
        ip.prev! ctx
      else
        block.getPrevBlock! ctx := by
  simp only [Rewriter.insertBlock]
  grind [cases BlockInsertPoint]

grind_pattern BlockPtr.prev!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, block.getPrevBlock! newCtx

@[simp_getset]
theorem BlockPtr.next!_insertBlock {block : BlockPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    block.getNextBlock! newCtx =
      if block = ip.prev! ctx then
        some newBlock
      else if block = newBlock then
        ip.next
      else
        block.getNextBlock! ctx := by
  simp only [Rewriter.insertBlock]
  grind [cases BlockInsertPoint]

grind_pattern BlockPtr.next!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, block.getNextBlock! newCtx

@[simp_getset]
theorem BlockPtr.parent!_insertBlock {block : BlockPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    block.getParent! newCtx =
      if block = newBlock then
        ip.region! ctx
      else
      block.getParent! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern BlockPtr.parent!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, block.getParent! newCtx

@[simp, simp_getset]
theorem BlockPtr.firstOp!_insertBlock {block : BlockPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    block.getFirstOp! newCtx = block.getFirstOp! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern BlockPtr.firstOp!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, block.getFirstOp! newCtx

@[simp, simp_getset]
theorem BlockPtr.lastOp!_insertBlock {block : BlockPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    block.getLastOp! newCtx = block.getLastOp! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern BlockPtr.lastOp!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, block.getLastOp! newCtx

@[simp, simp_getset]
private theorem OperationPtr.get!_insertBlock {operation : OperationPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.get! newCtx = operation.get! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern OperationPtr.get!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.get! newCtx

@[simp, simp_getset]
theorem OperationPtr.getNextOp!_insertBlock {operation : OperationPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.getNextOp! newCtx =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

grind_pattern OperationPtr.getNextOp!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getNextOp! newCtx

@[simp, simp_getset]
theorem OperationPtr.getPrevOp!_insertBlock {operation : OperationPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.getPrevOp! newCtx =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

grind_pattern OperationPtr.getPrevOp!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getPrevOp! newCtx

@[simp, simp_getset]
theorem OperationPtr.getParent!_insertBlock {operation : OperationPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.getParent! newCtx =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

grind_pattern OperationPtr.getParent!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getParent! newCtx

@[simp, simp_getset]
theorem OperationPtr.getAttributes!_insertBlock {operation : OperationPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.getAttributes! newCtx =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  grind

grind_pattern OperationPtr.getAttributes!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getAttributes! newCtx

@[simp, simp_getset]
theorem OperationPtr.getOpType!_insertBlock {operation : OperationPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.getOpType! newCtx = operation.getOpType! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern OperationPtr.getOpType!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getOpType! newCtx

@[simp, simp_getset]
theorem OperationPtr.getNumResults!_insertBlock {operation : OperationPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.getNumResults! newCtx = operation.getNumResults! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern OperationPtr.getNumResults!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getNumResults! newCtx

@[simp, simp_getset]
private theorem OpResultPtr.get!_insertBlock {opResult : OpResultPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    opResult.get! newCtx = opResult.get! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern OpResultPtr.get!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, opResult.get! newCtx

@[simp, simp_getset]
theorem OpResultPtr.getIndex!_insertBlock {opResult : OpResultPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    opResult.getIndex! newCtx =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

grind_pattern OpResultPtr.getIndex!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, opResult.getIndex! newCtx

@[simp, simp_getset]
theorem OpResultPtr.getType!_insertBlock {opResult : OpResultPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    opResult.getType! newCtx =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

grind_pattern OpResultPtr.getType!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, opResult.getType! newCtx

@[simp, simp_getset]
theorem OpResultPtr.getFirstUse!_insertBlock {opResult : OpResultPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    opResult.getFirstUse! newCtx =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

grind_pattern OpResultPtr.getFirstUse!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, opResult.getFirstUse! newCtx

@[simp, simp_getset]
theorem OpResultPtr.getOwner!_insertBlock {opResult : OpResultPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    opResult.getOwner! newCtx =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

grind_pattern OpResultPtr.getOwner!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, opResult.getOwner! newCtx

@[simp, simp_getset]
theorem OperationPtr.getNumOperands!_insertBlock {operation : OperationPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.getNumOperands! newCtx = operation.getNumOperands! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern OperationPtr.getNumOperands!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getNumOperands! newCtx

@[simp, simp_getset]
private theorem OpOperandPtr.get!_insertBlock {operand : OpOperandPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operand.get! newCtx = operand.get! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern OpOperandPtr.get!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operand.get! newCtx

@[simp, simp_getset]
theorem OpOperandPtr.getNextUse!_insertBlock {operand : OpOperandPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operand.getNextUse! newCtx =
    operand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

grind_pattern OpOperandPtr.getNextUse!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operand.getNextUse! newCtx

@[simp, simp_getset]
theorem OpOperandPtr.getBack!_insertBlock {operand : OpOperandPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operand.getBack! newCtx =
    operand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

grind_pattern OpOperandPtr.getBack!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operand.getBack! newCtx

@[simp, simp_getset]
theorem OpOperandPtr.getOwner!_insertBlock {operand : OpOperandPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operand.getOwner! newCtx =
    operand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

grind_pattern OpOperandPtr.getOwner!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operand.getOwner! newCtx

@[simp, simp_getset]
theorem OpOperandPtr.getValue!_insertBlock {operand : OpOperandPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operand.getValue! newCtx =
    operand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

grind_pattern OpOperandPtr.getValue!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operand.getValue! newCtx

@[simp, simp_getset]
theorem OperationPtr.getOperands!_insertBlock {operation : OperationPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.getOperands! newCtx = operation.getOperands! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern OperationPtr.getOperands!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getOperands! newCtx

@[simp, simp_getset]
theorem OperationPtr.getNumSuccessors!_insertBlock {operation : OperationPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.getNumSuccessors! newCtx = operation.getNumSuccessors! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern OperationPtr.getNumSuccessors!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getNumSuccessors! newCtx

@[simp, simp_getset]
theorem OperationPtr.getBlockOperands!_insertBlock {operation : OperationPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.getBlockOperands! newCtx =
    operation.getBlockOperands! ctx := by
  simp only [OperationPtr.getBlockOperands!_def]
  grind

grind_pattern OperationPtr.getBlockOperands!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getBlockOperands! newCtx

@[simp, simp_getset]
private theorem BlockOperandPtr.get!_insertBlock {operand : BlockOperandPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operand.get! newCtx = operand.get! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern BlockOperandPtr.get!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operand.get! newCtx

@[simp, simp_getset]
theorem BlockOperandPtr.getNextUse!_insertBlock {operand : BlockOperandPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operand.getNextUse! newCtx =
    operand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

grind_pattern BlockOperandPtr.getNextUse!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operand.getNextUse! newCtx

@[simp, simp_getset]
theorem BlockOperandPtr.getBack!_insertBlock {operand : BlockOperandPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operand.getBack! newCtx =
    operand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

grind_pattern BlockOperandPtr.getBack!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operand.getBack! newCtx

@[simp, simp_getset]
theorem BlockOperandPtr.getOwner!_insertBlock {operand : BlockOperandPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operand.getOwner! newCtx =
    operand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

grind_pattern BlockOperandPtr.getOwner!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operand.getOwner! newCtx

@[simp, simp_getset]
theorem BlockOperandPtr.getValue!_insertBlock {operand : BlockOperandPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operand.getValue! newCtx =
    operand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

grind_pattern BlockOperandPtr.getValue!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operand.getValue! newCtx

@[simp, simp_getset]
theorem OperationPtr.getSuccessor!_insertBlock {operation : OperationPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.getSuccessor! newCtx index = operation.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def]

grind_pattern OperationPtr.getSuccessor!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getSuccessor! newCtx index

@[simp, simp_getset]
theorem OperationPtr.getSuccessors!_insertBlock {operation : OperationPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.getSuccessors! newCtx = operation.getSuccessors! ctx := by
  grind [OperationPtr.getSuccessors!_def]

grind_pattern OperationPtr.getSuccessors!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getSuccessors! newCtx

@[simp, simp_getset]
theorem OperationPtr.getNumRegions!_insertBlock {operation : OperationPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.getNumRegions! newCtx = operation.getNumRegions! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern OperationPtr.getNumRegions!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getNumRegions! newCtx

@[simp, simp_getset]
theorem OperationPtr.getRegion!_insertBlock {operation : OperationPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.getRegion! newCtx = operation.getRegion! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern OperationPtr.getRegion!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getRegion! newCtx

@[simp, simp_getset]
private theorem BlockOperandPtrPtr.get!_insertBlock {operandPtr : BlockOperandPtrPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operandPtr.get! newCtx = operandPtr.get! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern BlockOperandPtrPtr.get!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operandPtr.get! newCtx

@[simp, simp_getset]
theorem BlockPtr.getNumArguments!_insertBlock {block : BlockPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    block.getNumArguments! newCtx = block.getNumArguments! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern BlockPtr.getNumArguments!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, block.getNumArguments! newCtx

@[simp, simp_getset]
theorem BlockPtr.getBlockArguments!_insertBlock {block : BlockPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    block.getBlockArguments! newCtx =
    block.getBlockArguments! ctx := by
  simp only [BlockPtr.getBlockArguments!_def]
  grind

grind_pattern BlockPtr.getBlockArguments!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, block.getBlockArguments! newCtx

@[simp, simp_getset]
private theorem BlockArgumentPtr.get!_insertBlock {blockArg : BlockArgumentPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    blockArg.get! newCtx = blockArg.get! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern BlockArgumentPtr.get!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, blockArg.get! newCtx

@[simp, simp_getset]
theorem BlockArgumentPtr.getType!_insertBlock {blockArg : BlockArgumentPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    blockArg.getType! newCtx =
    blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

grind_pattern BlockArgumentPtr.getType!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, blockArg.getType! newCtx

@[simp, simp_getset]
theorem BlockArgumentPtr.getFirstUse!_insertBlock {blockArg : BlockArgumentPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    blockArg.getFirstUse! newCtx =
    blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

grind_pattern BlockArgumentPtr.getFirstUse!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, blockArg.getFirstUse! newCtx

@[simp, simp_getset]
theorem BlockArgumentPtr.getIndex!_insertBlock {blockArg : BlockArgumentPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    blockArg.getIndex! newCtx =
    blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

grind_pattern BlockArgumentPtr.getIndex!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, blockArg.getIndex! newCtx

@[simp, simp_getset]
theorem BlockArgumentPtr.getLoc!_insertBlock {blockArg : BlockArgumentPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    blockArg.getLoc! newCtx =
    blockArg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

grind_pattern BlockArgumentPtr.getLoc!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, blockArg.getLoc! newCtx

@[simp, simp_getset]
theorem BlockArgumentPtr.getOwner!_insertBlock {blockArg : BlockArgumentPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    blockArg.getOwner! newCtx =
    blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

grind_pattern BlockArgumentPtr.getOwner!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, blockArg.getOwner! newCtx

@[simp_getset]
theorem RegionPtr.firstBlock!_insertBlock {region : RegionPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    region.getFirstBlock! newCtx =
      if ip.region! ctx = region ∧ ip.prev! ctx = none then
        some newBlock
      else
        region.getFirstBlock! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern RegionPtr.firstBlock!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, region.getFirstBlock! newCtx

@[simp_getset]
theorem RegionPtr.lastBlock!_insertBlock {region : RegionPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    region.getLastBlock! newCtx =
      if ip.region! ctx = region ∧ ip.next = none then
        some newBlock
      else
        region.getLastBlock! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern RegionPtr.lastBlock!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, region.getLastBlock! newCtx

@[simp, simp_getset]
theorem RegionPtr.parent!_insertBlock {region : RegionPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    region.getParent! newCtx = region.getParent! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern RegionPtr.parent!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, region.getParent! newCtx

@[simp, simp_getset]
theorem ValuePtr.getFirstUse!_insertBlock {value : ValuePtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    value.getFirstUse! newCtx = value.getFirstUse! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern ValuePtr.getFirstUse!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, value.getFirstUse! newCtx

@[simp, simp_getset]
theorem ValuePtr.getType!_insertBlock {value : ValuePtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    value.getType! newCtx = value.getType! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern ValuePtr.getType!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, value.getType! newCtx

@[simp, simp_getset]
private theorem OpOperandPtrPtr.get!_insertBlock {opOperandPtr : OpOperandPtrPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    opOperandPtr.get! newCtx = opOperandPtr.get! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern OpOperandPtrPtr.get!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, opOperandPtr.get! newCtx

end Rewriter.insertBlock

end Veir
