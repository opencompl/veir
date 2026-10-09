module

public import Veir.Rewriter.Basic

import all Veir.Rewriter.Basic
import all Veir.IR.Basic
import all Veir.IR.GetSet
import all Veir.Rewriter.LinkedList.GetSet
import Veir.Rewriter.WfRewriter.GetSetTactic

import all Veir.Rewriter.GetSet.Operands
import all Veir.Rewriter.GetSet.BlockOperands
import all Veir.Rewriter.GetSet.InsertOp
import all Veir.Rewriter.GetSet.Results
import all Veir.Rewriter.GetSet.Regions

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
    block.getFirstUse! ctx' = block.getFirstUse! ctx := by
  grind

grind_pattern BlockPtr.firstUse!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), block.getFirstUse! ctx'

@[simp, simp_getset]
theorem BlockPtr.prev!_createEmptyOp {block : BlockPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    block.getPrevBlock! ctx' = block.getPrevBlock! ctx := by
  grind

grind_pattern BlockPtr.prev!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), block.getPrevBlock! ctx'

@[simp, simp_getset]
theorem BlockPtr.next!_createEmptyOp {block : BlockPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    block.getNextBlock! ctx' = block.getNextBlock! ctx := by
  grind

grind_pattern BlockPtr.next!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), block.getNextBlock! ctx'

@[simp, simp_getset]
theorem BlockPtr.parent!_createEmptyOp {block : BlockPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    block.getParent! ctx' = block.getParent! ctx := by
  grind

grind_pattern BlockPtr.parent!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), block.getParent! ctx'

@[simp, simp_getset]
theorem BlockPtr.firstOp!_createEmptyOp {block : BlockPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    block.getFirstOp! ctx' = block.getFirstOp! ctx := by
  grind

grind_pattern BlockPtr.firstOp!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), block.getFirstOp! ctx'

@[simp, simp_getset]
theorem BlockPtr.lastOp!_createEmptyOp {block : BlockPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    block.getLastOp! ctx' = block.getLastOp! ctx := by
  grind

grind_pattern BlockPtr.lastOp!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), block.getLastOp! ctx'

@[simp_getset]
theorem OperationPtr.prev!_createEmptyOp {operation : OperationPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operation.getPrevOp! ctx' =
    if operation = op then none else (operation.getPrevOp! ctx) := by
  grind [Operation.empty]

grind_pattern OperationPtr.prev!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operation.getPrevOp! ctx'

@[simp_getset]
theorem OperationPtr.next!_createEmptyOp {operation : OperationPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operation.getNextOp! ctx' =
    if operation = op then none else (operation.getNextOp! ctx) := by
  grind [Operation.empty]

grind_pattern OperationPtr.next!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operation.getNextOp! ctx'

@[simp_getset]
theorem OperationPtr.parent!_createEmptyOp {operation : OperationPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operation.getParent! ctx' =
    if operation = op then none else (operation.getParent! ctx) := by
  grind [Operation.empty]

grind_pattern OperationPtr.parent!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operation.getParent! ctx'

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
    operation.getAttributes! ctx' =
    if operation = op then DictionaryAttr.empty else (operation.getAttributes! ctx) := by
  grind [Operation.empty]

grind_pattern OperationPtr.attrs!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operation.getAttributes! ctx'

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
private theorem OpResultPtr.get!_createEmptyOp {opResult : OpResultPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    opResult.get! ctx' = opResult.get! ctx := by
  grind

grind_pattern OpResultPtr.get!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), opResult.get! ctx'

@[simp, simp_getset]
theorem OpResultPtr.getIndex!_createEmptyOp {opResult : OpResultPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    opResult.getIndex! ctx' =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

grind_pattern OpResultPtr.getIndex!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), opResult.getIndex! ctx'

@[simp, simp_getset]
theorem OpResultPtr.getType!_createEmptyOp {opResult : OpResultPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    opResult.getType! ctx' =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

grind_pattern OpResultPtr.getType!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), opResult.getType! ctx'

@[simp, simp_getset]
theorem OpResultPtr.getFirstUse!_createEmptyOp {opResult : OpResultPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    opResult.getFirstUse! ctx' =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

grind_pattern OpResultPtr.getFirstUse!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), opResult.getFirstUse! ctx'

@[simp, simp_getset]
theorem OpResultPtr.getOwner!_createEmptyOp {opResult : OpResultPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    opResult.getOwner! ctx' =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

grind_pattern OpResultPtr.getOwner!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), opResult.getOwner! ctx'

@[simp_getset]
theorem OperationPtr.getNumOperands!_createEmptyOp {operation : OperationPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operation.getNumOperands! ctx' =
    if operation = op then 0 else operation.getNumOperands! ctx := by
  grind

grind_pattern OperationPtr.getNumOperands!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operation.getNumOperands! ctx'

@[simp, simp_getset]
private theorem OpOperandPtr.get!_createEmptyOp {operand : OpOperandPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operand.get! ctx' = operand.get! ctx := by
  grind

grind_pattern OpOperandPtr.get!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operand.get! ctx'

@[simp, simp_getset]
theorem OpOperandPtr.getNextUse!_createEmptyOp {operand : OpOperandPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operand.getNextUse! ctx' =
    operand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

grind_pattern OpOperandPtr.getNextUse!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operand.getNextUse! ctx'

@[simp, simp_getset]
theorem OpOperandPtr.getBack!_createEmptyOp {operand : OpOperandPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operand.getBack! ctx' =
    operand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

grind_pattern OpOperandPtr.getBack!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operand.getBack! ctx'

@[simp, simp_getset]
theorem OpOperandPtr.getOwner!_createEmptyOp {operand : OpOperandPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operand.getOwner! ctx' =
    operand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

grind_pattern OpOperandPtr.getOwner!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operand.getOwner! ctx'

@[simp, simp_getset]
theorem OpOperandPtr.getValue!_createEmptyOp {operand : OpOperandPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operand.getValue! ctx' =
    operand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

grind_pattern OpOperandPtr.getValue!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operand.getValue! ctx'

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

@[simp_getset]
theorem OperationPtr.getBlockOperands!_createEmptyOp {operation : OperationPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operation.getBlockOperands! ctx' =
    if operation = op then #[] else operation.getBlockOperands! ctx := by
  simp only [OperationPtr.getBlockOperands!_def]
  grind

grind_pattern OperationPtr.getBlockOperands!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operation.getBlockOperands! ctx'

@[simp, simp_getset]
private theorem BlockOperandPtr.get!_createEmptyOp {operand : BlockOperandPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operand.get! ctx' = operand.get! ctx := by
  grind

grind_pattern BlockOperandPtr.get!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operand.get! ctx'

@[simp, simp_getset]
theorem BlockOperandPtr.getNextUse!_createEmptyOp {operand : BlockOperandPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operand.getNextUse! ctx' =
    operand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

grind_pattern BlockOperandPtr.getNextUse!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operand.getNextUse! ctx'

@[simp, simp_getset]
theorem BlockOperandPtr.getBack!_createEmptyOp {operand : BlockOperandPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operand.getBack! ctx' =
    operand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

grind_pattern BlockOperandPtr.getBack!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operand.getBack! ctx'

@[simp, simp_getset]
theorem BlockOperandPtr.getOwner!_createEmptyOp {operand : BlockOperandPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operand.getOwner! ctx' =
    operand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

grind_pattern BlockOperandPtr.getOwner!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operand.getOwner! ctx'

@[simp, simp_getset]
theorem BlockOperandPtr.getValue!_createEmptyOp {operand : BlockOperandPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    operand.getValue! ctx' =
    operand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

grind_pattern BlockOperandPtr.getValue!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), operand.getValue! ctx'

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
private theorem BlockOperandPtrPtr.get!_createEmptyOp {operandPtr : BlockOperandPtrPtr} :
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
theorem BlockPtr.getBlockArguments!_createEmptyOp {block : BlockPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    block.getBlockArguments! ctx' =
    block.getBlockArguments! ctx := by
  simp only [BlockPtr.getBlockArguments!_def]
  grind

grind_pattern BlockPtr.getBlockArguments!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), block.getBlockArguments! ctx'

@[simp, simp_getset]
private theorem BlockArgumentPtr.get!_createEmptyOp {blockArg : BlockArgumentPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    blockArg.get! ctx' = blockArg.get! ctx := by
  grind

grind_pattern BlockArgumentPtr.get!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), blockArg.get! ctx'

@[simp, simp_getset]
theorem BlockArgumentPtr.getType!_createEmptyOp {blockArg : BlockArgumentPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    blockArg.getType! ctx' =
    blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

grind_pattern BlockArgumentPtr.getType!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), blockArg.getType! ctx'

@[simp, simp_getset]
theorem BlockArgumentPtr.getFirstUse!_createEmptyOp {blockArg : BlockArgumentPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    blockArg.getFirstUse! ctx' =
    blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

grind_pattern BlockArgumentPtr.getFirstUse!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), blockArg.getFirstUse! ctx'

@[simp, simp_getset]
theorem BlockArgumentPtr.getIndex!_createEmptyOp {blockArg : BlockArgumentPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    blockArg.getIndex! ctx' =
    blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

grind_pattern BlockArgumentPtr.getIndex!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), blockArg.getIndex! ctx'

@[simp, simp_getset]
theorem BlockArgumentPtr.getLoc!_createEmptyOp {blockArg : BlockArgumentPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    blockArg.getLoc! ctx' =
    blockArg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

grind_pattern BlockArgumentPtr.getLoc!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), blockArg.getLoc! ctx'

@[simp, simp_getset]
theorem BlockArgumentPtr.getOwner!_createEmptyOp {blockArg : BlockArgumentPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    blockArg.getOwner! ctx' =
    blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

grind_pattern BlockArgumentPtr.getOwner!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), blockArg.getOwner! ctx'

@[simp, simp_getset]
theorem RegionPtr.firstBlock!_createEmptyOp {region : RegionPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    region.getFirstBlock! ctx' = region.getFirstBlock! ctx := by
  grind

grind_pattern RegionPtr.firstBlock!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), region.getFirstBlock! ctx'

@[simp, simp_getset]
theorem RegionPtr.lastBlock!_createEmptyOp {region : RegionPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    region.getLastBlock! ctx' = region.getLastBlock! ctx := by
  grind

grind_pattern RegionPtr.lastBlock!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), region.getLastBlock! ctx'

@[simp, simp_getset]
theorem RegionPtr.parent!_createEmptyOp {region : RegionPtr} :
    Rewriter.createEmptyOp ctx opType properties = some (ctx', op) →
    region.getParent! ctx' = region.getParent! ctx := by
  grind

grind_pattern RegionPtr.parent!_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (ctx', op), region.getParent! ctx'

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
private theorem OpOperandPtrPtr.get!_createEmptyOp {opOperandPtr : OpOperandPtrPtr} :
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
    block.getPrevBlock! ctx' = block.getPrevBlock! ctx := by
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
    block.getNextBlock! ctx' = block.getNextBlock! ctx := by
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
    block.getParent! ctx' = block.getParent! ctx := by
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
    block.getFirstOp! ctx' =
    match insertionPoint with
    | some ip =>
      if ip.block! ctx = block ∧ ip.prev! ctx = none then some newOp
      else (block.getFirstOp! ctx)
    | none => block.getFirstOp! ctx := by
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
    block.getLastOp! ctx' =
    match insertionPoint with
    | some ip =>
      if ip.block! ctx = block ∧ ip.next = none then some newOp
      else (block.getLastOp! ctx)
    | none => block.getLastOp! ctx := by
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
    operation.getPrevOp! ctx' =
    match insertionPoint with
    | some ip =>
      if operation = newOp then ip.prev! ctx
      else if operation = ip.next then some newOp
      else (operation.getPrevOp! ctx)
    | none =>
      if operation = newOp then none else (operation.getPrevOp! ctx) := by
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
    operation.getNextOp! ctx' =
    match insertionPoint with
    | some ip =>
      if operation = newOp then ip.next
      else if operation = ip.prev! ctx then some newOp
      else (operation.getNextOp! ctx)
    | none =>
      if operation = newOp then none else (operation.getNextOp! ctx) := by
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
        by_cases hop' : some operation = op.getPrevOp! ctx
        · simp only [hop', ↓reduceIte, right_eq_ite_iff, Option.some.injEq]
          grind
        · simp only [hop', ↓reduceIte]
          by_cases hop'' : operation = newOpPtr <;> simp_all
    case atEnd block =>
      simp only [InsertPoint.prev_atEnd_eq, BlockPtr.lastOp!_initBlockOperands,
        BlockPtr.lastOp!_initOpOperands, InsertPoint.next_atEnd_eq]
      by_cases hop : some operation = block.getLastOp! ctx₂; grind
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
    operation.getParent! ctx' =
    if operation = newOp then
      match insertionPoint with
      | some ip => ip.block! ctx
      | none => none
    else (operation.getParent! ctx) := by
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
    operation.getAttributes! ctx' =
    if operation = newOp then DictionaryAttr.empty else (operation.getAttributes! ctx) := by
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

@[grind =>, simp_getset]
theorem OperationPtr.getBlockOperands!_createOp {operation : OperationPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    operation.getBlockOperands! ctx' =
    if operation = newOp then Array.map operation.getBlockOperand (Array.range blockOperands.size)
    else operation.getBlockOperands! ctx := by
  simp only [OperationPtr.getBlockOperands!_def]
  grind

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

@[simp, grind =>, simp_getset]
theorem BlockPtr.getBlockArguments!_createOp {block : BlockPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    block.getBlockArguments! ctx' =
    block.getBlockArguments! ctx := by
  simp only [BlockPtr.getBlockArguments!_def]
  grind

/-
BlockArgumentPtr.get!_createOp is too complex to be expressed, and should not be needed in practice,
as we should reason at a higher-level abstraction at this point.
-/

@[simp, grind =>, simp_getset]
theorem RegionPtr.firstBlock!_createOp {region : RegionPtr} :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint h₁ h₂ h₃ h₄ h₅ = some (ctx', newOp) →
    region.getFirstBlock! ctx' = region.getFirstBlock! ctx := by
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
    region.getLastBlock! ctx' = region.getLastBlock! ctx := by
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
    region.getParent! ctx' =
    if region ∈ regions then some newOp else (region.getParent! ctx) := by
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
