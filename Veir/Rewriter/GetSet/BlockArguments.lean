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
variable {Dialect : Type} [HasOpInfo Dialect] [HasDialect OpInfo Dialect]
variable {opCode : Dialect}

/-! ## `Rewriter.pushBlockArgument` -/

section Rewriter.pushBlockArgument

variable {block : BlockPtr}

attribute [local grind] Rewriter.pushBlockArgument

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstUse!_Rewriter_pushBlockArgument {block' : BlockPtr} :
    block'.getFirstUse! (Rewriter.pushBlockArgument ctx block type hblock) =
    block'.getFirstUse! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getPrevBlock!_Rewriter_pushBlockArgument {block' : BlockPtr} :
    block'.getPrevBlock! (Rewriter.pushBlockArgument ctx block type hblock) =
    block'.getPrevBlock! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNextBlock!_Rewriter_pushBlockArgument {block' : BlockPtr} :
    block'.getNextBlock! (Rewriter.pushBlockArgument ctx block type hblock) =
    block'.getNextBlock! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getParent!_Rewriter_pushBlockArgument {block' : BlockPtr} :
    block'.getParent! (Rewriter.pushBlockArgument ctx block type hblock) =
    block'.getParent! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstOp!_Rewriter_pushBlockArgument {block' : BlockPtr} :
    block'.getFirstOp! (Rewriter.pushBlockArgument ctx block type hblock) =
    block'.getFirstOp! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getLastOp!_Rewriter_pushBlockArgument {block' : BlockPtr} :
    block'.getLastOp! (Rewriter.pushBlockArgument ctx block type hblock) =
    block'.getLastOp! ctx := by
  grind

@[simp, grind =, simp_getset]
private theorem OperationPtr.get!_Rewriter_pushBlockArgument {operation : OperationPtr} :
    operation.get! (Rewriter.pushBlockArgument ctx block type hblock) =
    operation.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNextOp!_Rewriter_pushBlockArgument {operation : OperationPtr} :
    operation.getNextOp! (Rewriter.pushBlockArgument ctx block type hblock) =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getPrevOp!_Rewriter_pushBlockArgument {operation : OperationPtr} :
    operation.getPrevOp! (Rewriter.pushBlockArgument ctx block type hblock) =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getParent!_Rewriter_pushBlockArgument {operation : OperationPtr} :
    operation.getParent! (Rewriter.pushBlockArgument ctx block type hblock) =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getAttributes!_Rewriter_pushBlockArgument {operation : OperationPtr} :
    operation.getAttributes! (Rewriter.pushBlockArgument ctx block type hblock) =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOpType!_Rewriter_pushBlockArgument {operation : OperationPtr} :
    operation.getOpType! (Rewriter.pushBlockArgument ctx block type hblock) =
    operation.getOpType! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getProperties!_Rewriter_pushBlockArgument {operation : OperationPtr} :
    operation.getProperties! (Rewriter.pushBlockArgument ctx block type hblock) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumResults!_Rewriter_pushBlockArgument {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.pushBlockArgument ctx block type hblock) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =, simp_getset]
private theorem OpResultPtr.get!_Rewriter_pushBlockArgument {opResult : OpResultPtr} :
    opResult.get! (Rewriter.pushBlockArgument ctx block type hblock) =
    opResult.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getIndex!_Rewriter_pushBlockArgument {opResult : OpResultPtr} :
    opResult.getIndex! (Rewriter.pushBlockArgument ctx block type hblock) =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getType!_Rewriter_pushBlockArgument {opResult : OpResultPtr} :
    opResult.getType! (Rewriter.pushBlockArgument ctx block type hblock) =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getFirstUse!_Rewriter_pushBlockArgument {opResult : OpResultPtr} :
    opResult.getFirstUse! (Rewriter.pushBlockArgument ctx block type hblock) =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getOwner!_Rewriter_pushBlockArgument {opResult : OpResultPtr} :
    opResult.getOwner! (Rewriter.pushBlockArgument ctx block type hblock) =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumOperands!_Rewriter_pushBlockArgument {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.pushBlockArgument ctx block type hblock) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =, simp_getset]
private theorem OpOperandPtr.get!_Rewriter_pushBlockArgument {opOperand : OpOperandPtr} :
    opOperand.get! (Rewriter.pushBlockArgument ctx block type hblock) =
    opOperand.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getNextUse!_Rewriter_pushBlockArgument {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (Rewriter.pushBlockArgument ctx block type hblock) =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getBack!_Rewriter_pushBlockArgument {opOperand : OpOperandPtr} :
    opOperand.getBack! (Rewriter.pushBlockArgument ctx block type hblock) =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getOwner!_Rewriter_pushBlockArgument {opOperand : OpOperandPtr} :
    opOperand.getOwner! (Rewriter.pushBlockArgument ctx block type hblock) =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getValue!_Rewriter_pushBlockArgument {opOperand : OpOperandPtr} :
    opOperand.getValue! (Rewriter.pushBlockArgument ctx block type hblock) =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOperands!_Rewriter_pushBlockArgument {operation : OperationPtr} :
    operation.getOperands! (Rewriter.pushBlockArgument ctx block type hblock) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumSuccessors!_Rewriter_pushBlockArgument {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.pushBlockArgument ctx block type hblock) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =, simp_getset]
private theorem BlockOperandPtr.get!_Rewriter_pushBlockArgument {blockOperand : BlockOperandPtr} :
    blockOperand.get! (Rewriter.pushBlockArgument ctx block type hblock) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getNextUse!_Rewriter_pushBlockArgument {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (Rewriter.pushBlockArgument ctx block type hblock) =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getBack!_Rewriter_pushBlockArgument {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (Rewriter.pushBlockArgument ctx block type hblock) =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getOwner!_Rewriter_pushBlockArgument {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (Rewriter.pushBlockArgument ctx block type hblock) =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getValue!_Rewriter_pushBlockArgument {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (Rewriter.pushBlockArgument ctx block type hblock) =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessor!_Rewriter_pushBlockArgument {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.pushBlockArgument ctx block type hblock) index =
    operation.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def]

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessors!_Rewriter_pushBlockArgument {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.pushBlockArgument ctx block type hblock) =
    operation.getSuccessors! ctx := by
  grind [OperationPtr.getSuccessors!_def]

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumRegions!_Rewriter_pushBlockArgument {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.pushBlockArgument ctx block type hblock) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getRegion!_Rewriter_pushBlockArgument {operation : OperationPtr} :
    operation.getRegion! (Rewriter.pushBlockArgument ctx block type hblock) idx =
    operation.getRegion! ctx idx := by
  grind

@[simp, grind =, simp_getset]
private theorem BlockOperandPtrPtr.get!_Rewriter_pushBlockArgument {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (Rewriter.pushBlockArgument ctx block type hblock) =
    blockOperandPtr.get! ctx := by
  grind

@[grind =, simp_getset]
theorem BlockPtr.getNumArguments!_Rewriter_pushBlockArgument {block' : BlockPtr} :
    block'.getNumArguments! (Rewriter.pushBlockArgument ctx block type hblock) =
    if block = block' then
      block'.getNumArguments! ctx + 1
    else
      block'.getNumArguments! ctx := by
  grind

@[grind =, simp_getset]
private theorem BlockArgumentPtr.get!_Rewriter_pushBlockArgument {blockArg : BlockArgumentPtr} :
    blockArg.get! (Rewriter.pushBlockArgument ctx block type hblock) =
    if blockArg = block.nextArgument ctx then
      { type := type, firstUse := none, index := block.getNumArguments! ctx, owner := block, loc := ()}
    else
      blockArg.get! ctx := by
  grind

@[grind =, simp_getset]
theorem BlockArgumentPtr.getType!_Rewriter_pushBlockArgument {blockArg : BlockArgumentPtr} :
    blockArg.getType! (Rewriter.pushBlockArgument ctx block type hblock) =
    if blockArg = block.nextArgument ctx then type
    else blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[grind =, simp_getset]
theorem BlockArgumentPtr.getFirstUse!_Rewriter_pushBlockArgument {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (Rewriter.pushBlockArgument ctx block type hblock) =
    if blockArg = block.nextArgument ctx then none
    else blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[grind =, simp_getset]
theorem BlockArgumentPtr.getIndex!_Rewriter_pushBlockArgument {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (Rewriter.pushBlockArgument ctx block type hblock) =
    if blockArg = block.nextArgument ctx then
      block.getNumArguments! ctx
    else blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[grind =, simp_getset]
theorem BlockArgumentPtr.getLoc!_Rewriter_pushBlockArgument {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (Rewriter.pushBlockArgument ctx block type hblock) =
    if blockArg = block.nextArgument ctx then ()
    else blockArg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[grind =, simp_getset]
theorem BlockArgumentPtr.getOwner!_Rewriter_pushBlockArgument {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (Rewriter.pushBlockArgument ctx block type hblock) =
    if blockArg = block.nextArgument ctx then block
    else blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
private theorem RegionPtr.get!_Rewriter_pushBlockArgument {region : RegionPtr} :
    region.get! (Rewriter.pushBlockArgument ctx block type hblock) =
    region.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getParent!_Rewriter_pushBlockArgument {region : RegionPtr} :
    region.getParent! (Rewriter.pushBlockArgument ctx block type hblock) =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getFirstBlock!_Rewriter_pushBlockArgument {region : RegionPtr} :
    region.getFirstBlock! (Rewriter.pushBlockArgument ctx block type hblock) =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getLastBlock!_Rewriter_pushBlockArgument {region : RegionPtr} :
    region.getLastBlock! (Rewriter.pushBlockArgument ctx block type hblock) =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

@[grind =, simp_getset]
theorem ValuePtr.getFirstUse!_Rewriter_pushBlockArgument {value : ValuePtr} :
    value.getFirstUse! (Rewriter.pushBlockArgument ctx block type hblock) =
    if value = block.nextArgument ctx then
      none
    else
      value.getFirstUse! ctx := by
  grind

@[grind =, simp_getset]
theorem ValuePtr.getType!_Rewriter_pushBlockArgument {value : ValuePtr} :
    value.getType! (Rewriter.pushBlockArgument ctx block type hblock) =
    if value = block.nextArgument ctx then
      type
    else
      value.getType! ctx := by
  grind

@[grind =, simp_getset]
private theorem OpOperandPtrPtr.get!_Rewriter_pushBlockArgument {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.pushBlockArgument ctx block type hblock) =
    if opOperandPtr = OpOperandPtrPtr.valueFirstUse (block.nextArgument ctx) then
      none
    else
      opOperandPtr.get! ctx := by
  grind

end Rewriter.pushBlockArgument

/-! ## `Rewriter.initBlockArguments` -/

section Rewriter.initBlockArguments

variable {op : OperationPtr}

attribute [local grind] Rewriter.initBlockArguments

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstUse!_initBlockArguments {block' : BlockPtr} :
    block'.getFirstUse! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    block'.getFirstUse! ctx := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getPrevBlock!_initBlockArguments {block' : BlockPtr} :
    block'.getPrevBlock! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    block'.getPrevBlock! ctx := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNextBlock!_initBlockArguments {block' : BlockPtr} :
    block'.getNextBlock! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    block'.getNextBlock! ctx := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getParent!_initBlockArguments {block' : BlockPtr} :
    block'.getParent! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    block'.getParent! ctx := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstOp!_initBlockArguments {block' : BlockPtr} :
    block'.getFirstOp! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    block'.getFirstOp! ctx := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getLastOp!_initBlockArguments {block' : BlockPtr} :
    block'.getLastOp! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    block'.getLastOp! ctx := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[simp, grind =, simp_getset]
private theorem OperationPtr.get!_initBlockArguments {operation : OperationPtr} :
    operation.get! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    operation.get! ctx := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNextOp!_initBlockArguments {operation : OperationPtr} :
    operation.getNextOp! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getPrevOp!_initBlockArguments {operation : OperationPtr} :
    operation.getPrevOp! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getParent!_initBlockArguments {operation : OperationPtr} :
    operation.getParent! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getAttributes!_initBlockArguments {operation : OperationPtr} :
    operation.getAttributes! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOpType!_initBlockArguments {operation : OperationPtr} :
    operation.getOpType! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    operation.getOpType! ctx := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getProperties!_initBlockArguments {operation : OperationPtr} :
    operation.getProperties! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) opCode =
    operation.getProperties! ctx opCode := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumResults!_initBlockArguments {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    operation.getNumResults! ctx := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[simp, grind =, simp_getset]
private theorem OpResultPtr.get!_initBlockArguments {opResult : OpResultPtr} :
    opResult.get! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    opResult.get! ctx := by
  fun_induction Rewriter.initBlockArguments <;> grind [cases OpResultPtr]

@[simp, grind =, simp_getset]
theorem OpResultPtr.getIndex!_initBlockArguments {opResult : OpResultPtr} :
    opResult.getIndex! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getType!_initBlockArguments {opResult : OpResultPtr} :
    opResult.getType! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getFirstUse!_initBlockArguments {opResult : OpResultPtr} :
    opResult.getFirstUse! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getOwner!_initBlockArguments {opResult : OpResultPtr} :
    opResult.getOwner! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumOperands!_initBlockArguments {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    operation.getNumOperands! ctx := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[simp, grind =, simp_getset]
private theorem OpOperandPtr.get!_initBlockArguments {opOperand : OpOperandPtr}:
    opOperand.get! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) = opOperand.get! ctx := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getNextUse!_initBlockArguments {opOperand : OpOperandPtr}:
    opOperand.getNextUse! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getBack!_initBlockArguments {opOperand : OpOperandPtr}:
    opOperand.getBack! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getOwner!_initBlockArguments {opOperand : OpOperandPtr}:
    opOperand.getOwner! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getValue!_initBlockArguments {opOperand : OpOperandPtr}:
    opOperand.getValue! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOperands!_initBlockArguments {operation : OperationPtr} :
    operation.getOperands! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) = operation.getOperands! ctx := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumSuccessors!_initBlockArguments {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    operation.getNumSuccessors! ctx := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[simp, grind =, simp_getset]
private theorem BlockOperandPtr.get!_initBlockArguments {blockOperand : BlockOperandPtr} :
    blockOperand.get! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    blockOperand.get! ctx := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getNextUse!_initBlockArguments {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getBack!_initBlockArguments {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getOwner!_initBlockArguments {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getValue!_initBlockArguments {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessor!_initBlockArguments {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) i =
    operation.getSuccessor! ctx i := by
  fun_induction Rewriter.initBlockArguments <;> grind [OperationPtr.getSuccessor!_def]

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessors!_initBlockArguments {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    operation.getSuccessors! ctx := by
  simp only [OperationPtr.getSuccessors!_def, OperationPtr.getSuccessor!_initBlockArguments,
    OperationPtr.getNumSuccessors!_initBlockArguments]

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumRegions!_initBlockArguments {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    operation.getNumRegions! ctx := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getRegion!_initBlockArguments {operation : OperationPtr} :
    operation.getRegion! (Rewriter.initBlockArguments ctx block types index h₁ h₂) idx =
    operation.getRegion! ctx idx := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[simp, grind =, simp_getset]
private theorem BlockOperandPtrPtr.get!_initBlockArguments {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    blockOperandPtr.get! ctx := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[grind =, simp_getset]
theorem BlockPtr.getNumArguments!_initBlockArguments {block' : BlockPtr} :
    block'.getNumArguments! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    if block = block' then
      block'.getNumArguments! ctx + (types.size - idx)
    else
      block'.getNumArguments! ctx := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[grind =, simp_getset]
private theorem BlockArgumentPtr.get!_initBlockArguments {blockArg : BlockArgumentPtr} :
    blockArg.get! (Rewriter.initBlockArguments ctx bl types idx h₁ h₂) =
    if h : blockArg.block = bl ∧ blockArg.index < types.size ∧ bl.getNumArguments! ctx ≤ blockArg.index then
      { type := types[blockArg.index], firstUse := none, index := blockArg.index, owner := bl, loc := ()}
    else blockArg.get! ctx := by
  fun_induction Rewriter.initBlockArguments <;> grind [BlockPtr.getArgument_def, cases BlockArgumentPtr]

@[grind =, simp_getset]
theorem BlockArgumentPtr.getType!_initBlockArguments {blockArg : BlockArgumentPtr} :
    blockArg.getType! (Rewriter.initBlockArguments ctx bl types idx h₁ h₂) =
    if h : blockArg.block = bl ∧ blockArg.index < types.size ∧ bl.getNumArguments! ctx ≤ blockArg.index then
      types[blockArg.index]
    else blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[grind =, simp_getset]
theorem BlockArgumentPtr.getFirstUse!_initBlockArguments {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (Rewriter.initBlockArguments ctx bl types idx h₁ h₂) =
    if blockArg.block = bl ∧ blockArg.index < types.size ∧ bl.getNumArguments! ctx ≤ blockArg.index then none
    else blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[grind =, simp_getset]
theorem BlockArgumentPtr.getIndex!_initBlockArguments {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (Rewriter.initBlockArguments ctx bl types idx h₁ h₂) =
    if blockArg.block = bl ∧ blockArg.index < types.size ∧ bl.getNumArguments! ctx ≤ blockArg.index then blockArg.index
    else blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[grind =, simp_getset]
theorem BlockArgumentPtr.getLoc!_initBlockArguments {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (Rewriter.initBlockArguments ctx bl types idx h₁ h₂) =
    if blockArg.block = bl ∧ blockArg.index < types.size ∧ bl.getNumArguments! ctx ≤ blockArg.index then ()
    else blockArg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[grind =, simp_getset]
theorem BlockArgumentPtr.getOwner!_initBlockArguments {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (Rewriter.initBlockArguments ctx bl types idx h₁ h₂) =
    if blockArg.block = bl ∧ blockArg.index < types.size ∧ bl.getNumArguments! ctx ≤ blockArg.index then bl
    else blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
private theorem RegionPtr.get!_initBlockArguments {region : RegionPtr} :
    region.get! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    region.get! ctx := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getParent!_initBlockArguments {region : RegionPtr} :
    region.getParent! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getFirstBlock!_initBlockArguments {region : RegionPtr} :
    region.getFirstBlock! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getLastBlock!_initBlockArguments {region : RegionPtr} :
    region.getLastBlock! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

@[grind =, simp_getset]
theorem ValuePtr.getFirstUse!_initBlockArguments {value : ValuePtr} :
    value.getFirstUse! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    match value with
    | .blockArgument blockArg =>
      if blockArg.block = block ∧ blockArg.index < types.size ∧ block.getNumArguments! ctx ≤ blockArg.index then
        none
      else value.getFirstUse! ctx
    | _ => value.getFirstUse! ctx := by
  fun_induction Rewriter.initBlockArguments <;>
    grind [cases BlockArgumentPtr, cases ValuePtr, BlockPtr.getArgument_def]

@[grind =, simp_getset]
theorem ValuePtr.getType!_initBlockArguments {value : ValuePtr} :
    value.getType! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    match value with
    | .blockArgument blockArg =>
      if _ : blockArg.block = block ∧ blockArg.index < types.size ∧ block.getNumArguments! ctx ≤ blockArg.index then
        types[blockArg.index]
      else value.getType! ctx
    | _ => value.getType! ctx := by
  fun_induction Rewriter.initBlockArguments <;>
    grind [cases BlockArgumentPtr, cases ValuePtr, BlockPtr.getArgument_def]

@[grind =, simp_getset]
private theorem OpOperandPtrPtr.get!_initBlockArguments {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    match opOperandPtr with
    | .valueFirstUse (.blockArgument blockArg) =>
      if _ : blockArg.block = block ∧ blockArg.index < types.size ∧ block.getNumArguments! ctx ≤ blockArg.index then
        none
      else (blockArg.get! ctx).firstUse
    | _ => opOperandPtr.get! ctx := by
  cases opOperandPtr
  · grind
  · simp only [get!_valueFirstUse_eq, ValuePtr.getFirstUse!_initBlockArguments, dite_eq_ite]; grind

end Rewriter.initBlockArguments

/-! ## `Rewriter.setBlockArguments` -/

section Rewriter.setBlockArguments

variable {op : OperationPtr}
attribute [local grind] Rewriter.setBlockArguments

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstUse!_Rewriter_setBlockArguments {block' : BlockPtr} :
    block'.getFirstUse! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    block'.getFirstUse! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getPrevBlock!_Rewriter_setBlockArguments {block' : BlockPtr} :
    block'.getPrevBlock! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    block'.getPrevBlock! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNextBlock!_Rewriter_setBlockArguments {block' : BlockPtr} :
    block'.getNextBlock! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    block'.getNextBlock! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getParent!_Rewriter_setBlockArguments {block' : BlockPtr} :
    block'.getParent! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    block'.getParent! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstOp!_Rewriter_setBlockArguments {block' : BlockPtr} :
    block'.getFirstOp! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    block'.getFirstOp! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getLastOp!_Rewriter_setBlockArguments {block' : BlockPtr} :
    block'.getLastOp! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    block'.getLastOp! ctx := by
  grind

@[simp, grind =, simp_getset]
private theorem OperationPtr.get!_Rewriter_setBlockArguments {operation : OperationPtr} :
    operation.get! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    operation.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNextOp!_Rewriter_setBlockArguments {operation : OperationPtr} :
    operation.getNextOp! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getPrevOp!_Rewriter_setBlockArguments {operation : OperationPtr} :
    operation.getPrevOp! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getParent!_Rewriter_setBlockArguments {operation : OperationPtr} :
    operation.getParent! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getAttributes!_Rewriter_setBlockArguments {operation : OperationPtr} :
    operation.getAttributes! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOpType!_Rewriter_setBlockArguments {operation : OperationPtr} :
    operation.getOpType! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    operation.getOpType! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getProperties!_Rewriter_setBlockArguments {operation : OperationPtr} :
    operation.getProperties! (Rewriter.setBlockArguments ctx blockPtr types hblock) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumResults!_Rewriter_setBlockArguments {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =, simp_getset]
private theorem OpResultPtr.get!_Rewriter_setBlockArguments {opResult : OpResultPtr} :
    opResult.get! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    opResult.get! ctx := by
  grind [cases OpResultPtr]

@[simp, grind =, simp_getset]
theorem OpResultPtr.getIndex!_Rewriter_setBlockArguments {opResult : OpResultPtr} :
    opResult.getIndex! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getType!_Rewriter_setBlockArguments {opResult : OpResultPtr} :
    opResult.getType! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getFirstUse!_Rewriter_setBlockArguments {opResult : OpResultPtr} :
    opResult.getFirstUse! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getOwner!_Rewriter_setBlockArguments {opResult : OpResultPtr} :
    opResult.getOwner! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumOperands!_Rewriter_setBlockArguments {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =, simp_getset]
private theorem OpOperandPtr.get!_Rewriter_setBlockArguments {opOperand : OpOperandPtr} :
    opOperand.get! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    opOperand.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getNextUse!_Rewriter_setBlockArguments {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getBack!_Rewriter_setBlockArguments {opOperand : OpOperandPtr} :
    opOperand.getBack! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getOwner!_Rewriter_setBlockArguments {opOperand : OpOperandPtr} :
    opOperand.getOwner! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getValue!_Rewriter_setBlockArguments {opOperand : OpOperandPtr} :
    opOperand.getValue! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOperands!_Rewriter_setBlockArguments {operation : OperationPtr} :
    operation.getOperands! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumSuccessors!_Rewriter_setBlockArguments {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =, simp_getset]
private theorem BlockOperandPtr.get!_Rewriter_setBlockArguments {blockOperand : BlockOperandPtr} :
    blockOperand.get! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getNextUse!_Rewriter_setBlockArguments {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getBack!_Rewriter_setBlockArguments {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getOwner!_Rewriter_setBlockArguments {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getValue!_Rewriter_setBlockArguments {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessor!_Rewriter_setBlockArguments {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.setBlockArguments ctx blockPtr types hblock) index =
    operation.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def]

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessors!_Rewriter_setBlockArguments {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    operation.getSuccessors! ctx := by
  simp only [OperationPtr.getSuccessors!_def, OperationPtr.getSuccessor!_Rewriter_setBlockArguments,
    OperationPtr.getNumSuccessors!_Rewriter_setBlockArguments]

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumRegions!_Rewriter_setBlockArguments {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getRegion!_Rewriter_setBlockArguments {operation : OperationPtr} :
    operation.getRegion! (Rewriter.setBlockArguments ctx blockPtr types hblock) idx =
    operation.getRegion! ctx idx := by
  grind

@[simp, grind =, simp_getset]
private theorem BlockOperandPtrPtr.get!_Rewriter_setBlockArguments {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    blockOperandPtr.get! ctx := by
  grind

@[grind =, simp_getset]
theorem BlockPtr.getNumArguments!_Rewriter_setBlockArguments {block' : BlockPtr} :
    block'.getNumArguments! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    if blockPtr = block' then
      types.size
    else
      block'.getNumArguments! ctx := by
  grind

@[grind =, simp_getset]
private theorem BlockArgumentPtr.get!_Rewriter_setBlockArguments {blockArg : BlockArgumentPtr} :
    blockArg.get! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    if blockArg.block = blockPtr then
      if blockArg.index < types.size then
        { type := types[blockArg.index]!, firstUse := none, index := blockArg.index, owner := blockPtr, loc := () }
      else
        default
    else
      blockArg.get! ctx := by
  grind [BlockArgumentPtr.inBounds_def, BlockArgumentPtr.get!_of_not_inBounds]

@[grind =, simp_getset]
theorem BlockArgumentPtr.getType!_Rewriter_setBlockArguments {blockArg : BlockArgumentPtr} :
    blockArg.getType! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    if blockArg.block = blockPtr then if blockArg.index < types.size then types[blockArg.index]! else (default : BlockArgument).type
    else blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[grind =, simp_getset]
theorem BlockArgumentPtr.getFirstUse!_Rewriter_setBlockArguments {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    if blockArg.block = blockPtr then if blockArg.index < types.size then none else (default : BlockArgument).firstUse
    else blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[grind =, simp_getset]
theorem BlockArgumentPtr.getIndex!_Rewriter_setBlockArguments {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    if blockArg.block = blockPtr then if blockArg.index < types.size then blockArg.index else (default : BlockArgument).index
    else blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[grind =, simp_getset]
theorem BlockArgumentPtr.getLoc!_Rewriter_setBlockArguments {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    if blockArg.block = blockPtr then if blockArg.index < types.size then () else (default : BlockArgument).loc else blockArg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[grind =, simp_getset]
theorem BlockArgumentPtr.getOwner!_Rewriter_setBlockArguments {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    if blockArg.block = blockPtr then if blockArg.index < types.size then blockPtr else (default : BlockArgument).owner
    else blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
private theorem RegionPtr.get!_Rewriter_setBlockArguments {region : RegionPtr} :
    region.get! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    region.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getParent!_Rewriter_setBlockArguments {region : RegionPtr} :
    region.getParent! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getFirstBlock!_Rewriter_setBlockArguments {region : RegionPtr} :
    region.getFirstBlock! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getLastBlock!_Rewriter_setBlockArguments {region : RegionPtr} :
    region.getLastBlock! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

@[grind =, simp_getset]
theorem ValuePtr.getFirstUse!_Rewriter_setBlockArguments {value : ValuePtr} :
    value.getFirstUse! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    match value with
    | .blockArgument blockArg =>
      if blockArg.block = blockPtr then
        none
      else value.getFirstUse! ctx
    | _ => value.getFirstUse! ctx := by
  cases value <;>
    grind [BlockArgumentPtr.inBounds_def, BlockArgumentPtr.get!_of_not_inBounds,
      BlockArgument.default_firstUse_eq]

@[grind =, simp_getset]
theorem ValuePtr.getType!_Rewriter_setBlockArguments {value : ValuePtr} :
    value.getType! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    match value with
    | .blockArgument blockArg =>
      if blockArg.block = blockPtr then
        if blockArg.index < types.size then
          types[blockArg.index]!
        else
          default
      else
        value.getType! ctx
    | _ => value.getType! ctx := by
  cases value <;>
    grind [BlockArgumentPtr.inBounds_def, BlockArgumentPtr.get!_of_not_inBounds,
      BlockArgument.default_type_eq]

@[grind =, simp_getset]
private theorem OpOperandPtrPtr.get!_Rewriter_setBlockArguments {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.setBlockArguments ctx blockPtr types hblock) =
    match opOperandPtr with
    | .valueFirstUse (.blockArgument blockArg) =>
      if blockArg.block = blockPtr then
        none
      else opOperandPtr.get! ctx
    | _ => opOperandPtr.get! ctx := by
  grind

end Rewriter.setBlockArguments

end Veir
