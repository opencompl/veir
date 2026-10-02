module

public import Veir.Rewriter.Basic

import all Veir.Rewriter.Basic
import Veir.Rewriter.WfRewriter.GetSetTactic


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
variable {opCode : Dialect}
section Rewriter.detachOperands.loop

variable {op : OperationPtr}

attribute [local grind] Rewriter.detachOperands.loop

@[simp, grind =, simp_getset]
theorem BlockPtr.firstUse!_detachOperands_loop {block : BlockPtr} :
    (block.get! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex)).firstUse = (block.get! ctx).firstUse := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstUse!_detachOperands_loop {block : BlockPtr} :
    block.getFirstUse! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) = block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  first
  | exact BlockPtr.firstUse!_detachOperands_loop
  | grind

@[simp, grind =, simp_getset]
theorem BlockPtr.prev!_detachOperands_loop {block : BlockPtr} :
    (block.get! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex)).prev = (block.get! ctx).prev := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getPrevBlock!_detachOperands_loop {block : BlockPtr} :
    block.getPrevBlock! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) = block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  first
  | exact BlockPtr.prev!_detachOperands_loop
  | grind

@[simp, grind =, simp_getset]
theorem BlockPtr.next!_detachOperands_loop {block : BlockPtr} :
    (block.get! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex)).next = (block.get! ctx).next := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNextBlock!_detachOperands_loop {block : BlockPtr} :
    block.getNextBlock! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) = block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  first
  | exact BlockPtr.next!_detachOperands_loop
  | grind

@[simp, grind =, simp_getset]
theorem BlockPtr.parent!_detachOperands_loop {block : BlockPtr} :
    (block.get! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex)).parent = (block.get! ctx).parent := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getParent!_detachOperands_loop {block : BlockPtr} :
    block.getParent! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) = block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  first
  | exact BlockPtr.parent!_detachOperands_loop
  | grind

@[grind =, simp_getset]
theorem BlockPtr.firstOp!_detachOperands_loop {block : BlockPtr} :
    (block.get! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex)).firstOp =
    (block.get! ctx).firstOp := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

@[grind =, simp_getset]
theorem BlockPtr.getFirstOp!_detachOperands_loop {block : BlockPtr} :
    block.getFirstOp! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) = block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  first
  | exact BlockPtr.firstOp!_detachOperands_loop
  | grind

@[grind =, simp_getset]
theorem BlockPtr.lastOp!_detachOperands_loop {block : BlockPtr} :
    (block.get! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex)).lastOp =
    (block.get! ctx).lastOp := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

@[grind =, simp_getset]
theorem BlockPtr.getLastOp!_detachOperands_loop {block : BlockPtr} :
    block.getLastOp! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) = block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  first
  | exact BlockPtr.lastOp!_detachOperands_loop
  | grind

@[grind =, simp_getset]
theorem OperationPtr.prev!_detachOperands_loop {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex)).prev =
    (operation.get! ctx).prev := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

@[grind =, simp_getset]
theorem OperationPtr.getPrevOp!_detachOperands_loop {operation : OperationPtr} :
    operation.getPrevOp! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) = operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  first
  | exact OperationPtr.prev!_detachOperands_loop
  | grind

@[grind =, simp_getset]
theorem OperationPtr.next!_detachOperands_loop {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex)).next =
    (operation.get! ctx).next := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

@[grind =, simp_getset]
theorem OperationPtr.getNextOp!_detachOperands_loop {operation : OperationPtr} :
    operation.getNextOp! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) = operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  first
  | exact OperationPtr.next!_detachOperands_loop
  | grind

@[grind =, simp_getset]
theorem OperationPtr.parent!_detachOperands_loop {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex)).parent =
    (operation.get! ctx).parent := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

@[grind =, simp_getset]
theorem OperationPtr.getParent!_detachOperands_loop {operation : OperationPtr} :
    operation.getParent! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) = operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  first
  | exact OperationPtr.parent!_detachOperands_loop
  | grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOpType!_detachOperands_loop {operation : OperationPtr} :
    operation.getOpType! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) =
    operation.getOpType! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem OperationPtr.attrs!_detachOperands_loop {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex)).attrs =
    (operation.get! ctx).attrs := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getAttributes!_detachOperands_loop {operation : OperationPtr} :
    operation.getAttributes! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) = operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  first
  | exact OperationPtr.attrs!_detachOperands_loop
  | grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getProperties!_detachOperands_loop {operation : OperationPtr} :
    operation.getProperties! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) opCode =
    operation.getProperties! ctx opCode := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

@[simp, grind =, simp_getset]
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

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumOperands!_detachOperands_loop {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) = operation.getNumOperands! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

-- The theorem `OpOperandPtr.get!_detachOperands_loop` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.OpChain` directly.

@[simp, grind =, simp_getset]
theorem OperationPtr.getOperands!_detachOperands_loop {operation : OperationPtr} :
    operation.getOperands! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) =
    operation.getOperands! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumSuccessors!_detachOperands_loop {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) =
    operation.getNumSuccessors! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.get!_detachOperands_loop {blockOperand : BlockOperandPtr} :
    blockOperand.get! (Rewriter.detachOperands.loop ctx op' index' hCtx hOp hIndex) =
    blockOperand.get! ctx := by
  induction index' generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getValue!_detachOperands_loop {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (Rewriter.detachOperands.loop ctx op' index' hCtx hOp hIndex) = blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  first
  | exact BlockOperandPtr.get!_detachOperands_loop
  | grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getOwner!_detachOperands_loop {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (Rewriter.detachOperands.loop ctx op' index' hCtx hOp hIndex) = blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  first
  | exact BlockOperandPtr.get!_detachOperands_loop
  | grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getBack!_detachOperands_loop {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (Rewriter.detachOperands.loop ctx op' index' hCtx hOp hIndex) = blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  first
  | exact BlockOperandPtr.get!_detachOperands_loop
  | grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getNextUse!_detachOperands_loop {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (Rewriter.detachOperands.loop ctx op' index' hCtx hOp hIndex) = blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  first
  | exact BlockOperandPtr.get!_detachOperands_loop
  | grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessor!_detachOperands_loop {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) i =
    operation.getSuccessor! ctx i := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop, OperationPtr.getSuccessor!_def]
  · simp only [Rewriter.detachOperands.loop]
    grind [OperationPtr.getSuccessor!_def]

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessors!_detachOperands_loop {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) =
    operation.getSuccessors! ctx := by
  simp only [OperationPtr.getSuccessors!_def, OperationPtr.getSuccessor!_detachOperands_loop,
    OperationPtr.getNumSuccessors!_detachOperands_loop]

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumRegions!_detachOperands_loop {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) =
    operation.getNumRegions! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getRegion!_detachOperands_loop {operation : OperationPtr} :
    operation.getRegion! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) i =
    operation.getRegion! ctx i := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtrPtr.get!_detachOperands_loop {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) =
    blockOperandPtr.get! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

@[simp, grind =, simp_getset]
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

@[simp, grind =, simp_getset]
theorem RegionPtr.get!_detachOperands_loop {region : RegionPtr} :
    region.get! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) =
    region.get! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getLastBlock!_detachOperands_loop {region : RegionPtr} :
    region.getLastBlock! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) = region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  first
  | exact RegionPtr.get!_detachOperands_loop
  | grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getFirstBlock!_detachOperands_loop {region : RegionPtr} :
    region.getFirstBlock! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) = region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  first
  | exact RegionPtr.get!_detachOperands_loop
  | grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getParent!_detachOperands_loop {region : RegionPtr} :
    region.getParent! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) = region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  first
  | exact RegionPtr.get!_detachOperands_loop
  | grind

-- The theorem `ValuePtr.getFirstUse!_detachOperands_loop` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.OpChain` directly.

@[simp, grind =, simp_getset]
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

@[simp, grind =, simp_getset]
theorem BlockPtr.firstUse!_detachOperands {block : BlockPtr} :
    (block.get! (Rewriter.detachOperands ctx op' hCtx hOp)).firstUse = (block.get! ctx).firstUse := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstUse!_detachOperands {block : BlockPtr} :
    block.getFirstUse! (Rewriter.detachOperands ctx op' hCtx hOp) = block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  first
  | exact BlockPtr.firstUse!_detachOperands
  | grind

@[simp, grind =, simp_getset]
theorem BlockPtr.prev!_detachOperands {block : BlockPtr} :
    (block.get! (Rewriter.detachOperands ctx op' hCtx hOp)).prev = (block.get! ctx).prev := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getPrevBlock!_detachOperands {block : BlockPtr} :
    block.getPrevBlock! (Rewriter.detachOperands ctx op' hCtx hOp) = block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  first
  | exact BlockPtr.prev!_detachOperands
  | grind

@[simp, grind =, simp_getset]
theorem BlockPtr.next!_detachOperands {block : BlockPtr} :
    (block.get! (Rewriter.detachOperands ctx op' hCtx hOp)).next = (block.get! ctx).next := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNextBlock!_detachOperands {block : BlockPtr} :
    block.getNextBlock! (Rewriter.detachOperands ctx op' hCtx hOp) = block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  first
  | exact BlockPtr.next!_detachOperands
  | grind

@[simp, grind =, simp_getset]
theorem BlockPtr.parent!_detachOperands {block : BlockPtr} :
    (block.get! (Rewriter.detachOperands ctx op' hCtx hOp)).parent = (block.get! ctx).parent := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getParent!_detachOperands {block : BlockPtr} :
    block.getParent! (Rewriter.detachOperands ctx op' hCtx hOp) = block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  first
  | exact BlockPtr.parent!_detachOperands
  | grind

@[simp, grind =, simp_getset]
theorem BlockPtr.firstOp!_detachOperands {block : BlockPtr} :
    (block.get! (Rewriter.detachOperands ctx op' hCtx hOp)).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstOp!_detachOperands {block : BlockPtr} :
    block.getFirstOp! (Rewriter.detachOperands ctx op' hCtx hOp) = block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  first
  | exact BlockPtr.firstOp!_detachOperands
  | grind

@[simp, grind =, simp_getset]
theorem BlockPtr.lastOp!_detachOperands {block : BlockPtr} :
    (block.get! (Rewriter.detachOperands ctx op' hCtx hOp)).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getLastOp!_detachOperands {block : BlockPtr} :
    block.getLastOp! (Rewriter.detachOperands ctx op' hCtx hOp) = block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  first
  | exact BlockPtr.lastOp!_detachOperands
  | grind

@[simp, grind =, simp_getset]
theorem OperationPtr.prev!_detachOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOperands ctx op' hCtx hOp)).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getPrevOp!_detachOperands {operation : OperationPtr} :
    operation.getPrevOp! (Rewriter.detachOperands ctx op' hCtx hOp) = operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  first
  | exact OperationPtr.prev!_detachOperands
  | grind

@[simp, grind =, simp_getset]
theorem OperationPtr.next!_detachOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOperands ctx op' hCtx hOp)).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNextOp!_detachOperands {operation : OperationPtr} :
    operation.getNextOp! (Rewriter.detachOperands ctx op' hCtx hOp) = operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  first
  | exact OperationPtr.next!_detachOperands
  | grind

@[simp, grind =, simp_getset]
theorem OperationPtr.parent!_detachOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOperands ctx op' hCtx hOp)).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getParent!_detachOperands {operation : OperationPtr} :
    operation.getParent! (Rewriter.detachOperands ctx op' hCtx hOp) = operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  first
  | exact OperationPtr.parent!_detachOperands
  | grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOpType!_detachOperands {operation : OperationPtr} :
    operation.getOpType! (Rewriter.detachOperands ctx op' hCtx hOp) =
    operation.getOpType! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.attrs!_detachOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOperands ctx op' hCtx hOp)).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getAttributes!_detachOperands {operation : OperationPtr} :
    operation.getAttributes! (Rewriter.detachOperands ctx op' hCtx hOp) = operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  first
  | exact OperationPtr.attrs!_detachOperands
  | grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getProperties!_detachOperands {operation : OperationPtr} :
    operation.getProperties! (Rewriter.detachOperands ctx op' hCtx hOp) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumResults!_detachOperands {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.detachOperands ctx op' hCtx hOp) =
    operation.getNumResults! ctx := by
  grind

-- The theorem `OpResultPtr.get!_detachOperands` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.OpChain` directly.

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumOperands!_detachOperands {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.detachOperands ctx op' hCtx hOp) = operation.getNumOperands! ctx := by
  grind

-- The theorem `OpOperandPtr.get!_detachOperands` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.OpChain` directly.

@[simp, grind =, simp_getset]
theorem OperationPtr.getOperands!_detachOperands {operation : OperationPtr} :
    operation.getOperands! (Rewriter.detachOperands ctx op' hCtx hOp) = operation.getOperands! ctx := by
  simp only [Rewriter.detachOperands]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumSuccessors!_detachOperands {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.detachOperands ctx op' hCtx hOp) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.get!_detachOperands {blockOperand : BlockOperandPtr} :
    blockOperand.get! (Rewriter.detachOperands ctx op' hCtx hOp) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getValue!_detachOperands {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (Rewriter.detachOperands ctx op' hCtx hOp) = blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  first
  | exact BlockOperandPtr.get!_detachOperands
  | grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getOwner!_detachOperands {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (Rewriter.detachOperands ctx op' hCtx hOp) = blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  first
  | exact BlockOperandPtr.get!_detachOperands
  | grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getBack!_detachOperands {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (Rewriter.detachOperands ctx op' hCtx hOp) = blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  first
  | exact BlockOperandPtr.get!_detachOperands
  | grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getNextUse!_detachOperands {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (Rewriter.detachOperands ctx op' hCtx hOp) = blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  first
  | exact BlockOperandPtr.get!_detachOperands
  | grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessor!_detachOperands {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.detachOperands ctx op' hCtx hOp) index =
    operation.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def]

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessors!_detachOperands {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.detachOperands ctx op' hCtx hOp) =
    operation.getSuccessors! ctx := by
  grind [OperationPtr.getSuccessors!_def]

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumRegions!_detachOperands {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.detachOperands ctx op' hCtx hOp) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getRegion!_detachOperands {operation : OperationPtr} :
    operation.getRegion! (Rewriter.detachOperands ctx op' hCtx hOp) i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtrPtr.get!_detachOperands {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (Rewriter.detachOperands ctx op' hCtx hOp) =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNumArguments!_detachOperands {block : BlockPtr} :
    block.getNumArguments! (Rewriter.detachOperands ctx op' hCtx hOp) =
    block.getNumArguments! ctx := by
  grind

-- The theorem `BlockArgumentPtr.get!_detachOperands` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.OpChain` directly.

@[simp, grind =, simp_getset]
theorem RegionPtr.get!_detachOperands {region : RegionPtr} :
    region.get! (Rewriter.detachOperands ctx op' hCtx hOp) =
    region.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getLastBlock!_detachOperands {region : RegionPtr} :
    region.getLastBlock! (Rewriter.detachOperands ctx op' hCtx hOp) = region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  first
  | exact RegionPtr.get!_detachOperands
  | grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getFirstBlock!_detachOperands {region : RegionPtr} :
    region.getFirstBlock! (Rewriter.detachOperands ctx op' hCtx hOp) = region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  first
  | exact RegionPtr.get!_detachOperands
  | grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getParent!_detachOperands {region : RegionPtr} :
    region.getParent! (Rewriter.detachOperands ctx op' hCtx hOp) = region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  first
  | exact RegionPtr.get!_detachOperands
  | grind

-- The theorem `ValuePtr.getFirstUse!_detachOperands` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.OpChain` directly.

@[simp, grind =, simp_getset]
theorem ValuePtr.getType!_detachOperands {value : ValuePtr} :
    value.getType! (Rewriter.detachOperands ctx op' hCtx hOp) =
    value.getType! ctx := by
  grind

-- The theorem `OpOperandPtr.getFirstUse!_detachOperands` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.OpChain` directly.

end Rewriter.detachOperands

end Veir
