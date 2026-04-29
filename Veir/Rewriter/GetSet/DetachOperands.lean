module

public import Veir.IR.Basic
public import Veir.Rewriter.Basic

import all Veir.Rewriter.Basic

import Veir.Rewriter.LinkedList.GetSet
import Veir.ForLean
import Veir.IR.DeallocLemmas

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
theorem OperationPtr.getOperands!_detachOperands_loop {operation : OperationPtr} :
    operation.getOperands! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) =
    operation.getOperands! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop]
  · simp only [Rewriter.detachOperands.loop]
    grind

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
theorem OperationPtr.getSuccessor!_detachOperands_loop {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) i =
    operation.getSuccessor! ctx i := by
  induction index generalizing ctx
  · grind [Rewriter.detachOperands.loop, OperationPtr.getSuccessor!_def]
  · simp only [Rewriter.detachOperands.loop]
    grind [OperationPtr.getSuccessor!_def]

@[simp, grind =]
theorem OperationPtr.getSuccessors!_detachOperands_loop {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.detachOperands.loop ctx op' index hCtx hOp hIndex) =
    operation.getSuccessors! ctx := by
  simp only [OperationPtr.getSuccessors!_def, OperationPtr.getSuccessor!_detachOperands_loop,
    OperationPtr.getNumSuccessors!_detachOperands_loop]

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

@[simp, grind =]
theorem BlockPtr.firstOp!_detachOperands {block : BlockPtr} :
    (block.get! (Rewriter.detachOperands ctx op' hCtx hOp)).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =]
theorem BlockPtr.lastOp!_detachOperands {block : BlockPtr} :
    (block.get! (Rewriter.detachOperands ctx op' hCtx hOp)).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_detachOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOperands ctx op' hCtx hOp)).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_detachOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOperands ctx op' hCtx hOp)).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
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
theorem OperationPtr.getOperands!_detachOperands {operation : OperationPtr} :
    operation.getOperands! (Rewriter.detachOperands ctx op' hCtx hOp) = operation.getOperands! ctx := by
  simp only [Rewriter.detachOperands]
  grind

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
theorem OperationPtr.getSuccessor!_detachOperands {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.detachOperands ctx op' hCtx hOp) index =
    operation.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def]

@[simp, grind =]
theorem OperationPtr.getSuccessors!_detachOperands {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.detachOperands ctx op' hCtx hOp) =
    operation.getSuccessors! ctx := by
  grind [OperationPtr.getSuccessors!_def]

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

end Veir
