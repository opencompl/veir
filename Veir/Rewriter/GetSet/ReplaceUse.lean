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

fold_field_getters_in_grind

variable {OpInfo} [HasOpInfo OpInfo]
variable {ctx : IRContext OpInfo}
variable {Dialect : Type} [HasOpInfo Dialect] [HasDialect OpInfo Dialect]
variable {opCode : Dialect}
section Rewriter.replaceUse

@[simp, grind ., simp_getset]
theorem BlockOperandPtr.getValue!_replaceUse {bop : BlockOperandPtr} :
    bop.getValue! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = bop.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  unfold Rewriter.replaceUse
  grind

@[simp, grind ., simp_getset]
theorem BlockOperandPtr.getOwner!_replaceUse {bop : BlockOperandPtr} :
    bop.getOwner! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = bop.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  unfold Rewriter.replaceUse
  grind

@[simp, grind ., simp_getset]
theorem BlockOperandPtr.getBack!_replaceUse {bop : BlockOperandPtr} :
    bop.getBack! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = bop.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  unfold Rewriter.replaceUse
  grind

@[simp, grind ., simp_getset]
theorem BlockOperandPtr.getNextUse!_replaceUse {bop : BlockOperandPtr} :
    bop.getNextUse! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = bop.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  unfold Rewriter.replaceUse
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessor!_replaceUse {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) index =
    operation.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def, Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessors!_replaceUse {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    operation.getSuccessors! ctx := by
  grind [OperationPtr.getSuccessors!_def, Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstOp!_replaceUse {b : BlockPtr} :
    b.getFirstOp! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = b.getFirstOp! ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem BlockPtr.getLastOp!_replaceUse {b : BlockPtr} :
    b.getLastOp! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = b.getLastOp! ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem BlockPtr.getNextBlock!_replaceUse {b : BlockPtr} :
    b.getNextBlock! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = b.getNextBlock! ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem BlockPtr.getPrevBlock!_replaceUse {b : BlockPtr} :
    b.getPrevBlock! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = b.getPrevBlock! ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem BlockPtr.getParent!_replaceUse {b : BlockPtr} :
    b.getParent! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = b.getParent! ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem OperationPtr.getParent!_replaceUse {op : OperationPtr} :
    op.getParent! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = op.getParent! ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem OperationPtr.getNextOp!_replaceUse {op : OperationPtr} :
    op.getNextOp! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = op.getNextOp! ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem OperationPtr.getPrevOp!_replaceUse {op : OperationPtr} :
    op.getPrevOp! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = op.getPrevOp! ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem OperationPtr.getOpType!_replaceUse {op : OperationPtr} :
    op.getOpType! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    op.getOpType! ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem OperationPtr.getAttributes!_replaceUse {op : OperationPtr} :
    op.getAttributes! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = op.getAttributes! ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem OperationPtr.getProperties!_replaceUse {op : OperationPtr} :
    op.getProperties! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) opCode =
    op.getProperties! ctx opCode := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumOperands!_replaceUse :
    OperationPtr.getNumOperands! op (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    OperationPtr.getNumOperands! op ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getOwner!_replaceUse :
    OpOperandPtr.getOwner! opr (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = (OpOperandPtr.getOwner! opr ctx) := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getValue!_replaceUse :
    OpOperandPtr.getValue! opr (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = if use = opr then value' else (OpOperandPtr.getValue! opr ctx) := by
  grind [Rewriter.replaceUse]

@[grind =, simp_getset]
theorem OperationPtr.getOperands!_replaceUse :
    OperationPtr.getOperands! op (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    if use.op = op then
      (op.getOperands! ctx).set! use.index value'
    else
      OperationPtr.getOperands! op ctx := by
  simp only [Rewriter.replaceUse]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumSuccessors!_replaceUse :
    OperationPtr.getNumSuccessors! op (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    OperationPtr.getNumSuccessors! op ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumResults!_replaceUse :
    OperationPtr.getNumResults! op (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    OperationPtr.getNumResults! op ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem OpResultPtr.getOwner!_replaceUse :
    OpResultPtr.getOwner! opr (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = (OpResultPtr.getOwner! opr ctx) := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem OpResultPtr.getIndex!_replaceUse :
    (OpResultPtr.getIndex! opr (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn)) =
    (OpResultPtr.getIndex! opr ctx) := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumRegions!_replaceUse :
    OperationPtr.getNumRegions! op (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    OperationPtr.getNumRegions! op ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem OperationPtr.getRegions!_replaceUse :
    OperationPtr.getRegion! op (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    OperationPtr.getRegion! op ctx := by
  grind (instances := 2000) [Rewriter.replaceUse] -- TODO: instance threshold reached when adding lemmas for Region.allocEmpty

@[simp, grind =, simp_getset]
theorem BlockPtr.getNumArguments!_replaceUse :
    BlockPtr.getNumArguments! block (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    BlockPtr.getNumArguments! block ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getOwner!_replaceUse :
    BlockArgumentPtr.getOwner! arg (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = (BlockArgumentPtr.getOwner! arg ctx) := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getIndex!_replaceUse :
    BlockArgumentPtr.getIndex! arg (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = BlockArgumentPtr.getIndex! arg ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem RegionPtr.getLastBlock!_replaceUse :
    RegionPtr.getLastBlock! reg (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = reg.getLastBlock! ctx := by
  grind (instances := 2000) [Rewriter.replaceUse]  -- TODO: instance threshold reached when adding lemmas for Region.allocEmpty

@[simp, grind =, simp_getset]
theorem RegionPtr.getFirstBlock!_replaceUse :
    RegionPtr.getFirstBlock! reg (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = reg.getFirstBlock! ctx := by
  grind (instances := 2000) [Rewriter.replaceUse]  -- TODO: instance threshold reached when adding lemmas for Region.allocEmpty

@[simp, grind =, simp_getset]
theorem RegionPtr.getParent!_replaceUse :
    RegionPtr.getParent! reg (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = reg.getParent! ctx := by
  grind (instances := 2000) [Rewriter.replaceUse]  -- TODO: instance threshold reached when adding lemmas for Region.allocEmpty

@[simp, grind =, simp_getset]
theorem ValuePtr.getType!_replaceUse {v : ValuePtr} :
    v.getType! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    v.getType! ctx := by
  grind [Rewriter.replaceUse]

end Rewriter.replaceUse
/-! ## `Rewriter.replaceValue?` -/

section Rewriter.replaceValue?

attribute [local grind] Rewriter.replaceValue?

@[simp, grind =>, simp_getset]
theorem BlockOperandPtr.getValue!_replaceValue? {bop : BlockOperandPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → bop.getValue! newCtx = bop.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem BlockOperandPtr.getOwner!_replaceValue? {bop : BlockOperandPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → bop.getOwner! newCtx = bop.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem BlockOperandPtr.getBack!_replaceValue? {bop : BlockOperandPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → bop.getBack! newCtx = bop.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem BlockOperandPtr.getNextUse!_replaceValue? {bop : BlockOperandPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → bop.getNextUse! newCtx = bop.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getSuccessor!_replaceValue? {operation : OperationPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    operation.getSuccessor! newCtx index = operation.getSuccessor! ctx index := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind [OperationPtr.getSuccessor!_def]

@[simp, grind =>, simp_getset]
theorem OperationPtr.getSuccessors!_replaceValue? {operation : OperationPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    operation.getSuccessors! newCtx = operation.getSuccessors! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind [OperationPtr.getSuccessors!_def]

@[simp, grind =>, simp_getset]
theorem BlockPtr.getFirstOp!_replaceValue? {b : BlockPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → b.getFirstOp! newCtx = b.getFirstOp! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.getLastOp!_replaceValue? {b : BlockPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → b.getLastOp! newCtx = b.getLastOp! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.getNextBlock!_replaceValue? {b : BlockPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → b.getNextBlock! newCtx = b.getNextBlock! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.getPrevBlock!_replaceValue? {b : BlockPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → b.getPrevBlock! newCtx = b.getPrevBlock! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.getParent!_replaceValue? {b : BlockPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → b.getParent! newCtx = b.getParent! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getParent!_replaceValue? {op : OperationPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → op.getParent! newCtx = op.getParent! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getNextOp!_replaceValue? {op : OperationPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → op.getNextOp! newCtx = op.getNextOp! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getPrevOp!_replaceValue? {op : OperationPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → op.getPrevOp! newCtx = op.getPrevOp! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getNumOperands!_replaceValue? {op : OperationPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    op.getNumOperands! newCtx = op.getNumOperands! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem OpOperandPtr.getOwner!_replaceValue? {opr : OpOperandPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → opr.getOwner! newCtx = opr.getOwner! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

/-!
 theorem `OpOperandPtr.value!_replaceValue?` and
 `OperationPtr.getOperands!_replaceValue?` requires Well-formedness
 preservation to be stated.
-/

@[simp, grind =>, simp_getset]
theorem OperationPtr.getNumSuccessors!_replaceValue? {op : OperationPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    op.getNumSuccessors! newCtx = op.getNumSuccessors! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getNumResults!_replaceValue? {op : OperationPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    op.getNumResults! newCtx = op.getNumResults! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem OpResultPtr.getOwner!_replaceValue? {opr : OpResultPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → opr.getOwner! newCtx = opr.getOwner! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem OpResultPtr.getIndex!_replaceValue? {opr : OpResultPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    (opr.getIndex! newCtx) = (opr.getIndex! ctx) := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getNumRegions!_replaceValue? {op : OperationPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    op.getNumRegions! newCtx = op.getNumRegions! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getRegions_replaceValue? {op : OperationPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    op.getRegion! newCtx index = op.getRegion! ctx index := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.getNumArguments!_replaceValue? {block : BlockPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    block.getNumArguments! newCtx = block.getNumArguments! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem BlockArgumentPtr.getOwner!_replaceValue? {arg : BlockArgumentPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → arg.getOwner! newCtx = arg.getOwner! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem BlockArgumentPtr.getIndex!_replaceValue? {arg : BlockArgumentPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → arg.getIndex! newCtx = arg.getIndex! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem RegionPtr.getLastBlock!_replaceValue? {reg : RegionPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → reg.getLastBlock! newCtx = reg.getLastBlock! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem RegionPtr.getFirstBlock!_replaceValue? {reg : RegionPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → reg.getFirstBlock! newCtx = reg.getFirstBlock! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem RegionPtr.getParent!_replaceValue? {reg : RegionPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → reg.getParent! newCtx = reg.getParent! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

end Rewriter.replaceValue?

end Veir
