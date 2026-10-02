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

unfold_field_getters_in_grind

variable {OpInfo} [HasOpInfo OpInfo]
variable {ctx : IRContext OpInfo}
variable {Dialect : Type} [HasOpInfo Dialect] [HasDialect OpInfo Dialect]
variable {opCode : Dialect}
section Rewriter.replaceUse

@[simp, grind ., simp_getset]
theorem BlockOperandPtr.get!_replaceUse {bop : BlockOperandPtr} :
    bop.get! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    bop.get! ctx := by
  unfold Rewriter.replaceUse
  grind

@[simp, grind ., simp_getset]
theorem BlockOperandPtr.getValue!_replaceUse {bop : BlockOperandPtr} :
    bop.getValue! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = bop.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  first
  | exact BlockOperandPtr.get!_replaceUse
  | grind

@[simp, grind ., simp_getset]
theorem BlockOperandPtr.getOwner!_replaceUse {bop : BlockOperandPtr} :
    bop.getOwner! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = bop.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  first
  | exact BlockOperandPtr.get!_replaceUse
  | grind

@[simp, grind ., simp_getset]
theorem BlockOperandPtr.getBack!_replaceUse {bop : BlockOperandPtr} :
    bop.getBack! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = bop.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  first
  | exact BlockOperandPtr.get!_replaceUse
  | grind

@[simp, grind ., simp_getset]
theorem BlockOperandPtr.getNextUse!_replaceUse {bop : BlockOperandPtr} :
    bop.getNextUse! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = bop.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  first
  | exact BlockOperandPtr.get!_replaceUse
  | grind

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
theorem BlockPtr.firstOp!_replaceUse {b : BlockPtr} :
    (b.get! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn)).firstOp =
    (b.get! ctx).firstOp := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstOp!_replaceUse {b : BlockPtr} :
    b.getFirstOp! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = b.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  first
  | exact BlockPtr.firstOp!_replaceUse
  | grind

@[simp, grind =, simp_getset]
theorem BlockPtr.lastOp!_replaceUse {b : BlockPtr} :
    (b.get! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn)).lastOp =
    (b.get! ctx).lastOp := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem BlockPtr.getLastOp!_replaceUse {b : BlockPtr} :
    b.getLastOp! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = b.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  first
  | exact BlockPtr.lastOp!_replaceUse
  | grind

@[simp, grind =, simp_getset]
theorem BlockPtr.next!_replaceUse {b : BlockPtr} :
    (b.get! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn)).next =
    (b.get! ctx).next := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem BlockPtr.getNextBlock!_replaceUse {b : BlockPtr} :
    b.getNextBlock! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = b.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  first
  | exact BlockPtr.next!_replaceUse
  | grind

@[simp, grind =, simp_getset]
theorem BlockPtr.prev!_replaceUse {b : BlockPtr} :
    (b.get! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn)).prev =
    (b.get! ctx).prev := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem BlockPtr.getPrevBlock!_replaceUse {b : BlockPtr} :
    b.getPrevBlock! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = b.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  first
  | exact BlockPtr.prev!_replaceUse
  | grind

@[simp, grind =, simp_getset]
theorem BlockPtr.parent!_replaceUse {b : BlockPtr} :
    (b.get! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn)).parent =
    (b.get! ctx).parent := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem BlockPtr.getParent!_replaceUse {b : BlockPtr} :
    b.getParent! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = b.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  first
  | exact BlockPtr.parent!_replaceUse
  | grind

@[simp, grind =, simp_getset]
theorem OperationPtr.parent!_replaceUse {op : OperationPtr} :
    (op.get! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn)).parent =
    (op.get! ctx).parent := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem OperationPtr.getParent!_replaceUse {op : OperationPtr} :
    op.getParent! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = op.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  first
  | exact OperationPtr.parent!_replaceUse
  | grind

@[simp, grind =, simp_getset]
theorem OperationPtr.next!_replaceUse {op : OperationPtr} :
    (op.get! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn)).next =
    (op.get! ctx).next := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem OperationPtr.getNextOp!_replaceUse {op : OperationPtr} :
    op.getNextOp! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = op.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  first
  | exact OperationPtr.next!_replaceUse
  | grind

@[simp, grind =, simp_getset]
theorem OperationPtr.prev!_replaceUse {op : OperationPtr} :
    (op.get! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn)).prev =
    (op.get! ctx).prev := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem OperationPtr.getPrevOp!_replaceUse {op : OperationPtr} :
    op.getPrevOp! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = op.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  first
  | exact OperationPtr.prev!_replaceUse
  | grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOpType!_replaceUse {op : OperationPtr} :
    op.getOpType! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    op.getOpType! ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem OperationPtr.attrs!_replaceUse {op : OperationPtr} :
    (op.get! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn)).attrs =
    (op.get! ctx).attrs := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem OperationPtr.getAttributes!_replaceUse {op : OperationPtr} :
    op.getAttributes! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = op.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  first
  | exact OperationPtr.attrs!_replaceUse
  | grind

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
theorem OpOperandPtr.owner!_replaceUse :
    (OpOperandPtr.get! opr (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn)).owner =
    (OpOperandPtr.get! opr ctx).owner := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getOwner!_replaceUse :
    OpOperandPtr.getOwner! opr (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = (OpOperandPtr.get! opr ctx).owner := by
  simp only [OpOperandPtr.getOwner!_def]
  first
  | exact OpOperandPtr.owner!_replaceUse
  | grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.value!_replaceUse :
    (OpOperandPtr.get! opr (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn)).value =
    if use = opr then
      value'
    else
      (OpOperandPtr.get! opr ctx).value := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getValue!_replaceUse :
    OpOperandPtr.getValue! opr (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = if use = opr then value' else (OpOperandPtr.get! opr ctx).value := by
  simp only [OpOperandPtr.getValue!_def]
  first
  | exact OpOperandPtr.value!_replaceUse
  | grind

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
theorem OpResultPtr.owner!_replaceUse :
    (OpResultPtr.get! opr (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn)).owner =
    (OpResultPtr.get! opr ctx).owner := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem OpResultPtr.getOwner!_replaceUse :
    OpResultPtr.getOwner! opr (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = (OpResultPtr.get! opr ctx).owner := by
  simp only [OpResultPtr.getOwner!_def]
  first
  | exact OpResultPtr.owner!_replaceUse
  | grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.index!_replaceUse :
    (OpResultPtr.get! opr (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn)).index =
    (OpResultPtr.get! opr ctx).index := by
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
theorem BlockArgumentPtr.owner!_replaceUse :
    (BlockArgumentPtr.get! arg (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn)).owner =
    (BlockArgumentPtr.get! arg ctx).owner := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getOwner!_replaceUse :
    BlockArgumentPtr.getOwner! arg (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = (BlockArgumentPtr.get! arg ctx).owner := by
  simp only [BlockArgumentPtr.getOwner!_def]
  first
  | exact BlockArgumentPtr.owner!_replaceUse
  | grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.index!_replaceUse :
    (BlockArgumentPtr.get! arg (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn)).index =
    (BlockArgumentPtr.get! arg ctx).index := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getIndex!_replaceUse :
    BlockArgumentPtr.getIndex! arg (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = (BlockArgumentPtr.get! arg ctx).index := by
  simp only [BlockArgumentPtr.getIndex!_def]
  first
  | exact BlockArgumentPtr.index!_replaceUse
  | grind

@[simp, grind =, simp_getset]
theorem RegionPtr.get!_replaceUse :
    RegionPtr.get! reg (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    RegionPtr.get! reg ctx := by
  grind (instances := 2000) [Rewriter.replaceUse]  -- TODO: instance threshold reached when adding lemmas for Region.allocEmpty

@[simp, grind =, simp_getset]
theorem RegionPtr.getLastBlock!_replaceUse :
    RegionPtr.getLastBlock! reg (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = reg.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  first
  | exact RegionPtr.get!_replaceUse
  | grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getFirstBlock!_replaceUse :
    RegionPtr.getFirstBlock! reg (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = reg.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  first
  | exact RegionPtr.get!_replaceUse
  | grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getParent!_replaceUse :
    RegionPtr.getParent! reg (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) = reg.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  first
  | exact RegionPtr.get!_replaceUse
  | grind

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
theorem BlockOperandPtr.get!_replaceValue? {bop : BlockOperandPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    bop.get! newCtx = bop.get! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem BlockOperandPtr.getValue!_replaceValue? {bop : BlockOperandPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → bop.getValue! newCtx = bop.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  first
  | exact BlockOperandPtr.get!_replaceValue?
  | grind

@[simp, grind =>, simp_getset]
theorem BlockOperandPtr.getOwner!_replaceValue? {bop : BlockOperandPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → bop.getOwner! newCtx = bop.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  first
  | exact BlockOperandPtr.get!_replaceValue?
  | grind

@[simp, grind =>, simp_getset]
theorem BlockOperandPtr.getBack!_replaceValue? {bop : BlockOperandPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → bop.getBack! newCtx = bop.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  first
  | exact BlockOperandPtr.get!_replaceValue?
  | grind

@[simp, grind =>, simp_getset]
theorem BlockOperandPtr.getNextUse!_replaceValue? {bop : BlockOperandPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → bop.getNextUse! newCtx = bop.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  first
  | exact BlockOperandPtr.get!_replaceValue?
  | grind

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
theorem BlockPtr.firstOp!_replaceValue? {b : BlockPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    (b.get! newCtx).firstOp = (b.get! ctx).firstOp := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.getFirstOp!_replaceValue? {b : BlockPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → b.getFirstOp! newCtx = b.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  first
  | exact BlockPtr.firstOp!_replaceValue?
  | grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.lastOp!_replaceValue? {b : BlockPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    (b.get! newCtx).lastOp = (b.get! ctx).lastOp := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.getLastOp!_replaceValue? {b : BlockPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → b.getLastOp! newCtx = b.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  first
  | exact BlockPtr.lastOp!_replaceValue?
  | grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.next!_replaceValue? {b : BlockPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    (b.get! newCtx).next = (b.get! ctx).next := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.getNextBlock!_replaceValue? {b : BlockPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → b.getNextBlock! newCtx = b.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  first
  | exact BlockPtr.next!_replaceValue?
  | grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.prev!_replaceValue? {b : BlockPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    (b.get! newCtx).prev = (b.get! ctx).prev := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.getPrevBlock!_replaceValue? {b : BlockPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → b.getPrevBlock! newCtx = b.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  first
  | exact BlockPtr.prev!_replaceValue?
  | grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.parent!_replaceValue? {b : BlockPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    (b.get! newCtx).parent = (b.get! ctx).parent := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.getParent!_replaceValue? {b : BlockPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → b.getParent! newCtx = b.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  first
  | exact BlockPtr.parent!_replaceValue?
  | grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.parent!_replaceValue? {op : OperationPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    (op.get! newCtx).parent = (op.get! ctx).parent := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getParent!_replaceValue? {op : OperationPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → op.getParent! newCtx = op.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  first
  | exact OperationPtr.parent!_replaceValue?
  | grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.next!_replaceValue? {op : OperationPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    (op.get! newCtx).next = (op.get! ctx).next := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getNextOp!_replaceValue? {op : OperationPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → op.getNextOp! newCtx = op.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  first
  | exact OperationPtr.next!_replaceValue?
  | grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.prev!_replaceValue? {op : OperationPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    (op.get! newCtx).prev = (op.get! ctx).prev := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getPrevOp!_replaceValue? {op : OperationPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → op.getPrevOp! newCtx = op.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  first
  | exact OperationPtr.prev!_replaceValue?
  | grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getNumOperands!_replaceValue? {op : OperationPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    op.getNumOperands! newCtx = op.getNumOperands! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem OpOperandPtr.owner!_replaceValue? {opr : OpOperandPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    (opr.get! newCtx).owner = (opr.get! ctx).owner := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem OpOperandPtr.getOwner!_replaceValue? {opr : OpOperandPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → opr.getOwner! newCtx = opr.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  first
  | exact OpOperandPtr.owner!_replaceValue?
  | grind

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
theorem OpResultPtr.owner!_replaceValue? {opr : OpResultPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    (opr.get! newCtx).owner = (opr.get! ctx).owner := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem OpResultPtr.getOwner!_replaceValue? {opr : OpResultPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → opr.getOwner! newCtx = opr.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  first
  | exact OpResultPtr.owner!_replaceValue?
  | grind

@[simp, grind =>, simp_getset]
theorem OpResultPtr.index!_replaceValue? {opr : OpResultPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    (opr.get! newCtx).index = (opr.get! ctx).index := by
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
theorem BlockArgumentPtr.owner!_replaceValue? {arg : BlockArgumentPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    (arg.get! newCtx).owner = (arg.get! ctx).owner := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem BlockArgumentPtr.getOwner!_replaceValue? {arg : BlockArgumentPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → arg.getOwner! newCtx = arg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  first
  | exact BlockArgumentPtr.owner!_replaceValue?
  | grind

@[simp, grind =>, simp_getset]
theorem BlockArgumentPtr.index!_replaceValue? {arg : BlockArgumentPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    (arg.get! newCtx).index = (arg.get! ctx).index := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem BlockArgumentPtr.getIndex!_replaceValue? {arg : BlockArgumentPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → arg.getIndex! newCtx = arg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  first
  | exact BlockArgumentPtr.index!_replaceValue?
  | grind

@[simp, grind =>, simp_getset]
theorem RegionPtr.get!_replaceValue? {reg : RegionPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    reg.get! newCtx = reg.get! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem RegionPtr.getLastBlock!_replaceValue? {reg : RegionPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → reg.getLastBlock! newCtx = reg.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  first
  | exact RegionPtr.get!_replaceValue?
  | grind

@[simp, grind =>, simp_getset]
theorem RegionPtr.getFirstBlock!_replaceValue? {reg : RegionPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → reg.getFirstBlock! newCtx = reg.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  first
  | exact RegionPtr.get!_replaceValue?
  | grind

@[simp, grind =>, simp_getset]
theorem RegionPtr.getParent!_replaceValue? {reg : RegionPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx → reg.getParent! newCtx = reg.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  first
  | exact RegionPtr.get!_replaceValue?
  | grind

end Rewriter.replaceValue?

end Veir
