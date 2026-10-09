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
section Rewriter.replaceUse

@[simp, grind ., simp_getset]
private theorem BlockOperandPtr.get!_replaceUse {bop : BlockOperandPtr} :
    bop.get! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    bop.get! ctx := by
  unfold Rewriter.replaceUse
  grind

@[simp, grind ., simp_getset]
theorem BlockOperandPtr.getNextUse!_replaceUse {bop : BlockOperandPtr} :
    bop.getNextUse! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    bop.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind ., simp_getset]
theorem BlockOperandPtr.getBack!_replaceUse {bop : BlockOperandPtr} :
    bop.getBack! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    bop.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind ., simp_getset]
theorem BlockOperandPtr.getOwner!_replaceUse {bop : BlockOperandPtr} :
    bop.getOwner! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    bop.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind ., simp_getset]
theorem BlockOperandPtr.getValue!_replaceUse {bop : BlockOperandPtr} :
    bop.getValue! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    bop.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
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
theorem BlockPtr.firstOp!_replaceUse {b : BlockPtr} :
    b.getFirstOp! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    b.getFirstOp! ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem BlockPtr.lastOp!_replaceUse {b : BlockPtr} :
    b.getLastOp! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    b.getLastOp! ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem BlockPtr.next!_replaceUse {b : BlockPtr} :
    b.getNextBlock! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    b.getNextBlock! ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem BlockPtr.prev!_replaceUse {b : BlockPtr} :
    b.getPrevBlock! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    b.getPrevBlock! ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem BlockPtr.parent!_replaceUse {b : BlockPtr} :
    b.getParent! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    b.getParent! ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem OperationPtr.parent!_replaceUse {op : OperationPtr} :
    op.getParent! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    op.getParent! ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem OperationPtr.next!_replaceUse {op : OperationPtr} :
    op.getNextOp! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    op.getNextOp! ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem OperationPtr.prev!_replaceUse {op : OperationPtr} :
    op.getPrevOp! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    op.getPrevOp! ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem OperationPtr.getOpType!_replaceUse {op : OperationPtr} :
    op.getOpType! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    op.getOpType! ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem OperationPtr.attrs!_replaceUse {op : OperationPtr} :
    op.getAttributes! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    op.getAttributes! ctx := by
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
theorem OpOperandPtr.owner!_replaceUse :
    OpOperandPtr.getOwner! opr (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    OpOperandPtr.getOwner! opr ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem OpOperandPtr.value!_replaceUse :
    OpOperandPtr.getValue! opr (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    if use = opr then
      value'
    else
      OpOperandPtr.getValue! opr ctx := by
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
theorem OperationPtr.getBlockOperands!_replaceUse :
    OperationPtr.getBlockOperands! op (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    op.getBlockOperands! ctx := by
  simp only [OperationPtr.getBlockOperands!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumResults!_replaceUse :
    OperationPtr.getNumResults! op (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    OperationPtr.getNumResults! op ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem OpResultPtr.owner!_replaceUse :
    OpResultPtr.getOwner! opr (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    OpResultPtr.getOwner! opr ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem OpResultPtr.index!_replaceUse :
    OpResultPtr.getIndex! opr (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    OpResultPtr.getIndex! opr ctx := by
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
theorem BlockPtr.getBlockArguments!_replaceUse :
    BlockPtr.getBlockArguments! block (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    block.getBlockArguments! ctx := by
  simp only [BlockPtr.getBlockArguments!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.owner!_replaceUse :
    BlockArgumentPtr.getOwner! arg (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    BlockArgumentPtr.getOwner! arg ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.index!_replaceUse :
    BlockArgumentPtr.getIndex! arg (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    BlockArgumentPtr.getIndex! arg ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =, simp_getset]
private theorem RegionPtr.get!_replaceUse :
    RegionPtr.get! reg (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    RegionPtr.get! reg ctx := by
  grind (instances := 2000) [Rewriter.replaceUse]  -- TODO: instance threshold reached when adding lemmas for Region.allocEmpty

@[simp, grind =, simp_getset]
theorem RegionPtr.getParent!_replaceUse :
    RegionPtr.getParent! reg (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    reg.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getFirstBlock!_replaceUse :
    RegionPtr.getFirstBlock! reg (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    reg.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getLastBlock!_replaceUse :
    RegionPtr.getLastBlock! reg (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    reg.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

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
private theorem BlockOperandPtr.get!_replaceValue? {bop : BlockOperandPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    bop.get! newCtx = bop.get! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem BlockOperandPtr.getNextUse!_replaceValue? {bop : BlockOperandPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    bop.getNextUse! newCtx =
    bop.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =>, simp_getset]
theorem BlockOperandPtr.getBack!_replaceValue? {bop : BlockOperandPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    bop.getBack! newCtx =
    bop.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =>, simp_getset]
theorem BlockOperandPtr.getOwner!_replaceValue? {bop : BlockOperandPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    bop.getOwner! newCtx =
    bop.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =>, simp_getset]
theorem BlockOperandPtr.getValue!_replaceValue? {bop : BlockOperandPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    bop.getValue! newCtx =
    bop.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

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
    b.getFirstOp! newCtx = b.getFirstOp! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.lastOp!_replaceValue? {b : BlockPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    b.getLastOp! newCtx = b.getLastOp! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.next!_replaceValue? {b : BlockPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    b.getNextBlock! newCtx = b.getNextBlock! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.prev!_replaceValue? {b : BlockPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    b.getPrevBlock! newCtx = b.getPrevBlock! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.parent!_replaceValue? {b : BlockPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    b.getParent! newCtx = b.getParent! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.parent!_replaceValue? {op : OperationPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    op.getParent! newCtx = op.getParent! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.next!_replaceValue? {op : OperationPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    op.getNextOp! newCtx = op.getNextOp! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.prev!_replaceValue? {op : OperationPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    op.getPrevOp! newCtx = op.getPrevOp! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getNumOperands!_replaceValue? {op : OperationPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    op.getNumOperands! newCtx = op.getNumOperands! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem OpOperandPtr.owner!_replaceValue? {opr : OpOperandPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    opr.getOwner! newCtx = opr.getOwner! ctx := by
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
theorem OperationPtr.getBlockOperands!_replaceValue? {op : OperationPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    op.getBlockOperands! newCtx =
    op.getBlockOperands! ctx := by
  simp only [OperationPtr.getBlockOperands!_def]
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getNumResults!_replaceValue? {op : OperationPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    op.getNumResults! newCtx = op.getNumResults! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem OpResultPtr.owner!_replaceValue? {opr : OpResultPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    opr.getOwner! newCtx = opr.getOwner! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem OpResultPtr.index!_replaceValue? {opr : OpResultPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    opr.getIndex! newCtx = opr.getIndex! ctx := by
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
theorem BlockPtr.getBlockArguments!_replaceValue? {block : BlockPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    block.getBlockArguments! newCtx =
    block.getBlockArguments! ctx := by
  simp only [BlockPtr.getBlockArguments!_def]
  grind

@[simp, grind =>, simp_getset]
theorem BlockArgumentPtr.owner!_replaceValue? {arg : BlockArgumentPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    arg.getOwner! newCtx = arg.getOwner! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem BlockArgumentPtr.index!_replaceValue? {arg : BlockArgumentPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    arg.getIndex! newCtx = arg.getIndex! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
private theorem RegionPtr.get!_replaceValue? {reg : RegionPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    reg.get! newCtx = reg.get! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>, simp_getset]
theorem RegionPtr.getParent!_replaceValue? {reg : RegionPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    reg.getParent! newCtx =
    reg.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =>, simp_getset]
theorem RegionPtr.getFirstBlock!_replaceValue? {reg : RegionPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    reg.getFirstBlock! newCtx =
    reg.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =>, simp_getset]
theorem RegionPtr.getLastBlock!_replaceValue? {reg : RegionPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    reg.getLastBlock! newCtx =
    reg.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

end Rewriter.replaceValue?

end Veir
