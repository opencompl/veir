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
section Rewriter.replaceUse

@[simp, grind .]
theorem BlockOperandPtr.get!_replaceUse {bop : BlockOperandPtr} :
    bop.get! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    bop.get! ctx := by
  unfold Rewriter.replaceUse
  grind

@[simp, grind =]
theorem OperationPtr.getSuccessor!_replaceUse {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) index =
    operation.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def, Rewriter.replaceUse]

@[simp, grind =]
theorem OperationPtr.getSuccessors!_replaceUse {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    operation.getSuccessors! ctx := by
  grind [OperationPtr.getSuccessors!_def, Rewriter.replaceUse]

@[simp, grind =]
theorem BlockPtr.firstOp!_replaceUse {b : BlockPtr} :
    (b.get! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn)).firstOp =
    (b.get! ctx).firstOp := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem BlockPtr.lastOp!_replaceUse {b : BlockPtr} :
    (b.get! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn)).lastOp =
    (b.get! ctx).lastOp := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem BlockPtr.next!_replaceUse {b : BlockPtr} :
    (b.get! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn)).next =
    (b.get! ctx).next := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem BlockPtr.prev!_replaceUse {b : BlockPtr} :
    (b.get! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn)).prev =
    (b.get! ctx).prev := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem BlockPtr.parent!_replaceUse {b : BlockPtr} :
    (b.get! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn)).parent =
    (b.get! ctx).parent := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem OperationPtr.parent!_replaceUse {op : OperationPtr} :
    (op.get! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn)).parent =
    (op.get! ctx).parent := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem OperationPtr.next!_replaceUse {op : OperationPtr} :
    (op.get! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn)).next =
    (op.get! ctx).next := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem OperationPtr.prev!_replaceUse {op : OperationPtr} :
    (op.get! (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn)).prev =
    (op.get! ctx).prev := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem OperationPtr.getNumOperands!_replaceUse :
    OperationPtr.getNumOperands! op (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    OperationPtr.getNumOperands! op ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem OpOperandPtr.owner!_replaceUse :
    (OpOperandPtr.get! opr (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn)).owner =
    (OpOperandPtr.get! opr ctx).owner := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem OpOperandPtr.value!_replaceUse :
    (OpOperandPtr.get! opr (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn)).value =
    if use = opr then
      value'
    else
      (OpOperandPtr.get! opr ctx).value := by
  grind [Rewriter.replaceUse]

@[grind =]
theorem OperationPtr.getOperands!_replaceUse :
    OperationPtr.getOperands! op (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    if use.op = op then
      (op.getOperands! ctx).set! use.index value'
    else
      OperationPtr.getOperands! op ctx := by
  simp only [Rewriter.replaceUse]
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_replaceUse :
    OperationPtr.getNumSuccessors! op (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    OperationPtr.getNumSuccessors! op ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem OperationPtr.getNumResults!_replaceUse :
    OperationPtr.getNumResults! op (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    OperationPtr.getNumResults! op ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem OpResultPtr.owner!_replaceUse :
    (OpResultPtr.get! opr (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn)).owner =
    (OpResultPtr.get! opr ctx).owner := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem OpResultPtr.index!_replaceUse :
    (OpResultPtr.get! opr (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn)).index =
    (OpResultPtr.get! opr ctx).index := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem OperationPtr.getNumRegions!_replaceUse :
    OperationPtr.getNumRegions! op (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    OperationPtr.getNumRegions! op ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem OperationPtr.getRegions!_replaceUse :
    OperationPtr.getRegion! op (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    OperationPtr.getRegion! op ctx := by
  grind (instances := 2000) [Rewriter.replaceUse] -- TODO: instance threshold reached when adding lemmas for Region.allocEmpty

@[simp, grind =]
theorem BlockPtr.getNumArguments!_replaceUse :
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
theorem RegionPtr.get!_replaceUse :
    RegionPtr.get! reg (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    RegionPtr.get! reg ctx := by
  grind (instances := 2000) [Rewriter.replaceUse]  -- TODO: instance threshold reached when adding lemmas for Region.allocEmpty

end Rewriter.replaceUse
/-! ## `Rewriter.replaceValue?` -/

section Rewriter.replaceValue?

attribute [local grind] Rewriter.replaceValue?

@[simp, grind =>]
theorem BlockOperandPtr.get!_replaceValue? {bop : BlockOperandPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    bop.get! newCtx = bop.get! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>]
theorem OperationPtr.getSuccessor!_replaceValue? {operation : OperationPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    operation.getSuccessor! newCtx index = operation.getSuccessor! ctx index := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind [OperationPtr.getSuccessor!_def]

@[simp, grind =>]
theorem OperationPtr.getSuccessors!_replaceValue? {operation : OperationPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    operation.getSuccessors! newCtx = operation.getSuccessors! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind [OperationPtr.getSuccessors!_def]

@[simp, grind =>]
theorem BlockPtr.firstOp!_replaceValue? {b : BlockPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    (b.get! newCtx).firstOp = (b.get! ctx).firstOp := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>]
theorem BlockPtr.lastOp!_replaceValue? {b : BlockPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    (b.get! newCtx).lastOp = (b.get! ctx).lastOp := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>]
theorem BlockPtr.next!_replaceValue? {b : BlockPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    (b.get! newCtx).next = (b.get! ctx).next := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>]
theorem BlockPtr.prev!_replaceValue? {b : BlockPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    (b.get! newCtx).prev = (b.get! ctx).prev := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>]
theorem BlockPtr.parent!_replaceValue? {b : BlockPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    (b.get! newCtx).parent = (b.get! ctx).parent := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>]
theorem OperationPtr.parent!_replaceValue? {op : OperationPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    (op.get! newCtx).parent = (op.get! ctx).parent := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>]
theorem OperationPtr.next!_replaceValue? {op : OperationPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    (op.get! newCtx).next = (op.get! ctx).next := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>]
theorem OperationPtr.prev!_replaceValue? {op : OperationPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    (op.get! newCtx).prev = (op.get! ctx).prev := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>]
theorem OperationPtr.getNumOperands!_replaceValue? {op : OperationPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    op.getNumOperands! newCtx = op.getNumOperands! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>]
theorem OpOperandPtr.owner!_replaceValue? {opr : OpOperandPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    (opr.get! newCtx).owner = (opr.get! ctx).owner := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

/-!
 theorem `OpOperandPtr.value!_replaceValue?` and
 `OperationPtr.getOperands!_replaceValue?` requires Well-formedness
 preservation to be stated.
-/

@[simp, grind =>]
theorem OperationPtr.getNumSuccessors!_replaceValue? {op : OperationPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    op.getNumSuccessors! newCtx = op.getNumSuccessors! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>]
theorem OperationPtr.getNumResults!_replaceValue? {op : OperationPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    op.getNumResults! newCtx = op.getNumResults! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>]
theorem OpResultPtr.owner!_replaceValue? {opr : OpResultPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    (opr.get! newCtx).owner = (opr.get! ctx).owner := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>]
theorem OpResultPtr.index!_replaceValue? {opr : OpResultPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    (opr.get! newCtx).index = (opr.get! ctx).index := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>]
theorem OperationPtr.getNumRegions!_replaceValue? {op : OperationPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    op.getNumRegions! newCtx = op.getNumRegions! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>]
theorem OperationPtr.getRegions_replaceValue? {op : OperationPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    op.getRegion! newCtx index = op.getRegion! ctx index := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>]
theorem BlockPtr.getNumArguments!_replaceValue? {block : BlockPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    block.getNumArguments! newCtx = block.getNumArguments! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>]
theorem BlockArgumentPtr.owner!_replaceValue? {arg : BlockArgumentPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    (arg.get! newCtx).owner = (arg.get! ctx).owner := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>]
theorem BlockArgumentPtr.index!_replaceValue? {arg : BlockArgumentPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    (arg.get! newCtx).index = (arg.get! ctx).index := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

@[simp, grind =>]
theorem RegionPtr.get!_replaceValue? {reg : RegionPtr} :
    Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some newCtx →
    reg.get! newCtx = reg.get! ctx := by
  induction depth generalizing ctx <;> simp only [Rewriter.replaceValue?] <;> grind

end Rewriter.replaceValue?

end Veir
