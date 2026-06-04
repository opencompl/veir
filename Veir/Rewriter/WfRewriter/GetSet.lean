module

public import Veir.Rewriter.WfRewriter.Basic
public import Veir.Rewriter.GetSet
public import Veir.Rewriter.WfRewriter.GetSetTactic

import all Veir.Rewriter.WfRewriter.Basic

/-
The getters we consider are:
* BlockPtr.get! with optionally special cases for:
  * Block.prev
  * Block.next
  * Block.parent
  * Block.firstOp
  * Block.lastOp
* OperationPtr.get! with optionally special cases for:
  * Operation.prev
  * Operation.next
  * Operation.parent
  * Operation.attrs
* OperationPtr.getOpType!
* OperationPtr.getProperties!
* OperationPtr.getNumResults!
* OperationPtr.getNumOperands!
* OperationPtr.getOperand!
* OperationPtr.getOperands!
* OperationPtr.getNumSuccessors!
* OperationPtr.getSuccessor!
* OperationPtr.getSuccessors!
* OperationPtr.getNumRegions!
* OperationPtr.getRegion!
* BlockPtr.getNumArguments!
* RegionPtr.get! with optionally special cases for:
  * firstBlock
  * lastBlock
  * parent
* ValuePtr.getType!
* OperationPtr.getResultTypes!
-/

public section
namespace Veir

variable {OpInfo} [HasOpInfo OpInfo]
variable {ctx ctx' : WfIRContext OpInfo}
variable {operation : OperationPtr} {region : RegionPtr} {block : BlockPtr} {value : ValuePtr}

/-! ## `WfRewriter.createOp` -/

section WfRewriter.createOp

attribute [local grind] WfRewriter.createOp

/-
BlockPtr.firstUse!_WfRewriter_createOp is too complex to be expressed, and should not be needed
in practice, as we should reason at a higher-level abstraction at this point.
-/

@[simp, grind =>, simp_getset]
theorem BlockPtr.prev!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    (block.get! ctx'.raw).prev = (block.get! ctx.raw).prev := by
  grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.next!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    (block.get! ctx'.raw).next = (block.get! ctx.raw).next := by
  grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.parent!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    (block.get! ctx'.raw).parent = (block.get! ctx.raw).parent := by
  grind

@[grind =>, simp_getset]
theorem BlockPtr.firstOp!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    (block.get! ctx'.raw).firstOp =
    match insertionPoint with
    | some ip =>
      if ip.block! ctx.raw = block ∧ ip.prev! ctx.raw = none then some newOp
      else (block.get! ctx.raw).firstOp
    | none => (block.get! ctx.raw).firstOp := by
  simp only [WfRewriter.createOp]
  grind (gen := 20) [cases InsertPoint]

@[grind =>, simp_getset]
theorem BlockPtr.lastOp!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    (block.get! ctx'.raw).lastOp =
    match insertionPoint with
    | some ip =>
      if ip.block! ctx.raw = block ∧ ip.next = none then some newOp
      else (block.get! ctx.raw).lastOp
    | none => (block.get! ctx.raw).lastOp := by
  simp only [WfRewriter.createOp]
  grind (gen := 20) [cases InsertPoint]

@[grind =>, simp_getset]
theorem OperationPtr.prev!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    (operation.get! ctx'.raw).prev =
    match insertionPoint with
    | some ip =>
      if operation = newOp then ip.prev! ctx.raw
      else if operation = ip.next then some newOp
      else (operation.get! ctx.raw).prev
    | none =>
      if operation = newOp then none else (operation.get! ctx.raw).prev := by
  simp only [WfRewriter.createOp]
  grind (gen := 20) [cases InsertPoint]

@[grind =>, simp_getset]
theorem OperationPtr.next!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    (operation.get! ctx'.raw).next =
    match insertionPoint with
    | some ip =>
      if operation = newOp then ip.next
      else if operation = ip.prev! ctx.raw then some newOp
      else (operation.get! ctx.raw).next
    | none =>
      if operation = newOp then none else (operation.get! ctx.raw).next := by
  simp only [WfRewriter.createOp]
  grind (gen := 20) (splits := 20) [cases InsertPoint]

@[grind =>, simp_getset]
theorem OperationPtr.parent!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    (operation.get! ctx'.raw).parent =
    if operation = newOp then
      match insertionPoint with
      | some ip => ip.block! ctx.raw
      | none => none
    else (operation.get! ctx.raw).parent := by
  simp only [WfRewriter.createOp]
  grind (gen := 20) [cases InsertPoint, Operation.empty]

@[grind =>, simp_getset]
theorem OperationPtr.getOpType!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    operation.getOpType! ctx'.raw =
    if operation = newOp then opType else operation.getOpType! ctx.raw := by
  simp only [WfRewriter.createOp]
  grind (gen := 20)

@[grind =>, simp_getset]
theorem OperationPtr.attrs!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    (operation.get! ctx'.raw).attrs =
    if operation = newOp then DictionaryAttr.empty else (operation.get! ctx.raw).attrs := by
  simp only [WfRewriter.createOp]
  grind (gen := 20)

@[grind =>, simp_getset]
theorem OperationPtr.getProperties!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    operation.getProperties! ctx'.raw opType =
    if operation = newOp then properties else operation.getProperties! ctx.raw opType := by
  simp only [WfRewriter.createOp]
  grind (gen := 20)

@[grind =>, simp_getset]
theorem OperationPtr.getNumResults!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    operation.getNumResults! ctx'.raw =
    if operation = newOp then resultTypes.size else operation.getNumResults! ctx.raw := by
  simp only [WfRewriter.createOp]
  grind (gen := 20)

@[grind =>, simp_getset]
theorem OperationPtr.getNumOperands!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    operation.getNumOperands! ctx'.raw =
    if operation = newOp then operands.size else operation.getNumOperands! ctx.raw := by
  simp only [WfRewriter.createOp]
  grind (gen := 20)

@[grind =>, simp_getset]
theorem OperationPtr.getOperand!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    operation.getOperand! ctx'.raw index =
    if operation = newOp then operands[index]! else operation.getOperand! ctx.raw index := by
  simp only [WfRewriter.createOp]
  -- We do not have get-set lemmas for `getOperand!` in `Rewriter.createOp`, so we use the get-set
  -- lemma for `getOperands!` instead.
  grind (gen := 20) [=_ getOperands!.getElem!_eq_getOperand!]

@[grind =>, simp_getset]
theorem OperationPtr.getOperands!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    operation.getOperands! ctx'.raw =
    if operation = newOp then operands else operation.getOperands! ctx.raw := by
  simp only [WfRewriter.createOp]
  grind (gen := 20)

@[grind =>, simp_getset]
theorem OperationPtr.getNumSuccessors!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    operation.getNumSuccessors! ctx'.raw =
    if operation = newOp then blockOperands.size else operation.getNumSuccessors! ctx.raw := by
  grind (gen := 20)

@[grind =>, simp_getset]
theorem OperationPtr.getSuccessor!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    operation.getSuccessor! ctx'.raw index =
    if operation = newOp then blockOperands[index]! else operation.getSuccessor! ctx.raw index := by
  grind (gen := 20)

@[grind =>, simp_getset]
theorem OperationPtr.getSuccessors!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    operation.getSuccessors! ctx'.raw =
    if operation = newOp then blockOperands else operation.getSuccessors! ctx.raw := by
  grind (gen := 20)


@[grind =>, simp_getset]
theorem OperationPtr.getNumRegions!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    operation.getNumRegions! ctx'.raw =
    if operation = newOp then regions.size else operation.getNumRegions! ctx.raw := by
  grind (gen := 20)

@[grind =>, simp_getset]
theorem OperationPtr.getRegion!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    operation.getRegion! ctx'.raw idx =
    if _ : operation = newOp ∧ idx < regions.size then regions[idx]
    else operation.getRegion! ctx.raw idx := by
  grind (gen := 20)

@[simp, grind =>, simp_getset]
theorem BlockPtr.getNumArguments!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    block.getNumArguments! ctx'.raw = block.getNumArguments! ctx.raw := by
  grind (gen := 20)

@[simp, grind =>, simp_getset]
theorem RegionPtr.firstBlock!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    (region.get! ctx'.raw).firstBlock = (region.get! ctx.raw).firstBlock := by
  grind (gen := 20)

@[simp, grind =>, simp_getset]
theorem RegionPtr.lastBlock!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    (region.get! ctx'.raw).lastBlock = (region.get! ctx.raw).lastBlock := by
  grind (gen := 20)

@[simp, grind =>, simp_getset]
theorem RegionPtr.parent!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    (region.get! ctx'.raw).parent =
    if region ∈ regions then some newOp else (region.get! ctx.raw).parent := by
  grind (gen := 20)

@[grind =>, simp_getset]
theorem ValuePtr.getType!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    value.getType! ctx'.raw =
    match value with
    | .opResult opRes =>
      if _ : opRes.op = newOp ∧ opRes.index < resultTypes.size then
        resultTypes[opRes.index]
      else value.getType! ctx.raw
    | .blockArgument _ => value.getType! ctx.raw := by
  grind (gen := 20)

@[grind =>, simp_getset]
theorem OperationPtr.getResultTypes!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    operation.getResultTypes! ctx'.raw =
    if operation = newOp then resultTypes else operation.getResultTypes! ctx.raw := by
  intro h
  ext i hi hi'
  · grind
  · have := ValuePtr.getType!_WfRewriter_createOp h (value := operation.getResult i)
    grind

end WfRewriter.createOp

/-! ## `WfRewriter.insertOp?` -/

section WfRewriter.insertOp?

attribute [local grind] WfRewriter.insertOp?

@[simp, grind =>, simp_getset]
theorem BlockPtr.prev!_wfRewriter_insertOp? :
    WfRewriter.insertOp? ctx newOp insertionPoint newOpIn insIn = some ctx' →
    (block.get! ctx'.raw).prev = (block.get! ctx.raw).prev := by
  grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.next!_wfRewriter_insertOp? :
    WfRewriter.insertOp? ctx newOp insertionPoint newOpIn insIn = some ctx' →
    (block.get! ctx'.raw).next = (block.get! ctx.raw).next := by
  grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.parent!_wfRewriter_insertOp? :
    WfRewriter.insertOp? ctx newOp insertionPoint newOpIn insIn = some ctx' →
    (block.get! ctx'.raw).parent = (block.get! ctx.raw).parent := by
  grind

@[grind =>, simp_getset]
theorem BlockPtr.firstOp!_wfRewriter_insertOp? :
    WfRewriter.insertOp? ctx newOp insertionPoint newOpIn insIn = some ctx' →
    (block.get! ctx'.raw).firstOp =
    if insertionPoint.block! ctx.raw = block ∧ insertionPoint.prev! ctx.raw = none then some newOp
    else (block.get! ctx.raw).firstOp := by
  grind

@[grind =>, simp_getset]
theorem BlockPtr.lastOp!_wfRewriter_insertOp? :
    WfRewriter.insertOp? ctx newOp insertionPoint newOpIn insIn = some ctx' →
    (block.get! ctx'.raw).lastOp =
    if insertionPoint.block! ctx.raw = block ∧ insertionPoint.next = none then some newOp
    else (block.get! ctx.raw).lastOp := by
  grind

@[grind =>, simp_getset]
theorem OperationPtr.prev!_wfRewriter_insertOp? :
    WfRewriter.insertOp? ctx newOp insertionPoint newOpIn insIn = some ctx' →
    (operation.get! ctx'.raw).prev =
    if operation = insertionPoint.next then some newOp
    else if operation = newOp then insertionPoint.prev! ctx.raw
    else (operation.get! ctx.raw).prev := by
  grind

@[grind =>, simp_getset]
theorem OperationPtr.next!_wfRewriter_insertOp? :
    WfRewriter.insertOp? ctx newOp insertionPoint newOpIn insIn = some ctx' →
    (operation.get! ctx'.raw).next =
    if operation = insertionPoint.prev! ctx.raw then some newOp
    else if operation = newOp then insertionPoint.next
    else (operation.get! ctx.raw).next := by
  grind

@[grind =>, simp_getset]
theorem OperationPtr.parent!_wfRewriter_insertOp? :
    WfRewriter.insertOp? ctx newOp insertionPoint newOpIn insIn = some ctx' →
    (operation.get! ctx'.raw).parent =
    if operation = newOp then insertionPoint.block! ctx.raw
    else (operation.get! ctx.raw).parent := by
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getOpType!_wfRewriter_insertOp? :
    WfRewriter.insertOp? ctx newOp insertionPoint newOpIn insIn = some ctx' →
    operation.getOpType! ctx'.raw = operation.getOpType! ctx.raw := by
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.attrs!_wfRewriter_insertOp? :
    WfRewriter.insertOp? ctx newOp insertionPoint newOpIn insIn = some ctx' →
    (operation.get! ctx'.raw).attrs = (operation.get! ctx.raw).attrs := by
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getProperties!_wfRewriter_insertOp? :
    WfRewriter.insertOp? ctx newOp insertionPoint newOpIn insIn = some ctx' →
    operation.getProperties! ctx'.raw opType = operation.getProperties! ctx.raw opType := by
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getNumResults!_wfRewriter_insertOp? :
    WfRewriter.insertOp? ctx newOp insertionPoint newOpIn insIn = some ctx' →
    operation.getNumResults! ctx'.raw = operation.getNumResults! ctx.raw := by
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getNumOperands!_wfRewriter_insertOp? :
    WfRewriter.insertOp? ctx newOp insertionPoint newOpIn insIn = some ctx' →
    operation.getNumOperands! ctx'.raw = operation.getNumOperands! ctx.raw := by
  grind

@[grind =>, simp_getset]
theorem OperationPtr.getOperand!_wfRewriter_insertOp? :
    WfRewriter.insertOp? ctx newOp insertionPoint newOpIn insIn = some ctx' →
    operation.getOperand! ctx'.raw index = operation.getOperand! ctx.raw index := by
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getOperands!_wfRewriter_insertOp? :
    WfRewriter.insertOp? ctx newOp insertionPoint newOpIn insIn = some ctx' →
    operation.getOperands! ctx'.raw = operation.getOperands! ctx.raw := by
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getNumSuccessors!_wfRewriter_insertOp? :
    WfRewriter.insertOp? ctx newOp insertionPoint newOpIn insIn = some ctx' →
    operation.getNumSuccessors! ctx'.raw = operation.getNumSuccessors! ctx.raw := by
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getSuccessor!_wfRewriter_insertOp? :
    WfRewriter.insertOp? ctx newOp insertionPoint newOpIn insIn = some ctx' →
    operation.getSuccessor! ctx'.raw index = operation.getSuccessor! ctx.raw index := by
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getSuccessors!_wfRewriter_insertOp? :
    WfRewriter.insertOp? ctx newOp insertionPoint newOpIn insIn = some ctx' →
    operation.getSuccessors! ctx'.raw = operation.getSuccessors! ctx.raw := by
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getNumRegions!_wfRewriter_insertOp? :
    WfRewriter.insertOp? ctx newOp insertionPoint newOpIn insIn = some ctx' →
    operation.getNumRegions! ctx'.raw = operation.getNumRegions! ctx.raw := by
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getRegion!_wfRewriter_insertOp? :
    WfRewriter.insertOp? ctx newOp insertionPoint newOpIn insIn = some ctx' →
    operation.getRegion! ctx'.raw idx = operation.getRegion! ctx.raw idx := by
  grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.getNumArguments!_wfRewriter_insertOp? :
    WfRewriter.insertOp? ctx newOp insertionPoint newOpIn insIn = some ctx' →
    block.getNumArguments! ctx'.raw = block.getNumArguments! ctx.raw := by
  grind

@[simp, grind =>, simp_getset]
theorem RegionPtr.firstBlock!_wfRewriter_insertOp? :
    WfRewriter.insertOp? ctx newOp insertionPoint newOpIn insIn = some ctx' →
    (region.get! ctx'.raw).firstBlock = (region.get! ctx.raw).firstBlock := by
  grind

@[simp, grind =>, simp_getset]
theorem RegionPtr.lastBlock!_wfRewriter_insertOp? :
    WfRewriter.insertOp? ctx newOp insertionPoint newOpIn insIn = some ctx' →
    (region.get! ctx'.raw).lastBlock = (region.get! ctx.raw).lastBlock := by
  grind

@[simp, grind =>, simp_getset]
theorem RegionPtr.parent!_wfRewriter_insertOp? :
    WfRewriter.insertOp? ctx newOp insertionPoint newOpIn insIn = some ctx' →
    (region.get! ctx'.raw).parent = (region.get! ctx.raw).parent := by
  grind

@[grind =>, simp_getset]
theorem ValuePtr.getType!_wfRewriter_insertOp? :
    WfRewriter.insertOp? ctx newOp insertionPoint newOpIn insIn = some ctx' →
    value.getType! ctx'.raw = value.getType! ctx.raw := by
  grind

@[grind =>, simp_getset]
theorem OperationPtr.getResultTypes!_wfRewriter_insertOp? :
    WfRewriter.insertOp? ctx newOp insertionPoint newOpIn insIn = some ctx' →
    operation.getResultTypes! ctx'.raw = operation.getResultTypes! ctx.raw := by
  grind

end WfRewriter.insertOp?

/-! ## `WfRewriter.eraseOp` -/

section WfRewriter.eraseOp

variable {op : OperationPtr}

attribute [local grind] WfRewriter.eraseOp

@[simp, grind =]
theorem BlockPtr.prev!_wfRewriter_eraseOp :
    (block.get! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw).prev =
    (block.get! ctx.raw).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_wfRewriter_eraseOp :
    (block.get! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw).next =
    (block.get! ctx.raw).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_wfRewriter_eraseOp :
    (block.get! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw).parent =
    (block.get! ctx.raw).parent := by
  grind

@[grind =]
theorem BlockPtr.firstOp!_wfRewriter_eraseOp :
    (block.get! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw).firstOp =
    if (block.get! ctx.raw).firstOp = some op ∧ block.InBounds ctx.raw then
      (op.get! ctx.raw).next
    else
      (block.get! ctx.raw).firstOp := by
  simp only [WfRewriter.eraseOp]
  simp [BlockPtr.firstOp!_eraseOp]
  split
  · grind
  · grind [IRContext.WellFormed.firstOp!_eq_some_iff]

@[grind =]
theorem BlockPtr.lastOp!_wfRewriter_eraseOp :
    (block.get! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw).lastOp =
    if (block.get! ctx.raw).lastOp = some op ∧ block.InBounds ctx.raw then
      (op.get! ctx.raw).prev
    else
      (block.get! ctx.raw).lastOp := by
  grind

@[grind =]
theorem OperationPtr.prev!_wfRewriter_eraseOp :
    operation.InBounds (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw →
    (operation.get! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw).prev =
    if (op.get! ctx.raw).next = operation then
      (op.get! ctx.raw).prev
    else if operation = op then
      none
    else
      (operation.get! ctx.raw).prev := by
  grind

@[grind =]
theorem OperationPtr.next!_wfRewriter_eraseOp :
    operation.InBounds (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw →
    (operation.get! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw).next =
    if operation = (op.get! ctx.raw).prev then
      (op.get! ctx.raw).next
    else if operation = op then
      none
    else
      (operation.get! ctx.raw).next := by
  grind

@[grind =]
theorem OperationPtr.parent!_wfRewriter_eraseOp :
    operation.InBounds (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw →
    (operation.get! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw).parent =
    if operation = op then none else (operation.get! ctx.raw).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_wfRewriter_eraseOp :
    operation.InBounds (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw →
    operation.getOpType! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw =
    operation.getOpType! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_wfRewriter_eraseOp :
    operation.InBounds (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw →
    (operation.get! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw).attrs =
    (operation.get! ctx.raw).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_wfRewriter_eraseOp :
    operation.InBounds (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw →
    operation.getProperties! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw opType =
    operation.getProperties! ctx.raw opType := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_wfRewriter_eraseOp :
    operation.InBounds (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw →
    operation.getNumResults! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw =
    operation.getNumResults! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_wfRewriter_eraseOp :
    operation.InBounds (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw →
    operation.getNumOperands! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw =
    operation.getNumOperands! ctx.raw := by
  grind

@[grind =]
theorem OperationPtr.getOperand!_wfRewriter_eraseOp :
    operation.InBounds (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw →
    operation.getOperand! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw index =
    operation.getOperand! ctx.raw index := by
  grind [=_ getOperands!.getElem!_eq_getOperand!]

@[simp, grind =]
theorem OperationPtr.getOperands!_wfRewriter_eraseOp :
    operation.InBounds (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw →
    operation.getOperands! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw =
    operation.getOperands! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_wfRewriter_eraseOp :
    operation.InBounds (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw →
    operation.getNumSuccessors! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw =
    operation.getNumSuccessors! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.getSuccessor!_wfRewriter_eraseOp :
    operation.InBounds (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw →
    operation.getSuccessor! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw index =
    operation.getSuccessor! ctx.raw index := by
  grind

@[simp, grind =]
theorem OperationPtr.getSuccessors!_wfRewriter_eraseOp :
    operation.InBounds (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw →
    operation.getSuccessors! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw =
    operation.getSuccessors! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_wfRewriter_eraseOp :
    operation.InBounds (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw →
    operation.getNumRegions! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw =
    operation.getNumRegions! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_wfRewriter_eraseOp :
    operation.InBounds (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw →
    operation.getRegion! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw idx =
    operation.getRegion! ctx.raw idx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_wfRewriter_eraseOp :
    block.getNumArguments! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw =
    block.getNumArguments! ctx.raw := by
  grind

@[simp, grind =]
theorem RegionPtr.firstBlock!_wfRewriter_eraseOp :
    (region.get! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw).firstBlock =
    (region.get! ctx.raw).firstBlock := by
  grind

@[simp, grind =]
theorem RegionPtr.lastBlock!_wfRewriter_eraseOp :
    (region.get! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw).lastBlock =
    (region.get! ctx.raw).lastBlock := by
  grind

@[simp, grind =]
theorem RegionPtr.parent!_wfRewriter_eraseOp :
    (region.get! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw).parent =
    (region.get! ctx.raw).parent := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_wfRewriter_eraseOp :
    value.InBounds (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw →
    value.getType! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw =
    value.getType! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.getResultTypes!_wfRewriter_eraseOp :
    operation.InBounds (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw →
    operation.getResultTypes! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw =
    operation.getResultTypes! ctx.raw := by
  intro h
  ext i hi hi'
  · grind
  · have := @ValuePtr.getType!_wfRewriter_eraseOp _ _ ctx (operation.getResult i)
    grind

end WfRewriter.eraseOp

/-! ## `WfRewriter.replaceValue` -/

section WfRewriter.replaceValue

variable {oldValue newValue : ValuePtr} {oldIn : oldValue.InBounds ctx.raw} {newIn : newValue.InBounds ctx.raw}
variable {ne : oldValue ≠ newValue}

attribute [local grind] Id.run

@[simp, grind =]
theorem BlockPtr.prev!_WfRewriter_replaceValue :
    (block.get! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw).prev =
    (block.get! ctx.raw).prev := by
  fun_induction WfRewriter.replaceValue <;> grind

@[simp, grind =]
theorem BlockPtr.next!_WfRewriter_replaceValue :
    (block.get! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw).next =
    (block.get! ctx.raw).next := by
  fun_induction WfRewriter.replaceValue <;> grind

@[simp, grind =]
theorem BlockPtr.parent!_WfRewriter_replaceValue :
    (block.get! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw).parent =
    (block.get! ctx.raw).parent := by
  fun_induction WfRewriter.replaceValue <;> grind

@[simp, grind =]
theorem BlockPtr.firstOp!_WfRewriter_replaceValue :
    (block.get! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw).firstOp =
    (block.get! ctx.raw).firstOp := by
  fun_induction WfRewriter.replaceValue <;> grind

@[simp, grind =]
theorem BlockPtr.lastOp!_WfRewriter_replaceValue :
    (block.get! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw).lastOp =
    (block.get! ctx.raw).lastOp := by
  fun_induction WfRewriter.replaceValue <;> grind

@[simp, grind =]
theorem OperationPtr.prev!_WfRewriter_replaceValue :
    (operation.get! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw).prev =
    (operation.get! ctx.raw).prev := by
  fun_induction WfRewriter.replaceValue <;> grind

@[simp, grind =]
theorem OperationPtr.next!_WfRewriter_replaceValue :
    (operation.get! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw).next =
    (operation.get! ctx.raw).next := by
  fun_induction WfRewriter.replaceValue <;> grind

@[simp, grind =]
theorem OperationPtr.parent!_WfRewriter_replaceValue :
    (operation.get! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw).parent =
    (operation.get! ctx.raw).parent := by
  fun_induction WfRewriter.replaceValue <;> grind

@[simp, grind =]
theorem OperationPtr.getOpType!_WfRewriter_replaceValue :
    operation.getOpType! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw =
    operation.getOpType! ctx.raw := by
  fun_induction WfRewriter.replaceValue <;> grind

@[simp, grind =]
theorem OperationPtr.attrs!_WfRewriter_replaceValue :
    (operation.get! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw).attrs =
    (operation.get! ctx.raw).attrs := by
  fun_induction WfRewriter.replaceValue <;> grind

@[simp, grind =]
theorem OperationPtr.getProperties!_WfRewriter_replaceValue :
    operation.getProperties! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw opType =
    operation.getProperties! ctx.raw opType := by
  fun_induction WfRewriter.replaceValue <;> grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_WfRewriter_replaceValue :
    operation.getNumResults! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw =
    operation.getNumResults! ctx.raw := by
  fun_induction WfRewriter.replaceValue <;> grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_WfRewriter_replaceValue :
    operation.getNumOperands! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw =
    operation.getNumOperands! ctx.raw := by
  fun_induction WfRewriter.replaceValue <;> grind

@[grind =]
theorem OperationPtr.getOperand!_WfRewriter_replaceValue :
    operation.InBounds ctx.raw →
    index < operation.getNumOperands! ctx.raw →
    operation.getOperand! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw index =
    if operation.getOperand! ctx.raw index = oldValue then
      newValue
    else
      operation.getOperand! ctx.raw index := by
  intro h₁ h₂
  fun_induction WfRewriter.replaceValue
  rename_i ctx neValues oldIn newIn hi
  split
  · simp only [Id.run_pure, right_eq_ite_iff]
    intro holdValue
    suffices oldValue.hasUses! ctx.raw by grind [ValuePtr.hasUses!_def]
    grind
  · grind [OpOperandPtr.inBounds_def]

@[grind =]
theorem OperationPtr.getOperands!_WfRewriter_replaceValue :
    operation.InBounds ctx.raw →
    operation.getOperands! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw =
    (operation.getOperands! ctx.raw).map (fun v => if v = oldValue then newValue else v) := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_WfRewriter_replaceValue :
    operation.getNumSuccessors! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw =
    operation.getNumSuccessors! ctx.raw := by
  fun_induction WfRewriter.replaceValue <;> grind

@[simp, grind =]
theorem OperationPtr.getSuccessor!_WfRewriter_replaceValue :
    operation.getSuccessor! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw index =
    operation.getSuccessor! ctx.raw index := by
  fun_induction WfRewriter.replaceValue <;> grind

@[simp, grind =]
theorem OperationPtr.getSuccessors!_WfRewriter_replaceValue :
    operation.getSuccessors! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw =
    operation.getSuccessors! ctx.raw := by
  fun_induction WfRewriter.replaceValue <;> grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_WfRewriter_replaceValue :
    operation.getNumRegions! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw =
    operation.getNumRegions! ctx.raw := by
  fun_induction WfRewriter.replaceValue <;> grind

@[simp, grind =]
theorem OperationPtr.getRegion!_WfRewriter_replaceValue :
    operation.getRegion! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw idx =
    operation.getRegion! ctx.raw idx := by
  fun_induction WfRewriter.replaceValue <;> grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_WfRewriter_replaceValue :
    block.getNumArguments! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw =
    block.getNumArguments! ctx.raw := by
  fun_induction WfRewriter.replaceValue <;> grind

@[simp, grind =]
theorem RegionPtr.firstBlock!_WfRewriter_replaceValue :
    (region.get! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw).firstBlock =
    (region.get! ctx.raw).firstBlock := by
  fun_induction WfRewriter.replaceValue <;> grind

@[simp, grind =]
theorem RegionPtr.lastBlock!_WfRewriter_replaceValue :
    (region.get! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw).lastBlock =
    (region.get! ctx.raw).lastBlock := by
  fun_induction WfRewriter.replaceValue <;> grind

@[simp, grind =]
theorem RegionPtr.parent!_WfRewriter_replaceValue :
    (region.get! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw).parent =
    (region.get! ctx.raw).parent := by
  fun_induction WfRewriter.replaceValue <;> grind

@[simp, grind =]
theorem ValuePtr.getType!_WfRewriter_replaceValue :
    value.getType! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw =
    value.getType! ctx.raw := by
  fun_induction WfRewriter.replaceValue <;> grind

@[simp, grind =]
theorem OperationPtr.getResultTypes!_WfRewriter_replaceValue :
    operation.getResultTypes! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw =
    operation.getResultTypes! ctx.raw := by
  ext i hi hi'
  · grind
  · have := @ValuePtr.getType!_WfRewriter_replaceValue _ _ ctx (operation.getResult i)
    grind

end WfRewriter.replaceValue

end Veir
