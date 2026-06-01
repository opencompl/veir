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

end Veir
