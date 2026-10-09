module

public import Veir.Rewriter.WfRewriter.Basic
public import Veir.Rewriter.GetSet
public import Veir.Rewriter.WfRewriter.GetSetTactic

import all Veir.Rewriter.WfRewriter.Basic
import all Veir.IR.Basic
import all Veir.IR.GetSet
import all Veir.Rewriter.LinkedList.GetSet
import all Veir.Rewriter.GetSet.BlockArguments
import all Veir.Rewriter.GetSet.BlockOperands
import all Veir.Rewriter.GetSet.CreateOp
import all Veir.Rewriter.GetSet.CreateRegion
import all Veir.Rewriter.GetSet.DetachBlockOperands
import all Veir.Rewriter.GetSet.DetachOperands
import all Veir.Rewriter.GetSet.DetachOp
import all Veir.Rewriter.GetSet.InsertBlock
import all Veir.Rewriter.GetSet.InsertOp
import all Veir.Rewriter.GetSet.Operands
import all Veir.Rewriter.GetSet.Operation
import all Veir.Rewriter.GetSet.Regions
import all Veir.Rewriter.GetSet.ReplaceUse
import all Veir.Rewriter.GetSet.Results
import all Veir.Rewriter.GetSet.Value

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
variable {ctx ctx' : WfIRContext OpInfo}
variable {operation : OperationPtr} {region : RegionPtr} {block : BlockPtr} {value : ValuePtr}
variable {Dialect : Type} [HasOpInfo Dialect] [HasDialect OpInfo Dialect]
variable {dialectOpType : Dialect}
variable {CreateDialect : Type} [HasOpInfo CreateDialect]
  [HasDialect OpInfo CreateDialect]
variable {opType : CreateDialect}
variable {properties : propertiesOf opType}

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
    block.getPrevBlock! ctx'.raw = block.getPrevBlock! ctx.raw := by
  grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.next!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    block.getNextBlock! ctx'.raw = block.getNextBlock! ctx.raw := by
  grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.parent!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    block.getParent! ctx'.raw = block.getParent! ctx.raw := by
  grind

@[grind =>, simp_getset]
theorem BlockPtr.firstOp!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    block.getFirstOp! ctx'.raw =
    match insertionPoint with
    | some ip =>
      if ip.block! ctx.raw = block ∧ ip.prev! ctx.raw = none then some newOp
      else (block.getFirstOp! ctx.raw)
    | none => block.getFirstOp! ctx.raw := by
  simp only [WfRewriter.createOp]
  grind (gen := 20) [cases InsertPoint]

@[grind =>, simp_getset]
theorem BlockPtr.lastOp!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    block.getLastOp! ctx'.raw =
    match insertionPoint with
    | some ip =>
      if ip.block! ctx.raw = block ∧ ip.next = none then some newOp
      else (block.getLastOp! ctx.raw)
    | none => block.getLastOp! ctx.raw := by
  simp only [WfRewriter.createOp]
  grind (gen := 20) [cases InsertPoint]

@[grind =>, simp_getset]
theorem OperationPtr.prev!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    operation.getPrevOp! ctx'.raw =
    match insertionPoint with
    | some ip =>
      if operation = newOp then ip.prev! ctx.raw
      else if operation = ip.next then some newOp
      else (operation.getPrevOp! ctx.raw)
    | none =>
      if operation = newOp then none else (operation.getPrevOp! ctx.raw) := by
  simp only [WfRewriter.createOp]
  grind (gen := 20) [cases InsertPoint]

@[grind =>, simp_getset]
theorem OperationPtr.next!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    operation.getNextOp! ctx'.raw =
    match insertionPoint with
    | some ip =>
      if operation = newOp then ip.next
      else if operation = ip.prev! ctx.raw then some newOp
      else (operation.getNextOp! ctx.raw)
    | none =>
      if operation = newOp then none else (operation.getNextOp! ctx.raw) := by
  simp only [WfRewriter.createOp]
  grind (gen := 20) (splits := 20) [cases InsertPoint]

@[grind =>, simp_getset]
theorem OperationPtr.parent!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    operation.getParent! ctx'.raw =
    if operation = newOp then
      match insertionPoint with
      | some ip => ip.block! ctx.raw
      | none => none
    else (operation.getParent! ctx.raw) := by
  simp only [WfRewriter.createOp]
  grind (gen := 20) [cases InsertPoint, Operation.empty]

@[grind =>, simp_getset]
theorem OperationPtr.getOpType!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    operation.getOpType! ctx'.raw =
    if operation = newOp then ofDialect OpInfo opType else operation.getOpType! ctx.raw := by
  simp only [WfRewriter.createOp]
  grind (gen := 20)

@[grind =>, simp_getset]
theorem OperationPtr.attrs!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    operation.getAttributes! ctx'.raw =
    if operation = newOp then DictionaryAttr.empty else (operation.getAttributes! ctx.raw) := by
  simp only [WfRewriter.createOp]
  grind (gen := 20)

@[grind =>, simp_getset]
theorem OperationPtr.getProperties!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    operation.getProperties! ctx'.raw dialectOpType =
    if operation = newOp then
      if h : ofDialect OpInfo opType = ofDialect OpInfo dialectOpType then
        HasDialect.properties_eq_of_ofDialect_eq h ▸ properties
      else default
    else operation.getProperties! ctx.raw dialectOpType := by
  simp only [WfRewriter.createOp]
  grind (gen := 20) [HasDialect.toDialectProperties_cast_ofDialectProperties_eq]

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
theorem OperationPtr.getBlockOperands!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    operation.getBlockOperands! ctx'.raw =
    if operation = newOp then Array.map operation.getBlockOperand (Array.range blockOperands.size)
    else operation.getBlockOperands! ctx.raw := by
  simp only [OperationPtr.getBlockOperands!_def]
  grind

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
theorem BlockPtr.getBlockArguments!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    block.getBlockArguments! ctx'.raw =
    block.getBlockArguments! ctx.raw := by
  simp only [BlockPtr.getBlockArguments!_def]
  grind

@[simp, grind =>, simp_getset]
theorem RegionPtr.firstBlock!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    region.getFirstBlock! ctx'.raw = region.getFirstBlock! ctx.raw := by
  grind (gen := 20)

@[simp, grind =>, simp_getset]
theorem RegionPtr.lastBlock!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    region.getLastBlock! ctx'.raw = region.getLastBlock! ctx.raw := by
  grind (gen := 20)

@[simp, grind =>, simp_getset]
theorem RegionPtr.parent!_WfRewriter_createOp :
    WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp) →
    region.getParent! ctx'.raw =
    if region ∈ regions then some newOp else (region.getParent! ctx.raw) := by
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

/-! ## `WfRewriter.insertOp` -/

section WfRewriter.insertOp

attribute [local grind] WfRewriter.insertOp

@[simp, grind =>, simp_getset]
theorem BlockPtr.prev!_wfRewriter_insertOp :
    WfRewriter.insertOp ctx newOp insertionPoint newOpIn insIn = some ctx' →
    block.getPrevBlock! ctx'.raw = block.getPrevBlock! ctx.raw := by
  grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.next!_wfRewriter_insertOp :
    WfRewriter.insertOp ctx newOp insertionPoint newOpIn insIn = some ctx' →
    block.getNextBlock! ctx'.raw = block.getNextBlock! ctx.raw := by
  grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.parent!_wfRewriter_insertOp :
    WfRewriter.insertOp ctx newOp insertionPoint newOpIn insIn = some ctx' →
    block.getParent! ctx'.raw = block.getParent! ctx.raw := by
  grind

@[grind =>, simp_getset]
theorem BlockPtr.firstOp!_wfRewriter_insertOp :
    WfRewriter.insertOp ctx newOp insertionPoint newOpIn insIn = some ctx' →
    block.getFirstOp! ctx'.raw =
    if insertionPoint.block! ctx.raw = block ∧ insertionPoint.prev! ctx.raw = none then some newOp
    else (block.getFirstOp! ctx.raw) := by
  grind

@[grind =>, simp_getset]
theorem BlockPtr.lastOp!_wfRewriter_insertOp :
    WfRewriter.insertOp ctx newOp insertionPoint newOpIn insIn = some ctx' →
    block.getLastOp! ctx'.raw =
    if insertionPoint.block! ctx.raw = block ∧ insertionPoint.next = none then some newOp
    else (block.getLastOp! ctx.raw) := by
  grind

@[grind =>, simp_getset]
theorem OperationPtr.prev!_wfRewriter_insertOp :
    WfRewriter.insertOp ctx newOp insertionPoint newOpIn insIn = some ctx' →
    operation.getPrevOp! ctx'.raw =
    if operation = insertionPoint.next then some newOp
    else if operation = newOp then insertionPoint.prev! ctx.raw
    else (operation.getPrevOp! ctx.raw) := by
  grind

@[grind =>, simp_getset]
theorem OperationPtr.next!_wfRewriter_insertOp :
    WfRewriter.insertOp ctx newOp insertionPoint newOpIn insIn = some ctx' →
    operation.getNextOp! ctx'.raw =
    if operation = insertionPoint.prev! ctx.raw then some newOp
    else if operation = newOp then insertionPoint.next
    else (operation.getNextOp! ctx.raw) := by
  grind

@[grind =>, simp_getset]
theorem OperationPtr.parent!_wfRewriter_insertOp :
    WfRewriter.insertOp ctx newOp insertionPoint newOpIn insIn = some ctx' →
    operation.getParent! ctx'.raw =
    if operation = newOp then insertionPoint.block! ctx.raw
    else (operation.getParent! ctx.raw) := by
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getOpType!_wfRewriter_insertOp :
    WfRewriter.insertOp ctx newOp insertionPoint newOpIn insIn = some ctx' →
    operation.getOpType! ctx'.raw = operation.getOpType! ctx.raw := by
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.attrs!_wfRewriter_insertOp :
    WfRewriter.insertOp ctx newOp insertionPoint newOpIn insIn = some ctx' →
    operation.getAttributes! ctx'.raw = operation.getAttributes! ctx.raw := by
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getProperties!_wfRewriter_insertOp :
    WfRewriter.insertOp ctx newOp insertionPoint newOpIn insIn = some ctx' →
    operation.getProperties! ctx'.raw dialectOpType =
      operation.getProperties! ctx.raw dialectOpType := by
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getNumResults!_wfRewriter_insertOp :
    WfRewriter.insertOp ctx newOp insertionPoint newOpIn insIn = some ctx' →
    operation.getNumResults! ctx'.raw = operation.getNumResults! ctx.raw := by
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getNumOperands!_wfRewriter_insertOp :
    WfRewriter.insertOp ctx newOp insertionPoint newOpIn insIn = some ctx' →
    operation.getNumOperands! ctx'.raw = operation.getNumOperands! ctx.raw := by
  grind

@[grind =>, simp_getset]
theorem OperationPtr.getOperand!_wfRewriter_insertOp :
    WfRewriter.insertOp ctx newOp insertionPoint newOpIn insIn = some ctx' →
    operation.getOperand! ctx'.raw index = operation.getOperand! ctx.raw index := by
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getOperands!_wfRewriter_insertOp :
    WfRewriter.insertOp ctx newOp insertionPoint newOpIn insIn = some ctx' →
    operation.getOperands! ctx'.raw = operation.getOperands! ctx.raw := by
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getNumSuccessors!_wfRewriter_insertOp :
    WfRewriter.insertOp ctx newOp insertionPoint newOpIn insIn = some ctx' →
    operation.getNumSuccessors! ctx'.raw = operation.getNumSuccessors! ctx.raw := by
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getBlockOperands!_wfRewriter_insertOp :
    WfRewriter.insertOp ctx newOp insertionPoint newOpIn insIn = some ctx' →
    operation.getBlockOperands! ctx'.raw =
    operation.getBlockOperands! ctx.raw := by
  simp only [OperationPtr.getBlockOperands!_def]
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getSuccessor!_wfRewriter_insertOp :
    WfRewriter.insertOp ctx newOp insertionPoint newOpIn insIn = some ctx' →
    operation.getSuccessor! ctx'.raw index = operation.getSuccessor! ctx.raw index := by
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getSuccessors!_wfRewriter_insertOp :
    WfRewriter.insertOp ctx newOp insertionPoint newOpIn insIn = some ctx' →
    operation.getSuccessors! ctx'.raw = operation.getSuccessors! ctx.raw := by
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getNumRegions!_wfRewriter_insertOp :
    WfRewriter.insertOp ctx newOp insertionPoint newOpIn insIn = some ctx' →
    operation.getNumRegions! ctx'.raw = operation.getNumRegions! ctx.raw := by
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getRegion!_wfRewriter_insertOp :
    WfRewriter.insertOp ctx newOp insertionPoint newOpIn insIn = some ctx' →
    operation.getRegion! ctx'.raw idx = operation.getRegion! ctx.raw idx := by
  grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.getNumArguments!_wfRewriter_insertOp :
    WfRewriter.insertOp ctx newOp insertionPoint newOpIn insIn = some ctx' →
    block.getNumArguments! ctx'.raw = block.getNumArguments! ctx.raw := by
  grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.getBlockArguments!_wfRewriter_insertOp :
    WfRewriter.insertOp ctx newOp insertionPoint newOpIn insIn = some ctx' →
    block.getBlockArguments! ctx'.raw =
    block.getBlockArguments! ctx.raw := by
  simp only [BlockPtr.getBlockArguments!_def]
  grind

@[simp, grind =>, simp_getset]
theorem RegionPtr.firstBlock!_wfRewriter_insertOp :
    WfRewriter.insertOp ctx newOp insertionPoint newOpIn insIn = some ctx' →
    region.getFirstBlock! ctx'.raw = region.getFirstBlock! ctx.raw := by
  grind

@[simp, grind =>, simp_getset]
theorem RegionPtr.lastBlock!_wfRewriter_insertOp :
    WfRewriter.insertOp ctx newOp insertionPoint newOpIn insIn = some ctx' →
    region.getLastBlock! ctx'.raw = region.getLastBlock! ctx.raw := by
  grind

@[simp, grind =>, simp_getset]
theorem RegionPtr.parent!_wfRewriter_insertOp :
    WfRewriter.insertOp ctx newOp insertionPoint newOpIn insIn = some ctx' →
    region.getParent! ctx'.raw = region.getParent! ctx.raw := by
  grind

@[grind =>, simp_getset]
theorem ValuePtr.getType!_wfRewriter_insertOp :
    WfRewriter.insertOp ctx newOp insertionPoint newOpIn insIn = some ctx' →
    value.getType! ctx'.raw = value.getType! ctx.raw := by
  grind

@[grind =>, simp_getset]
theorem OperationPtr.getResultTypes!_wfRewriter_insertOp :
    WfRewriter.insertOp ctx newOp insertionPoint newOpIn insIn = some ctx' →
    operation.getResultTypes! ctx'.raw = operation.getResultTypes! ctx.raw := by
  grind

end WfRewriter.insertOp

/-! ## `WfRewriter.eraseOp` -/

section WfRewriter.eraseOp

variable {op : OperationPtr}

attribute [local grind] WfRewriter.eraseOp

@[simp, grind =]
theorem BlockPtr.prev!_wfRewriter_eraseOp :
    block.getPrevBlock! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw =
    block.getPrevBlock! ctx.raw := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_wfRewriter_eraseOp :
    block.getNextBlock! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw =
    block.getNextBlock! ctx.raw := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_wfRewriter_eraseOp :
    block.getParent! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw =
    block.getParent! ctx.raw := by
  grind

@[grind =]
theorem BlockPtr.firstOp!_wfRewriter_eraseOp :
    block.getFirstOp! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw =
    if block.getFirstOp! ctx.raw = some op ∧ block.InBounds ctx.raw then
      op.getNextOp! ctx.raw
    else
      block.getFirstOp! ctx.raw := by
  simp only [WfRewriter.eraseOp]
  simp [BlockPtr.firstOp!_eraseOp]
  split
  · grind
  · grind [IRContext.WellFormed.firstOp!_eq_some_iff]

@[grind =]
theorem BlockPtr.lastOp!_wfRewriter_eraseOp :
    block.getLastOp! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw =
    if block.getLastOp! ctx.raw = some op ∧ block.InBounds ctx.raw then
      op.getPrevOp! ctx.raw
    else
      block.getLastOp! ctx.raw := by
  grind

@[grind =]
theorem OperationPtr.prev!_wfRewriter_eraseOp :
    operation.InBounds (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw →
    operation.getPrevOp! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw =
    if op.getNextOp! ctx.raw = operation then
      op.getPrevOp! ctx.raw
    else if operation = op then
      none
    else
      operation.getPrevOp! ctx.raw := by
  grind

@[grind =]
theorem OperationPtr.next!_wfRewriter_eraseOp :
    operation.InBounds (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw →
    operation.getNextOp! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw =
    if operation = op.getPrevOp! ctx.raw then
      op.getNextOp! ctx.raw
    else if operation = op then
      none
    else
      operation.getNextOp! ctx.raw := by
  grind

@[grind =]
theorem OperationPtr.parent!_wfRewriter_eraseOp :
    operation.InBounds (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw →
    operation.getParent! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw =
    if operation = op then none else (operation.getParent! ctx.raw) := by
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
    operation.getAttributes! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw =
    operation.getAttributes! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_wfRewriter_eraseOp :
    operation.InBounds (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw →
    operation.getProperties!
      (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw dialectOpType =
    operation.getProperties! ctx.raw dialectOpType := by
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
theorem OperationPtr.getBlockOperands!_wfRewriter_eraseOp :
    operation.InBounds (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw →
    operation.getBlockOperands! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw =
    operation.getBlockOperands! ctx.raw := by
  simp only [OperationPtr.getBlockOperands!_def]
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
theorem BlockPtr.getBlockArguments!_wfRewriter_eraseOp :
    block.getBlockArguments! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw =
    block.getBlockArguments! ctx.raw := by
  simp only [BlockPtr.getBlockArguments!_def]
  grind

@[simp, grind =]
theorem RegionPtr.firstBlock!_wfRewriter_eraseOp :
    region.getFirstBlock! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw =
    region.getFirstBlock! ctx.raw := by
  grind

@[simp, grind =]
theorem RegionPtr.lastBlock!_wfRewriter_eraseOp :
    region.getLastBlock! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw =
    region.getLastBlock! ctx.raw := by
  grind

@[simp, grind =]
theorem RegionPtr.parent!_wfRewriter_eraseOp :
    region.getParent! (WfRewriter.eraseOp ctx op opRegions opUses hOp).raw =
    region.getParent! ctx.raw := by
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
    block.getPrevBlock! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw =
    block.getPrevBlock! ctx.raw := by
  fun_induction WfRewriter.replaceValue <;> grind

@[simp, grind =]
theorem BlockPtr.next!_WfRewriter_replaceValue :
    block.getNextBlock! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw =
    block.getNextBlock! ctx.raw := by
  fun_induction WfRewriter.replaceValue <;> grind

@[simp, grind =]
theorem BlockPtr.parent!_WfRewriter_replaceValue :
    block.getParent! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw =
    block.getParent! ctx.raw := by
  fun_induction WfRewriter.replaceValue <;> grind

@[simp, grind =]
theorem BlockPtr.firstOp!_WfRewriter_replaceValue :
    block.getFirstOp! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw =
    block.getFirstOp! ctx.raw := by
  fun_induction WfRewriter.replaceValue <;> grind

@[simp, grind =]
theorem BlockPtr.lastOp!_WfRewriter_replaceValue :
    block.getLastOp! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw =
    block.getLastOp! ctx.raw := by
  fun_induction WfRewriter.replaceValue <;> grind

@[simp, grind =]
theorem OperationPtr.prev!_WfRewriter_replaceValue :
    operation.getPrevOp! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw =
    operation.getPrevOp! ctx.raw := by
  fun_induction WfRewriter.replaceValue <;> grind

@[simp, grind =]
theorem OperationPtr.next!_WfRewriter_replaceValue :
    operation.getNextOp! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw =
    operation.getNextOp! ctx.raw := by
  fun_induction WfRewriter.replaceValue <;> grind

@[simp, grind =]
theorem OperationPtr.parent!_WfRewriter_replaceValue :
    operation.getParent! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw =
    operation.getParent! ctx.raw := by
  fun_induction WfRewriter.replaceValue <;> grind

@[simp, grind =]
theorem OperationPtr.getOpType!_WfRewriter_replaceValue :
    operation.getOpType! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw =
    operation.getOpType! ctx.raw := by
  fun_induction WfRewriter.replaceValue <;> grind

@[simp, grind =]
theorem OperationPtr.attrs!_WfRewriter_replaceValue :
    operation.getAttributes! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw =
    operation.getAttributes! ctx.raw := by
  fun_induction WfRewriter.replaceValue <;> grind

@[simp, grind =]
theorem OperationPtr.getProperties!_WfRewriter_replaceValue :
    operation.getProperties!
      (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw dialectOpType =
    operation.getProperties! ctx.raw dialectOpType := by
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
theorem OperationPtr.getBlockOperands!_WfRewriter_replaceValue :
    operation.getBlockOperands! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw =
    operation.getBlockOperands! ctx.raw := by
  simp only [OperationPtr.getBlockOperands!_def]
  grind

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
theorem BlockPtr.getBlockArguments!_WfRewriter_replaceValue :
    block.getBlockArguments! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw =
    block.getBlockArguments! ctx.raw := by
  simp only [BlockPtr.getBlockArguments!_def]
  grind

@[simp, grind =]
theorem RegionPtr.firstBlock!_WfRewriter_replaceValue :
    region.getFirstBlock! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw =
    region.getFirstBlock! ctx.raw := by
  fun_induction WfRewriter.replaceValue <;> grind

@[simp, grind =]
theorem RegionPtr.lastBlock!_WfRewriter_replaceValue :
    region.getLastBlock! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw =
    region.getLastBlock! ctx.raw := by
  fun_induction WfRewriter.replaceValue <;> grind

@[simp, grind =]
theorem RegionPtr.parent!_WfRewriter_replaceValue :
    region.getParent! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw =
    region.getParent! ctx.raw := by
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

/-! ## `WfRewriter.setAttributes` -/

section WfRewriter.setAttributes

attribute [local grind] WfRewriter.setAttributes

variable {op : OperationPtr} {newAttrs : DictionaryAttr} {opIn : op.InBounds ctx.raw}

@[simp, grind =]
theorem BlockPtr.prev!_wfRewriter_setAttributes {block : BlockPtr} :
    block.getPrevBlock! ((WfRewriter.setAttributes ctx op newAttrs opIn)).raw =
    block.getPrevBlock! ctx.raw := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_wfRewriter_setAttributes {block : BlockPtr} :
    block.getNextBlock! ((WfRewriter.setAttributes ctx op newAttrs opIn)).raw =
    block.getNextBlock! ctx.raw := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_wfRewriter_setAttributes {block : BlockPtr} :
    block.getParent! ((WfRewriter.setAttributes ctx op newAttrs opIn).raw) =
    block.getParent! ctx.raw := by
  grind

@[simp, grind =]
theorem BlockPtr.firstOp!_wfRewriter_setAttributes {block : BlockPtr} :
    block.getFirstOp! ((WfRewriter.setAttributes ctx op newAttrs opIn)).raw =
    block.getFirstOp! ctx.raw := by
  grind

@[simp, grind =]
theorem BlockPtr.lastOp!_wfRewriter_setAttributes {block : BlockPtr} :
    block.getLastOp! ((WfRewriter.setAttributes ctx op newAttrs opIn)).raw =
    block.getLastOp! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_wfRewriter_setAttributes {op' : OperationPtr} :
    op'.getPrevOp! ((WfRewriter.setAttributes ctx op newAttrs opIn)).raw =
    op'.getPrevOp! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_wfRewriter_setAttributes {op' : OperationPtr} :
    op'.getNextOp! ((WfRewriter.setAttributes ctx op newAttrs opIn)).raw =
    op'.getNextOp! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_wfRewriter_setAttributes {op' : OperationPtr} :
    op'.getParent! ((WfRewriter.setAttributes ctx op newAttrs opIn)).raw =
    op'.getParent! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_wfRewriter_setAttributes {op' : OperationPtr} :
    op'.getOpType! (WfRewriter.setAttributes ctx op newAttrs opIn).raw =
    op'.getOpType! ctx := by
  grind

@[grind =]
theorem OperationPtr.attrs!_wfRewriter_setAttributes {op' : OperationPtr} :
    op'.getAttributes! ((WfRewriter.setAttributes ctx op newAttrs opIn)).raw =
    if op' = op then newAttrs else (op'.getAttributes! ctx.raw)  := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_wfRewriter_setAttributes {op' : OperationPtr} :
    op'.getProperties! (WfRewriter.setAttributes ctx op newAttrs opIn).raw dialectOpType =
    op'.getProperties! ctx.raw dialectOpType := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_wfRewriter_setAttributes {op' : OperationPtr} :
    op'.getNumResults! (WfRewriter.setAttributes ctx op newAttrs opIn).raw =
    op'.getNumResults! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_wfRewriter_setAttributes {op' : OperationPtr} :
    op'.getNumOperands! (WfRewriter.setAttributes ctx op newAttrs opIn).raw =
    op'.getNumOperands! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperand!_wfRewriter_setAttributes {op' : OperationPtr} :
    op'.getOperand! (WfRewriter.setAttributes ctx op newAttrs opIn).raw index =
    op'.getOperand! ctx.raw index := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_wfRewriter_setAttributes {op' : OperationPtr} :
    op'.getOperands! (WfRewriter.setAttributes ctx op newAttrs opIn).raw =
    op'.getOperands! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_wfRewriter_setAttributes {op' : OperationPtr} :
    op'.getNumSuccessors! (WfRewriter.setAttributes ctx op newAttrs opIn).raw =
    op'.getNumSuccessors! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.getBlockOperands!_wfRewriter_setAttributes {op' : OperationPtr} :
    op'.getBlockOperands! (WfRewriter.setAttributes ctx op newAttrs opIn).raw =
    op'.getBlockOperands! ctx.raw := by
  simp only [OperationPtr.getBlockOperands!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getSuccessor!_wfRewriter_setAttributes {op' : OperationPtr} :
    op'.getSuccessor! (WfRewriter.setAttributes ctx op newAttrs opIn).raw index =
    op'.getSuccessor! ctx.raw index := by
  grind

@[simp, grind =]
theorem OperationPtr.getSuccessors!_wfRewriter_setAttributes {op' : OperationPtr} :
    op'.getSuccessors! (WfRewriter.setAttributes ctx op newAttrs opIn).raw =
    op'.getSuccessors! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_wfRewriter_setAttributes {op' : OperationPtr} :
    op'.getNumRegions! (WfRewriter.setAttributes ctx op newAttrs opIn).raw =
    op'.getNumRegions! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_wfRewriter_setAttributes {op' : OperationPtr} :
    op'.getRegions! (WfRewriter.setAttributes ctx op newAttrs opIn).raw =
    op'.getRegions! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_wfRewriter_setAttributes {op' : OperationPtr} :
    op'.getRegion! (WfRewriter.setAttributes ctx op newAttrs opIn).raw index =
    op'.getRegion! ctx.raw index := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_wfRewriter_setAttributes {block : BlockPtr} :
    block.getNumArguments! (WfRewriter.setAttributes ctx op newAttrs opIn).raw =
    block.getNumArguments! ctx.raw := by
  grind

@[simp, grind =]
theorem BlockPtr.getBlockArguments!_wfRewriter_setAttributes {block : BlockPtr} :
    block.getBlockArguments! (WfRewriter.setAttributes ctx op newAttrs opIn).raw =
    block.getBlockArguments! ctx.raw := by
  simp only [BlockPtr.getBlockArguments!_def]
  grind

@[simp, grind =]
theorem RegionPtr.firstBlock!_wfRewriter_setAttributes {region : RegionPtr} :
    region.getFirstBlock! ((WfRewriter.setAttributes ctx op newAttrs opIn)).raw =
    region.getFirstBlock! ctx.raw := by
  grind

@[simp, grind =]
theorem RegionPtr.lastBlock!_wfRewriter_setAttributes {region : RegionPtr} :
    region.getLastBlock! ((WfRewriter.setAttributes ctx op newAttrs opIn)).raw =
    region.getLastBlock! ctx.raw := by
  grind

@[simp, grind =]
theorem RegionPtr.parent!_wfRewriter_setAttributes {region : RegionPtr} :
    region.getParent! ((WfRewriter.setAttributes ctx op newAttrs opIn)).raw =
    region.getParent! ctx.raw := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_wfRewriter_setAttributes {value : ValuePtr} :
    value.getType! (WfRewriter.setAttributes ctx op newAttrs opIn).raw  =
    value.getType! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.getResultTypes!_wfRewriter_setAttributes {op' : OperationPtr} :
    op'.getResultTypes! (WfRewriter.setAttributes ctx op newAttrs opIn).raw =
    op'.getResultTypes! ctx.raw := by
  grind

end WfRewriter.setAttributes

/-! ## `WfRewriter.setProperties` -/

section WfRewriter.setProperties

attribute [local grind] WfRewriter.setProperties

variable {opCode : Dialect} {op : OperationPtr}
         {newProps : propertiesOf opCode}
         {opIn : op.InBounds ctx.raw} {hprop : op.getOpType! ctx.raw = opCode}

@[simp, grind =]
theorem BlockPtr.prev!_wfRewriter_setProperties {block : BlockPtr} :
    block.getPrevBlock! ((WfRewriter.setProperties ctx op opCode newProps opIn hprop)).raw =
    block.getPrevBlock! ctx.raw := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_wfRewriter_setProperties {block : BlockPtr} :
    block.getNextBlock! ((WfRewriter.setProperties ctx op opCode newProps opIn hprop)).raw =
    block.getNextBlock! ctx.raw := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_wfRewriter_setProperties {block : BlockPtr} :
    block.getParent! ((WfRewriter.setProperties ctx op opCode newProps opIn hprop).raw) =
    block.getParent! ctx.raw := by
  grind

@[simp, grind =]
theorem BlockPtr.firstOp!_wfRewriter_setProperties {block : BlockPtr} :
    block.getFirstOp! ((WfRewriter.setProperties ctx op opCode newProps opIn hprop)).raw =
    block.getFirstOp! ctx.raw := by
  grind

@[simp, grind =]
theorem BlockPtr.lastOp!_wfRewriter_setProperties {block : BlockPtr} :
    block.getLastOp! ((WfRewriter.setProperties ctx op opCode newProps opIn hprop)).raw =
    block.getLastOp! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_wfRewriter_setProperties {op' : OperationPtr} :
    op'.getPrevOp! ((WfRewriter.setProperties ctx op opCode newProps opIn hprop)).raw =
    op'.getPrevOp! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_wfRewriter_setProperties {op' : OperationPtr} :
    op'.getNextOp! ((WfRewriter.setProperties ctx op opCode newProps opIn hprop)).raw =
    op'.getNextOp! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_wfRewriter_setProperties {op' : OperationPtr} :
    op'.getParent! ((WfRewriter.setProperties ctx op opCode newProps opIn hprop)).raw =
    op'.getParent! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_wfRewriter_setProperties {op' : OperationPtr} :
    op'.getOpType! (WfRewriter.setProperties ctx op opCode newProps opIn hprop).raw =
    op'.getOpType! ctx := by
  grind

@[simp ,grind =]
theorem OperationPtr.attrs!_wfRewriter_setProperties {op' : OperationPtr} :
    op'.getAttributes! ((WfRewriter.setProperties ctx op opCode newProps opIn hprop)).raw =
    op'.getAttributes! ctx.raw := by
  grind

@[grind =]
theorem OperationPtr.getProperties!_wfRewriter_setProperties
    {GetterDialect : Type} [HasOpInfo GetterDialect]
    [HasDialect OpInfo GetterDialect] {getterOpCode : GetterDialect} {op' : OperationPtr} :
    op'.getProperties!
      (WfRewriter.setProperties ctx op opCode newProps opIn hprop).raw getterOpCode =
    if op' = op then
      if h : ofDialect OpInfo opCode = ofDialect OpInfo getterOpCode then
        HasDialect.toDialectProperties getterOpCode
          (h ▸ HasDialect.ofDialectProperties OpInfo opCode newProps)
      else
        default
    else
      op'.getProperties! ctx.raw getterOpCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_wfRewriter_setProperties {op' : OperationPtr} :
    op'.getNumResults! (WfRewriter.setProperties ctx op opCode newProps opIn hprop).raw =
    op'.getNumResults! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_wfRewriter_setProperties {op' : OperationPtr} :
    op'.getNumOperands! (WfRewriter.setProperties ctx op opCode newProps opIn hprop).raw =
    op'.getNumOperands! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperand!_wfRewriter_setProperties {op' : OperationPtr} :
    op'.getOperand! (WfRewriter.setProperties ctx op opCode newProps opIn hprop).raw index =
    op'.getOperand! ctx.raw index := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_wfRewriter_setProperties {op' : OperationPtr} :
    op'.getOperands! (WfRewriter.setProperties ctx op opCode newProps opIn hprop).raw =
    op'.getOperands! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_wfRewriter_setProperties {op' : OperationPtr} :
    op'.getNumSuccessors! (WfRewriter.setProperties ctx op opCode newProps opIn hprop).raw =
    op'.getNumSuccessors! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.getBlockOperands!_wfRewriter_setProperties {op' : OperationPtr} :
    op'.getBlockOperands! (WfRewriter.setProperties ctx op opCode newProps opIn hprop).raw =
    op'.getBlockOperands! ctx.raw := by
  simp only [OperationPtr.getBlockOperands!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getSuccessor!_wfRewriter_setProperties {op' : OperationPtr} :
    op'.getSuccessor! (WfRewriter.setProperties ctx op opCode newProps opIn hprop).raw index =
    op'.getSuccessor! ctx.raw index := by
  grind

@[simp, grind =]
theorem OperationPtr.getSuccessors!_wfRewriter_setProperties {op' : OperationPtr} :
    op'.getSuccessors! (WfRewriter.setProperties ctx op opCode newProps opIn hprop).raw =
    op'.getSuccessors! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_wfRewriter_setProperties {op' : OperationPtr} :
    op'.getNumRegions! (WfRewriter.setProperties ctx op opCode newProps opIn hprop).raw =
    op'.getNumRegions! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_wfRewriter_setProperties {op' : OperationPtr} :
    op'.getRegions! (WfRewriter.setProperties ctx op opCode newProps opIn hprop).raw =
    op'.getRegions! ctx.raw := by
  grind

@[simp, grind =]
theorem RegionPtr.firstBlock!_wfRewriter_setProperties {region : RegionPtr} :
    region.getFirstBlock! ((WfRewriter.setProperties ctx op opCode newProps opIn hprop)).raw =
    region.getFirstBlock! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_wfRewriter_setProperties {op' : OperationPtr} :
    op'.getRegion! (WfRewriter.setProperties ctx op opCode newProps opIn hprop).raw index =
    op'.getRegion! ctx.raw index := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_wfRewriter_setProperties {block : BlockPtr} :
    block.getNumArguments! (WfRewriter.setProperties ctx op opCode newProps opIn).raw =
    block.getNumArguments! ctx.raw := by
  grind

@[simp, grind =]
theorem BlockPtr.getBlockArguments!_wfRewriter_setProperties {block : BlockPtr} :
    block.getBlockArguments! (WfRewriter.setProperties ctx op opCode newProps opIn).raw =
    block.getBlockArguments! ctx.raw := by
  simp only [BlockPtr.getBlockArguments!_def]
  grind

@[simp, grind =]
theorem RegionPtr.lastBlock!_wfRewriter_setProperties {region : RegionPtr} :
    region.getLastBlock! ((WfRewriter.setProperties ctx op opCode newProps opIn hprop)).raw =
    region.getLastBlock! ctx.raw := by
  grind

@[simp, grind =]
theorem RegionPtr.parent!_wfRewriter_setProperties {region : RegionPtr} :
    region.getParent! ((WfRewriter.setProperties ctx op opCode newProps opIn hprop)).raw =
    region.getParent! ctx.raw := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_wfRewriter_setProperties {value : ValuePtr} :
    value.getType! (WfRewriter.setProperties ctx op opCode newProps opIn hprop).raw  =
    value.getType! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.getResultTypes!_wfRewriter_setProperties {op' : OperationPtr} :
    op'.getResultTypes! (WfRewriter.setProperties ctx op opCode newProps opIn hprop).raw =
    op'.getResultTypes! ctx.raw := by
  grind

end WfRewriter.setProperties

/-! ## `WfRewriter.setType` -/

section WfRewriter.setType

variable {setValue : ValuePtr} {newType : TypeAttr} {hValue : setValue.InBounds ctx.raw}

attribute [local grind] WfRewriter.setType

@[simp, grind =]
theorem BlockPtr.prev!_wfRewriter_setType :
    block.getPrevBlock! (WfRewriter.setType ctx setValue newType hValue).raw =
    block.getPrevBlock! ctx.raw := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_wfRewriter_setType :
    block.getNextBlock! (WfRewriter.setType ctx setValue newType hValue).raw =
    block.getNextBlock! ctx.raw := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_wfRewriter_setType :
    block.getParent! (WfRewriter.setType ctx setValue newType hValue).raw =
    block.getParent! ctx.raw := by
  grind

@[simp, grind =]
theorem BlockPtr.firstOp!_wfRewriter_setType :
    block.getFirstOp! (WfRewriter.setType ctx setValue newType hValue).raw =
    block.getFirstOp! ctx.raw := by
  grind

@[simp, grind =]
theorem BlockPtr.lastOp!_wfRewriter_setType :
    block.getLastOp! (WfRewriter.setType ctx setValue newType hValue).raw =
    block.getLastOp! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_wfRewriter_setType :
    operation.getPrevOp! (WfRewriter.setType ctx setValue newType hValue).raw =
    operation.getPrevOp! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_wfRewriter_setType :
    operation.getNextOp! (WfRewriter.setType ctx setValue newType hValue).raw =
    operation.getNextOp! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_wfRewriter_setType :
    operation.getParent! (WfRewriter.setType ctx setValue newType hValue).raw =
    operation.getParent! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_wfRewriter_setType :
    operation.getOpType! (WfRewriter.setType ctx setValue newType hValue).raw =
    operation.getOpType! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_wfRewriter_setType :
    operation.getAttributes! (WfRewriter.setType ctx setValue newType hValue).raw =
    operation.getAttributes! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_wfRewriter_setType :
    operation.getProperties! (WfRewriter.setType ctx setValue newType hValue).raw dialectOpType =
    operation.getProperties! ctx.raw dialectOpType := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_wfRewriter_setType :
    operation.getNumResults! (WfRewriter.setType ctx setValue newType hValue).raw =
    operation.getNumResults! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_wfRewriter_setType :
    operation.getNumOperands! (WfRewriter.setType ctx setValue newType hValue).raw =
    operation.getNumOperands! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperand!_wfRewriter_setType :
    operation.getOperand! (WfRewriter.setType ctx setValue newType hValue).raw index =
    operation.getOperand! ctx.raw index := by
  grind (gen := 20) [=_ getOperands!.getElem!_eq_getOperand!]

@[simp, grind =]
theorem OperationPtr.getOperands!_wfRewriter_setType :
    operation.getOperands! (WfRewriter.setType ctx setValue newType hValue).raw =
    operation.getOperands! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_wfRewriter_setType :
    operation.getNumSuccessors! (WfRewriter.setType ctx setValue newType hValue).raw =
    operation.getNumSuccessors! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.getBlockOperands!_wfRewriter_setType :
    operation.getBlockOperands! (WfRewriter.setType ctx setValue newType hValue).raw =
    operation.getBlockOperands! ctx.raw := by
  simp only [OperationPtr.getBlockOperands!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getSuccessor!_wfRewriter_setType :
    operation.getSuccessor! (WfRewriter.setType ctx setValue newType hValue).raw index =
    operation.getSuccessor! ctx.raw index := by
  simp only [OperationPtr.getSuccessor!_def]; grind

@[simp, grind =]
theorem OperationPtr.getSuccessors!_wfRewriter_setType :
    operation.getSuccessors! (WfRewriter.setType ctx setValue newType hValue).raw =
    operation.getSuccessors! ctx.raw := by
  simp only [getSuccessors!_def]; grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_wfRewriter_setType :
    operation.getNumRegions! (WfRewriter.setType ctx setValue newType hValue).raw =
    operation.getNumRegions! ctx.raw := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_wfRewriter_setType :
    operation.getRegion! (WfRewriter.setType ctx setValue newType hValue).raw idx =
    operation.getRegion! ctx.raw idx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_wfRewriter_setType :
    block.getNumArguments! (WfRewriter.setType ctx setValue newType hValue).raw =
    block.getNumArguments! ctx.raw := by
  grind

@[simp, grind =]
theorem BlockPtr.getBlockArguments!_wfRewriter_setType :
    block.getBlockArguments! (WfRewriter.setType ctx setValue newType hValue).raw =
    block.getBlockArguments! ctx.raw := by
  simp only [BlockPtr.getBlockArguments!_def]
  grind

@[simp, grind =]
theorem RegionPtr.firstBlock!_wfRewriter_setType :
    region.getFirstBlock! (WfRewriter.setType ctx setValue newType hValue).raw =
    region.getFirstBlock! ctx.raw := by
  grind

@[simp, grind =]
theorem RegionPtr.lastBlock!_wfRewriter_setType :
    region.getLastBlock! (WfRewriter.setType ctx setValue newType hValue).raw =
    region.getLastBlock! ctx.raw := by
  grind

@[simp, grind =]
theorem RegionPtr.parent!_wfRewriter_setType :
    region.getParent! (WfRewriter.setType ctx setValue newType hValue).raw =
    region.getParent! ctx.raw := by
  grind

@[grind =]
theorem ValuePtr.getType!_wfRewriter_setType :
    value.getType! (WfRewriter.setType ctx setValue newType hValue).raw =
    if setValue = value then newType else value.getType! ctx.raw := by
  grind

@[grind =]
theorem OperationPtr.getResultTypes!_wfRewriter_setType :
    operation.getResultTypes! (WfRewriter.setType ctx setValue newType hValue).raw =
    match setValue with
    | .opResult opRes =>
      if opRes.op = operation then
        (operation.getResultTypes! ctx.raw).set! opRes.index newType
      else operation.getResultTypes! ctx.raw
    | .blockArgument _ => operation.getResultTypes! ctx.raw := by
  ext i hi hi'
  · grind
  · have := ValuePtr.getType!_wfRewriter_setType
      (ctx := ctx) (setValue := setValue) (newType := newType) (hValue := hValue)
      (value := operation.getResult i)
    have key : ∀ (r : OpResultPtr), r.op = operation → r.index = i → r = operation.getResult i := by
      rintro ⟨_, _⟩; grind [getResult_def]
    grind (gen := 20)

end WfRewriter.setType

end Veir
