module

public import Veir.IR.OpInfo
public import Veir.IR.WellFormed
public import Veir.Rewriter.InsertPoint
public import Veir.Rewriter.Basic

import Veir.Rewriter.WellFormed

public section
namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]

/-- Insert an operation at a given location. -/
@[inline]
def WfRewriter.insertOp? (wfCtx : WfIRContext OpInfo) (newOp : OperationPtr)
    (insertionPoint : InsertPoint)
    (newOpIn : newOp.InBounds wfCtx.raw := by grind)
    (insIn : insertionPoint.InBounds wfCtx.raw := by grind)
    : Option (WfIRContext OpInfo) := do
  rlet ctx ← Rewriter.insertOp? wfCtx newOp insertionPoint newOpIn insIn (by grind)
  return ⟨ctx, by grind [Rewriter.insertOp?_WellFormed]⟩

/-- Detach an operation from its parent. -/
@[inline]
def WfRewriter.detachOp (wfCtx : WfIRContext OpInfo) (op : OperationPtr)
    (hIn : op.InBounds wfCtx.raw)
    (hasParent : (op.get! wfCtx.raw).parent.isSome)
    : WfIRContext OpInfo :=
  ⟨Rewriter.detachOp wfCtx op (by grind) hIn (by grind),
    by grind [Rewriter.detachOp_WellFormed]⟩

/--
Detach an operation from its parent if it has one.
If it has no parent, return the context unchanged.
-/
@[inline]
def WfRewriter.detachOpIfAttached (wfCtx : WfIRContext OpInfo) (op : OperationPtr)
    (hop : op.InBounds wfCtx.raw := by grind)
    : WfIRContext OpInfo :=
  ⟨Rewriter.detachOpIfAttached wfCtx op (by grind) hop,
    by grind [Rewriter.detachOpIfAttached_WellFormed]⟩

/-- Erase an operation. -/
@[inline]
def WfRewriter.eraseOp (wfCtx : WfIRContext OpInfo) (op : OperationPtr)
    (opRegions : op.getNumRegions! wfCtx.raw = 0 := by grind)
    (opUses : !op.hasUses! wfCtx.raw := by grind)
    (hOp : op.InBounds wfCtx.raw := by grind)
    : WfIRContext OpInfo :=
  ⟨Rewriter.eraseOp wfCtx op (by grind) hOp,
    by grind [Rewriter.eraseOp_WellFormed]⟩

/-- Insert a block at a given location. -/
@[inline]
def WfRewriter.insertBlock? (wfCtx : WfIRContext OpInfo) (newBlock : BlockPtr)
    (insertionPoint : BlockInsertPoint)
    (newBlockIn : newBlock.InBounds wfCtx.raw := by grind)
    (insIn : insertionPoint.InBounds wfCtx.raw := by grind)
    : Option (WfIRContext OpInfo) := do
  rlet h: ctx ← Rewriter.insertBlock? wfCtx newBlock insertionPoint newBlockIn insIn (by grind)
  return ⟨ctx, by grind [Rewriter.insertBlock?_WellFormed]⟩

/-- Replace the operand of an operation with a new value. -/
@[inline]
def WfRewriter.replaceOperand (wfCtx : WfIRContext OpInfo) (use : OpOperandPtr) (newValue : ValuePtr)
    (useIn : use.InBounds wfCtx.raw := by grind)
    (newIn : newValue.InBounds wfCtx.raw := by grind)
    : WfIRContext OpInfo :=
  ⟨Rewriter.replaceUse wfCtx use newValue useIn newIn (by grind),
    by grind [Rewriter.replaceUse_WellFormed]⟩

/-- Replace a value with another value. -/
@[inline]
def WfRewriter.replaceValue (wfCtx : WfIRContext OpInfo) (oldValue newValue : ValuePtr)
    (oldIn : oldValue.InBounds wfCtx.raw := by grind)
    (newIn : newValue.InBounds wfCtx.raw := by grind)
    : Option (WfIRContext OpInfo) := do
  rlet h: ctx ← Rewriter.replaceValue? wfCtx oldValue newValue oldIn newIn (by grind)
  return ⟨ctx, by grind [Rewriter.replaceValue?_WellFormed, Option.maybe₁_def]⟩

/--
Replace all results of an operation with the results of another.
Erase the replaced operation.
-/
@[inline]
def WfRewriter.replaceOp? (wfCtx : WfIRContext OpInfo) (oldOp newOp : OperationPtr)
    (opNe : oldOp ≠ newOp := by grind)
    (hpar : (oldOp.get! wfCtx.raw).parent.isSome = true := by grind)
    (noRegions : oldOp.getNumRegions! wfCtx.raw = 0 := by grind)
    (oldIn : oldOp.InBounds wfCtx.raw := by grind)
    (newIn : newOp.InBounds wfCtx.raw := by grind)
    : Option (WfIRContext OpInfo) := do
  rlet h: ctx ← Rewriter.replaceOp? wfCtx oldOp newOp oldIn newIn (by grind) (by grind)
  return ⟨ctx, by apply IRContext.wellFormed_replaceOp? (hNewCtx := h) <;> grind⟩

/-- Create a new block and insert it at a given location. -/
@[inline]
def WfRewriter.createBlock (wfCtx : WfIRContext OpInfo)
    (insertionPoint : Option BlockInsertPoint)
    (hip : insertionPoint.maybe BlockInsertPoint.InBounds wfCtx.raw)
    : Option (WfIRContext OpInfo × BlockPtr) := do
  rlet (ctx, blk) ← Rewriter.createBlock wfCtx insertionPoint (by grind) hip
  return (⟨ctx, by grind [Rewriter.createBlock_WellFormed]⟩, blk)

/-- Create a new region. -/
@[inline]
def WfRewriter.createRegion (wfCtx : WfIRContext OpInfo)
    : Option (WfIRContext OpInfo × RegionPtr) := do
  rlet (ctx, reg) ← Rewriter.createRegion wfCtx
  return (⟨ctx, by grind [IRContext.wellFormed_Rewriter_createRegion]⟩, reg)

/-- Insert a region at the end of an operation's region list. -/
@[inline]
def WfRewriter.pushRegion (wfCtx : WfIRContext OpInfo) (op : OperationPtr) (region : RegionPtr)
    (hop : op.InBounds wfCtx.raw := by grind)
    (hregion : region.InBounds wfCtx.raw := by grind)
    (hRegionParent : (region.get! wfCtx.raw).parent = none := by grind)
    : WfIRContext OpInfo :=
  ⟨Rewriter.pushRegion wfCtx op region hop hregion hRegionParent,
    by grind [IRContext.wellFormed_Rewriter_pushRegion]⟩

/-- Insert a result at the end of an operation's result list. -/
@[inline]
def WfRewriter.pushResult (wfCtx : WfIRContext OpInfo) (op : OperationPtr) (type : TypeAttr)
    (hop : op.InBounds wfCtx.raw := by grind)
    : WfIRContext OpInfo :=
  ⟨Rewriter.pushResult wfCtx op type hop,
    by grind [IRContext.wellFormed_Rewriter_pushResult]⟩

/-- Insert an operand at the end of an operation's operand list. -/
@[inline]
def WfRewriter.pushOperand (wfCtx : WfIRContext OpInfo) (opPtr : OperationPtr) (valuePtr : ValuePtr)
    (opPtrInBounds : opPtr.InBounds wfCtx.raw := by grind)
    (valueInBounds : valuePtr.InBounds wfCtx.raw := by grind)
    : WfIRContext OpInfo :=
  ⟨Rewriter.pushOperand wfCtx opPtr valuePtr opPtrInBounds valueInBounds (by grind),
    by grind [Rewriter.pushOperand_WellFormed]⟩

/-- Insert a block operand at the end of an operation's block operand list. -/
@[inline]
def WfRewriter.pushBlockOperand (wfCtx : WfIRContext OpInfo) (opPtr : OperationPtr) (blockPtr : BlockPtr)
    (opPtrInBounds : opPtr.InBounds wfCtx.raw := by grind)
    (blockInBounds : blockPtr.InBounds wfCtx.raw := by grind)
    : WfIRContext OpInfo :=
  ⟨Rewriter.pushBlockOperand wfCtx opPtr blockPtr opPtrInBounds blockInBounds (by grind),
    by grind [Rewriter.pushBlockOperand_WellFormed]⟩

/-- Create an operation and insert it at a given location. -/
@[inline]
def WfRewriter.createOp (wfCtx : WfIRContext OpInfo) (opType : OpInfo)
    (resultTypes : Array TypeAttr) (operands : Array ValuePtr) (blockOperands : Array BlockPtr)
    (regions : Array RegionPtr) (properties : HasOpInfo.propertiesOf opType)
    (insertionPoint : Option InsertPoint)
    (hoper : ∀ oper, oper ∈ operands → oper.InBounds wfCtx.raw := by grind)
    (hblockOperands : ∀ oper, oper ∈ blockOperands → oper.InBounds wfCtx.raw := by grind)
    (hregions : ∀ reg, reg ∈ regions → reg.InBounds wfCtx.raw := by grind)
    (hins : insertionPoint.maybe InsertPoint.InBounds wfCtx.raw := by grind)
    : Option (WfIRContext OpInfo × OperationPtr) := do
  rlet (ctx, op) ← Rewriter.createOp wfCtx opType resultTypes operands blockOperands regions
    properties insertionPoint hoper hblockOperands hregions hins (by grind)
  return (⟨ctx, by grind [Rewriter.createOp_WellFormed]⟩, op)

/--
Create a new IR context with a single `builtin.module` operation at the top-level.
The operation contains a single region, which contains a single empty block.
-/
@[inline]
def WfIRContext.create (OpInfo : Type) [HasOpInfo OpInfo]
    : Option (WfIRContext OpInfo × OperationPtr) := do
  rlet (ctx, op) ← IRContext.create OpInfo
  return (⟨ctx, by grind [IRContext.wellFormed_IRContext_create]⟩, op)

end Veir
