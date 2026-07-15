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
def WfRewriter.insertOp (wfCtx : WfIRContext OpInfo) (newOp : OperationPtr)
    (insertionPoint : InsertPoint)
    (newOpIn : newOp.InBounds wfCtx.raw := by grind)
    (insIn : insertionPoint.InBounds wfCtx.raw := by grind)
    : Option (WfIRContext OpInfo) := do
  rlet ctx ← Rewriter.insertOp wfCtx newOp insertionPoint newOpIn insIn (by grind)
  return ⟨ctx, by grind [Rewriter.insertOp_WellFormed]⟩

/-- Insert an operation at a given location, panicking if the insertion point is out of bounds,
if the new operation is out of bounds, or if the insertion point doesn't have a parent block. -/
def WfRewriter.insertOp! (wfCtx : WfIRContext OpInfo) (newOp : OperationPtr)
    (insertionPoint : InsertPoint)
    : WfIRContext OpInfo :=
  if newOpIn : newOp.InBounds wfCtx.raw then
    if insIn : insertionPoint.InBounds wfCtx.raw then
      if let some ctx := WfRewriter.insertOp wfCtx newOp insertionPoint then
        ctx
      else
        panic! "WfRewriter.insertOp! failed: insertion point does not have a parent block"
    else
      panic! "WfRewriter.insertOp! failed: insertion point is out of bounds"
  else
    panic! "WfRewriter.insertOp! failed: new operation is out of bounds"

/-- Detach an operation from its parent. -/
@[inline]
def WfRewriter.detachOp (wfCtx : WfIRContext OpInfo) (op : OperationPtr)
    (hIn : op.InBounds wfCtx.raw)
    (hasParent : (op.get! wfCtx.raw).parent.isSome)
    : WfIRContext OpInfo :=
  ⟨Rewriter.detachOp wfCtx op (by grind) hIn (by grind),
    by grind [Rewriter.detachOp_WellFormed]⟩

/-- Detach an operation from its parent, panicking if the operation is out of bounds or if it
does not have a parent. -/
def WfRewriter.detachOp! (wfCtx : WfIRContext OpInfo) (op : OperationPtr)
    : WfIRContext OpInfo :=
  if hIn : op.InBounds wfCtx.raw then
    if hasParent : (op.get! wfCtx.raw).parent.isSome then
      WfRewriter.detachOp wfCtx op hIn hasParent
    else
      panic! "WfRewriter.detachOp! failed: operation does not have a parent"
  else
    panic! "WfRewriter.detachOp! failed: operation is out of bounds"

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

/--
Detach an operation from its parent if it has one, panicking if the operation is out of bounds.
If it has no parent, return the context unchanged.
-/
def WfRewriter.detachOpIfAttached! (wfCtx : WfIRContext OpInfo) (op : OperationPtr)
    : WfIRContext OpInfo :=
  if hop : op.InBounds wfCtx.raw then
    WfRewriter.detachOpIfAttached wfCtx op hop
  else
    panic! "WfRewriter.detachOpIfAttached! failed: operation is out of bounds"

/-- Erase an operation. -/
@[inline]
def WfRewriter.eraseOp (wfCtx : WfIRContext OpInfo) (op : OperationPtr)
    (opRegions : op.getNumRegions! wfCtx.raw = 0 := by grind)
    (opUses : !op.hasUses! wfCtx.raw := by grind)
    (hOp : op.InBounds wfCtx.raw := by grind)
    : WfIRContext OpInfo :=
  ⟨Rewriter.eraseOp wfCtx op (by grind) hOp,
    by grind [Rewriter.eraseOp_WellFormed]⟩

/-- Erase an operation, panicking if the operation is out of bounds, has regions, or has uses. -/
def WfRewriter.eraseOp! (wfCtx : WfIRContext OpInfo) (op : OperationPtr)
    : WfIRContext OpInfo :=
  if hOp : op.InBounds wfCtx.raw then
    if opRegions : op.getNumRegions! wfCtx.raw = 0 then
      if opUses : !op.hasUses! wfCtx.raw then
        WfRewriter.eraseOp wfCtx op opRegions opUses hOp
      else
        panic! "WfRewriter.eraseOp! failed: operation has uses"
    else
      panic! "WfRewriter.eraseOp! failed: operation has regions"
  else
    panic! "WfRewriter.eraseOp! failed: operation is out of bounds"

/-- Insert a block at a given location. -/
@[inline]
def WfRewriter.insertBlock (wfCtx : WfIRContext OpInfo) (newBlock : BlockPtr)
    (insertionPoint : BlockInsertPoint)
    (newBlockIn : newBlock.InBounds wfCtx.raw := by grind)
    (insIn : insertionPoint.InBounds wfCtx.raw := by grind)
    : Option (WfIRContext OpInfo) := do
  rlet h: ctx ← Rewriter.insertBlock wfCtx newBlock insertionPoint newBlockIn insIn (by grind)
  return ⟨ctx, by grind [Rewriter.insertBlock_WellFormed]⟩

/-- Insert a block at a given location, panicking if the insertion point is out of bounds,
if the new block is out of bounds, or if the insertion point doesn't have a parent region. -/
def WfRewriter.insertBlock! (wfCtx : WfIRContext OpInfo) (newBlock : BlockPtr)
    (insertionPoint : BlockInsertPoint)
    : WfIRContext OpInfo :=
  if newBlockIn : newBlock.InBounds wfCtx.raw then
    if insIn : insertionPoint.InBounds wfCtx.raw then
      if let some ctx := WfRewriter.insertBlock wfCtx newBlock insertionPoint then
        ctx
      else
        panic! "WfRewriter.insertBlock! failed: insertion point does not have a parent region"
    else
      panic! "WfRewriter.insertBlock! failed: insertion point is out of bounds"
  else
    panic! "WfRewriter.insertBlock! failed: new block is out of bounds"

/-- Replace the operand of an operation with a new value. -/
@[inline]
def WfRewriter.replaceOperand (wfCtx : WfIRContext OpInfo) (use : OpOperandPtr) (newValue : ValuePtr)
    (useIn : use.InBounds wfCtx.raw := by grind)
    (newIn : newValue.InBounds wfCtx.raw := by grind)
    : WfIRContext OpInfo :=
  ⟨Rewriter.replaceUse wfCtx use newValue useIn newIn (by grind),
    by grind [Rewriter.replaceUse_WellFormed]⟩

/-- Replace the operand of an operation with a new value, panicking if the operand use or the new
value is out of bounds. -/
def WfRewriter.replaceOperand! (wfCtx : WfIRContext OpInfo) (use : OpOperandPtr) (newValue : ValuePtr)
    : WfIRContext OpInfo :=
  if useIn : use.InBounds wfCtx.raw then
    if newIn : newValue.InBounds wfCtx.raw then
      WfRewriter.replaceOperand wfCtx use newValue useIn newIn
    else
      panic! "WfRewriter.replaceOperand! failed: new value is out of bounds"
  else
    panic! "WfRewriter.replaceOperand! failed: operand use is out of bounds"

/-- Set the type of a value. -/
@[inline]
def WfRewriter.setType (wfCtx : WfIRContext OpInfo) (value : ValuePtr) (newType : TypeAttr)
    (hvalue : value.InBounds wfCtx.raw := by grind) : WfIRContext OpInfo :=
  ⟨Rewriter.setType wfCtx.raw value newType hvalue,
    by grind [IRContext.wellFormed_rewriter_setType]⟩

/-- Set the type of a value, panicking if the value is out of bounds. -/
def WfRewriter.setType! (wfCtx : WfIRContext OpInfo) (value : ValuePtr) (newType : TypeAttr)
    : WfIRContext OpInfo :=
  if hvalue : value.InBounds wfCtx.raw then
    WfRewriter.setType wfCtx value newType hvalue
  else
    panic! "WfRewriter.setType! failed: value is out of bounds"

/-- Replace a value with another value. -/
def WfRewriter.replaceValue (ctx: WfIRContext OpInfo) (oldValue: ValuePtr) (newValue: ValuePtr)
    (neValues : oldValue ≠ newValue := by grind)
    (oldIn: oldValue.InBounds ctx.raw := by grind)
    (newIn: newValue.InBounds ctx.raw := by grind) : WfIRContext OpInfo := Id.run do
  match h : oldValue.getFirstUse ctx.raw with
  | none => return ctx
  | some firstUse =>
    let ctx := Rewriter.replaceUse ctx.raw firstUse newValue
    replaceValue ⟨ctx, by grind [Rewriter.replaceUse_WellFormed]⟩ oldValue newValue
  termination_by (ValuePtr.defUseArray oldValue ctx.raw ctx.wellFormed oldIn).size
  decreasing_by
    rename_i oldCtx
    rw [ValuePtr.defUseArray_Rewriter_replaceUse_oldValue] <;>
      grind [ValuePtr.defUseArray_contains_operand_use]

/-- Replace a value with another value, panicking if the two values are equal, or if either value
is out of bounds. -/
def WfRewriter.replaceValue! (wfCtx : WfIRContext OpInfo) (oldValue : ValuePtr) (newValue : ValuePtr)
    : WfIRContext OpInfo :=
  if neValues : oldValue ≠ newValue then
    if oldIn : oldValue.InBounds wfCtx.raw then
      if newIn : newValue.InBounds wfCtx.raw then
        WfRewriter.replaceValue wfCtx oldValue newValue neValues oldIn newIn
      else
        panic! "WfRewriter.replaceValue! failed: new value is out of bounds"
    else
      panic! "WfRewriter.replaceValue! failed: old value is out of bounds"
  else
    panic! "WfRewriter.replaceValue! failed: old and new values are equal"

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

/--
Replace all results of an operation with the results of another, erasing the replaced operation.
Panics if the two operations are equal, if the old operation has no parent or has regions, if
either operation is out of bounds, or if the operations have different numbers of results.
-/
def WfRewriter.replaceOp! (wfCtx : WfIRContext OpInfo) (oldOp newOp : OperationPtr)
    : WfIRContext OpInfo :=
  if opNe : oldOp ≠ newOp then
    if hpar : (oldOp.get! wfCtx.raw).parent.isSome = true then
      if noRegions : oldOp.getNumRegions! wfCtx.raw = 0 then
        if oldIn : oldOp.InBounds wfCtx.raw then
          if newIn : newOp.InBounds wfCtx.raw then
            if let some ctx := WfRewriter.replaceOp? wfCtx oldOp newOp opNe hpar noRegions oldIn newIn then
              ctx
            else
              panic! "WfRewriter.replaceOp! failed: operations have different numbers of results"
          else
            panic! "WfRewriter.replaceOp! failed: new operation is out of bounds"
        else
          panic! "WfRewriter.replaceOp! failed: old operation is out of bounds"
      else
        panic! "WfRewriter.replaceOp! failed: old operation has regions"
    else
      panic! "WfRewriter.replaceOp! failed: old operation does not have a parent"
  else
    panic! "WfRewriter.replaceOp! failed: old and new operations are equal"

/-- Create a new block and insert it at a given location. -/
@[inline]
def WfRewriter.createBlock (wfCtx : WfIRContext OpInfo)
    (argTypes : Array TypeAttr)
    (insertionPoint : Option BlockInsertPoint)
    (hip : insertionPoint.maybe BlockInsertPoint.InBounds wfCtx.raw)
    : Option (WfIRContext OpInfo × BlockPtr) := do
  rlet (ctx, blk) ← Rewriter.createBlock wfCtx argTypes insertionPoint (by grind) hip
  return (⟨ctx, by grind [Rewriter.createBlock_WellFormed]⟩, blk)

/-- Create a new block and insert it at a given location, panicking if the insertion point is out
of bounds or if the block could not be created. -/
def WfRewriter.createBlock! (wfCtx : WfIRContext OpInfo)
    (argTypes : Array TypeAttr)
    (insertionPoint : Option BlockInsertPoint)
    : WfIRContext OpInfo × BlockPtr :=
  match insertionPoint with
  | none =>
    if let some result := WfRewriter.createBlock wfCtx argTypes none (by grind) then
      result
    else
      panic! "WfRewriter.createBlock! failed: could not create block"
  | some ip =>
    if hip : ip.InBounds wfCtx.raw then
      if let some result := WfRewriter.createBlock wfCtx argTypes (some ip) (by grind) then
        result
      else
        panic! "WfRewriter.createBlock! failed: could not insert block at insertion point"
    else
      panic! "WfRewriter.createBlock! failed: insertion point is out of bounds"

/--
Set the block arguments of a block.
This replaces all existing block arguments with new ones of the given types, so the existing block
arguments must have no uses.
-/
@[inline]
def WfRewriter.setBlockArguments (wfCtx : WfIRContext OpInfo) (blockPtr : BlockPtr)
    (types : Array TypeAttr)
    (hblock : blockPtr.InBounds wfCtx.raw := by grind)
    (noUses : ∀ blockArg ∈ blockPtr.getArguments! wfCtx.raw, ¬ blockArg.hasUses! wfCtx.raw := by grind)
    : WfIRContext OpInfo :=
  ⟨Rewriter.setBlockArguments wfCtx blockPtr types hblock,
    by grind [IRContext.wellFormed_Rewriter_setBlockArguments]⟩

/--
Set the block arguments of a block, panicking if the block is out of bounds or if any existing
block argument has uses.
-/
def WfRewriter.setBlockArguments! (wfCtx : WfIRContext OpInfo) (blockPtr : BlockPtr)
    (types : Array TypeAttr)
    : WfIRContext OpInfo :=
  if hblock : blockPtr.InBounds wfCtx.raw then
    if noUses : ∀ blockArg ∈ blockPtr.getArguments! wfCtx.raw, ¬ blockArg.hasUses! wfCtx.raw then
      WfRewriter.setBlockArguments wfCtx blockPtr types hblock noUses
    else
      panic! "WfRewriter.setBlockArguments! failed: existing block arguments have uses"
  else
    panic! "WfRewriter.setBlockArguments! failed: block is out of bounds"

/-- Create a new region. -/
@[inline]
def WfRewriter.createRegion (wfCtx : WfIRContext OpInfo)
    : Option (WfIRContext OpInfo × RegionPtr) := do
  rlet (ctx, reg) ← Rewriter.createRegion wfCtx
  return (⟨ctx, by grind [IRContext.wellFormed_Rewriter_createRegion]⟩, reg)

/-- Create a new region, panicking if the region could not be created. -/
def WfRewriter.createRegion! (wfCtx : WfIRContext OpInfo)
    : WfIRContext OpInfo × RegionPtr :=
  if let some result := WfRewriter.createRegion wfCtx then
    result
  else
    panic! "WfRewriter.createRegion! failed: could not create region"

/-- Insert a region at the end of an operation's region list. -/
@[inline]
def WfRewriter.pushRegion (wfCtx : WfIRContext OpInfo) (op : OperationPtr) (region : RegionPtr)
    (hop : op.InBounds wfCtx.raw := by grind)
    (hregion : region.InBounds wfCtx.raw := by grind)
    (hRegionParent : (region.get! wfCtx.raw).parent = none := by grind)
    : WfIRContext OpInfo :=
  ⟨Rewriter.pushRegion wfCtx op region hop hregion hRegionParent,
    by grind [IRContext.wellFormed_Rewriter_pushRegion]⟩

/-- Insert a region at the end of an operation's region list, panicking if the operation or region
is out of bounds, or if the region already has a parent. -/
def WfRewriter.pushRegion! (wfCtx : WfIRContext OpInfo) (op : OperationPtr) (region : RegionPtr)
    : WfIRContext OpInfo :=
  if hop : op.InBounds wfCtx.raw then
    if hregion : region.InBounds wfCtx.raw then
      if hRegionParent : (region.get! wfCtx.raw).parent = none then
        WfRewriter.pushRegion wfCtx op region hop hregion hRegionParent
      else
        panic! "WfRewriter.pushRegion! failed: region already has a parent"
    else
      panic! "WfRewriter.pushRegion! failed: region is out of bounds"
  else
    panic! "WfRewriter.pushRegion! failed: operation is out of bounds"

/-- Insert a result at the end of an operation's result list. -/
@[inline]
def WfRewriter.pushResult (wfCtx : WfIRContext OpInfo) (op : OperationPtr) (type : TypeAttr)
    (hop : op.InBounds wfCtx.raw := by grind)
    : WfIRContext OpInfo :=
  ⟨Rewriter.pushResult wfCtx op type hop,
    by grind [IRContext.wellFormed_Rewriter_pushResult]⟩

/-- Insert a result at the end of an operation's result list, panicking if the operation is out of
bounds. -/
def WfRewriter.pushResult! (wfCtx : WfIRContext OpInfo) (op : OperationPtr) (type : TypeAttr)
    : WfIRContext OpInfo :=
  if hop : op.InBounds wfCtx.raw then
    WfRewriter.pushResult wfCtx op type hop
  else
    panic! "WfRewriter.pushResult! failed: operation is out of bounds"

/-- Insert an operand at the end of an operation's operand list. -/
@[inline]
def WfRewriter.pushOperand (wfCtx : WfIRContext OpInfo) (opPtr : OperationPtr) (valuePtr : ValuePtr)
    (opPtrInBounds : opPtr.InBounds wfCtx.raw := by grind)
    (valueInBounds : valuePtr.InBounds wfCtx.raw := by grind)
    : WfIRContext OpInfo :=
  ⟨Rewriter.pushOperand wfCtx opPtr valuePtr opPtrInBounds valueInBounds (by grind),
    by grind [Rewriter.pushOperand_WellFormed]⟩

/-- Insert an operand at the end of an operation's operand list, panicking if the operation or the
value is out of bounds. -/
def WfRewriter.pushOperand! (wfCtx : WfIRContext OpInfo) (opPtr : OperationPtr) (valuePtr : ValuePtr)
    : WfIRContext OpInfo :=
  if opPtrInBounds : opPtr.InBounds wfCtx.raw then
    if valueInBounds : valuePtr.InBounds wfCtx.raw then
      WfRewriter.pushOperand wfCtx opPtr valuePtr opPtrInBounds valueInBounds
    else
      panic! "WfRewriter.pushOperand! failed: value is out of bounds"
  else
    panic! "WfRewriter.pushOperand! failed: operation is out of bounds"

/-- Insert a block operand at the end of an operation's block operand list. -/
@[inline]
def WfRewriter.pushBlockOperand (wfCtx : WfIRContext OpInfo) (opPtr : OperationPtr) (blockPtr : BlockPtr)
    (opPtrInBounds : opPtr.InBounds wfCtx.raw := by grind)
    (blockInBounds : blockPtr.InBounds wfCtx.raw := by grind)
    : WfIRContext OpInfo :=
  ⟨Rewriter.pushBlockOperand wfCtx opPtr blockPtr opPtrInBounds blockInBounds (by grind),
    by grind [Rewriter.pushBlockOperand_WellFormed]⟩

/-- Insert a block operand at the end of an operation's block operand list, panicking if the
operation or the block is out of bounds. -/
def WfRewriter.pushBlockOperand! (wfCtx : WfIRContext OpInfo) (opPtr : OperationPtr) (blockPtr : BlockPtr)
    : WfIRContext OpInfo :=
  if opPtrInBounds : opPtr.InBounds wfCtx.raw then
    if blockInBounds : blockPtr.InBounds wfCtx.raw then
      WfRewriter.pushBlockOperand wfCtx opPtr blockPtr opPtrInBounds blockInBounds
    else
      panic! "WfRewriter.pushBlockOperand! failed: block is out of bounds"
  else
    panic! "WfRewriter.pushBlockOperand! failed: operation is out of bounds"

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
Create an operation and insert it at a given location, panicking if any operand, block operand,
or region is out of bounds, if the insertion point is out of bounds, or if the operation could
not be created.
-/
def WfRewriter.createOp! (wfCtx : WfIRContext OpInfo) (opType : OpInfo)
    (resultTypes : Array TypeAttr) (operands : Array ValuePtr) (blockOperands : Array BlockPtr)
    (regions : Array RegionPtr) (properties : HasOpInfo.propertiesOf opType)
    (insertionPoint : Option InsertPoint)
    : Option (WfIRContext OpInfo × OperationPtr) :=
  if hoper : ∀ oper, oper ∈ operands → oper.InBounds wfCtx.raw then
    if hblockOperands : ∀ oper, oper ∈ blockOperands → oper.InBounds wfCtx.raw then
      if hregions : ∀ reg, reg ∈ regions → reg.InBounds wfCtx.raw then
        match insertionPoint with
        | none =>
          WfRewriter.createOp wfCtx opType resultTypes operands blockOperands regions
            properties none hoper hblockOperands hregions
        | some ip =>
          if hins : ip.InBounds wfCtx.raw then
            if let some result := WfRewriter.createOp wfCtx opType resultTypes operands
                blockOperands regions properties (some ip) hoper hblockOperands hregions then
              result
            else
              panic! "WfRewriter.createOp! failed: could not insert operation at insertion point"
          else
            panic! "WfRewriter.createOp! failed: insertion point is out of bounds"
      else
        panic! "WfRewriter.createOp! failed: a region is out of bounds"
    else
      panic! "WfRewriter.createOp! failed: a block operand is out of bounds"
  else
    panic! "WfRewriter.createOp! failed: an operand is out of bounds"

/--
Create a new IR context with a single `builtin.module` operation at the top-level.
The operation contains a single region, which contains a single empty block.
-/
@[inline]
def WfIRContext.create (OpInfo : Type) [HasOpInfo OpInfo]
    : Option (WfIRContext OpInfo × OperationPtr) := do
  rlet (ctx, op) ← IRContext.create OpInfo
  return (⟨ctx, by grind [IRContext.wellFormed_IRContext_create]⟩, op)

/--
Create a new IR context with a single `builtin.module` operation at the top-level, panicking if
the context could not be created.
The operation contains a single region, which contains a single empty block.
-/
def WfIRContext.create! (OpInfo : Type) [HasOpInfo OpInfo]
    : WfIRContext OpInfo × OperationPtr :=
  if let some result := WfIRContext.create OpInfo then
    result
  else
    panic! "WfIRContext.create! failed: could not create IR context"

end Veir
