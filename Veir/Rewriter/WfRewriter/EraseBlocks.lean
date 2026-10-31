module

public import Veir.Rewriter.EraseBlocks
public import Veir.Rewriter.WfRewriter.Basic

import Veir.Rewriter.WellFormed
import Veir.Rewriter.WellFormed.EraseBlocks

/-!
# Well-formed wrappers for block and region erasure

Each operation comes in two variants: one taking its preconditions as
hypotheses, and a `?` variant that checks them and returns `none` if they do
not hold.
-/

public section
namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]

/-- Remove the operands and successors of an operation. -/
@[inline]
def WfRewriter.dropOperands (wfCtx : WfIRContext OpInfo) (op : OperationPtr)
    (hOp : op.InBounds wfCtx.raw := by grind)
    : WfIRContext OpInfo :=
  ⟨Rewriter.dropOperands wfCtx op (by grind) hOp,
    by grind [Rewriter.dropOperands_WellFormed]⟩

/--
Remove the operands and successors of an operation, returning `none` if the
operation is out of bounds.
-/
def WfRewriter.dropOperands? (wfCtx : WfIRContext OpInfo) (op : OperationPtr)
    : Option (WfIRContext OpInfo) :=
  if hOp : op.InBounds wfCtx.raw then
    some (WfRewriter.dropOperands wfCtx op hOp)
  else
    none

/-- Detach all regions from an operation. -/
@[inline]
def WfRewriter.detachRegions (wfCtx : WfIRContext OpInfo) (op : OperationPtr)
    (hOp : op.InBounds wfCtx.raw := by grind)
    : WfIRContext OpInfo :=
  ⟨Rewriter.detachRegions wfCtx op (by grind) hOp,
    by grind [Rewriter.detachRegions_WellFormed]⟩

/-- Detach all regions from an operation, returning `none` if the operation is out of bounds. -/
def WfRewriter.detachRegions? (wfCtx : WfIRContext OpInfo) (op : OperationPtr)
    : Option (WfIRContext OpInfo) :=
  if hOp : op.InBounds wfCtx.raw then
    some (WfRewriter.detachRegions wfCtx op hOp)
  else
    none

/--
Erase an operation, returning `none` if the operation is out of bounds, has
regions, or has uses.
-/
def WfRewriter.eraseOp? (wfCtx : WfIRContext OpInfo) (op : OperationPtr)
    : Option (WfIRContext OpInfo) :=
  if hOp : op.InBounds wfCtx.raw then
    if opRegions : op.getNumRegions! wfCtx.raw = 0 then
      if opUses : !op.hasUses! wfCtx.raw then
        some (WfRewriter.eraseOp wfCtx op opRegions opUses hOp)
      else
        none
    else
      none
  else
    none

/-- Unlink a block from its parent region. -/
@[inline]
def WfRewriter.detachBlock (wfCtx : WfIRContext OpInfo) (block : BlockPtr)
    (hIn : block.InBounds wfCtx.raw)
    (hasParent : (block.getParent! wfCtx.raw).isSome)
    : WfIRContext OpInfo :=
  ⟨Rewriter.detachBlock wfCtx block (by grind) hIn (by grind),
    by grind [Rewriter.detachBlock_WellFormed]⟩

/--
Unlink a block from its parent region, returning `none` if the block is out of
bounds or does not have a parent.
-/
def WfRewriter.detachBlock? (wfCtx : WfIRContext OpInfo) (block : BlockPtr)
    : Option (WfIRContext OpInfo) :=
  if hIn : block.InBounds wfCtx.raw then
    if hasParent : (block.getParent! wfCtx.raw).isSome then
      some (WfRewriter.detachBlock wfCtx block hIn hasParent)
    else
      none
  else
    none

/--
Unlink a block from its parent region if it has one.
If it has no parent, return the context unchanged.
-/
@[inline]
def WfRewriter.detachBlockIfAttached (wfCtx : WfIRContext OpInfo) (block : BlockPtr)
    (hIn : block.InBounds wfCtx.raw := by grind)
    : WfIRContext OpInfo :=
  ⟨Rewriter.detachBlockIfAttached wfCtx block (by grind) hIn,
    by grind [Rewriter.detachBlockIfAttached_WellFormed]⟩

/--
Unlink a block from its parent region if it has one, returning `none` if the
block is out of bounds.
-/
def WfRewriter.detachBlockIfAttached? (wfCtx : WfIRContext OpInfo) (block : BlockPtr)
    : Option (WfIRContext OpInfo) :=
  if hIn : block.InBounds wfCtx.raw then
    some (WfRewriter.detachBlockIfAttached wfCtx block hIn)
  else
    none

/-- Deallocate a detached, empty, and unused block. -/
@[inline]
def WfRewriter.deallocBlock (wfCtx : WfIRContext OpInfo) (block : BlockPtr)
    (hIn : block.InBounds wfCtx.raw)
    (noParent : block.getParent! wfCtx.raw = none)
    (noOps : block.getFirstOp! wfCtx.raw = none)
    (noPreds : block.hasPredecessor! wfCtx.raw = false)
    (noArgUses : block.hasArgumentUses! wfCtx.raw = false)
    : WfIRContext OpInfo :=
  ⟨block.dealloc wfCtx hIn,
    IRContext.wellFormed_BlockPtr_dealloc wfCtx.wellFormed noParent noOps noPreds noArgUses⟩

/--
Deallocate a block, returning `none` if the block is out of bounds, has a parent,
contains operations, has predecessors, or has arguments with uses.
-/
def WfRewriter.deallocBlock? (wfCtx : WfIRContext OpInfo) (block : BlockPtr)
    : Option (WfIRContext OpInfo) :=
  if hIn : block.InBounds wfCtx.raw then
    if noParent : block.getParent! wfCtx.raw = none then
      if noOps : block.getFirstOp! wfCtx.raw = none then
        if noPreds : block.hasPredecessor! wfCtx.raw = false then
          if noArgUses : block.hasArgumentUses! wfCtx.raw = false then
            some (WfRewriter.deallocBlock wfCtx block hIn noParent noOps noPreds noArgUses)
          else
            none
        else
          none
      else
        none
    else
      none
  else
    none

/-- Deallocate a detached and empty region. -/
@[inline]
def WfRewriter.deallocRegion (wfCtx : WfIRContext OpInfo) (region : RegionPtr)
    (hIn : region.InBounds wfCtx.raw)
    (noParent : region.getParent! wfCtx.raw = none)
    (noBlocks : region.getFirstBlock! wfCtx.raw = none)
    : WfIRContext OpInfo :=
  ⟨region.dealloc wfCtx hIn,
    IRContext.wellFormed_RegionPtr_dealloc wfCtx.wellFormed noParent noBlocks⟩

/--
Deallocate a region, returning `none` if the region is out of bounds, has a
parent, or contains blocks.
-/
def WfRewriter.deallocRegion? (wfCtx : WfIRContext OpInfo) (region : RegionPtr)
    : Option (WfIRContext OpInfo) :=
  if hIn : region.InBounds wfCtx.raw then
    if noParent : region.getParent! wfCtx.raw = none then
      if noBlocks : region.getFirstBlock! wfCtx.raw = none then
        some (WfRewriter.deallocRegion wfCtx region hIn noParent noBlocks)
      else
        none
    else
      none
  else
    none

end Veir
