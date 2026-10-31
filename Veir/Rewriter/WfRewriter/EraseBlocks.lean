module

public import Veir.Rewriter.EraseBlocks
public import Veir.Rewriter.WfRewriter.Basic

import Veir.Rewriter.WellFormed
import Veir.Rewriter.WellFormed.EraseBlocks

/-!
# Well-formed wrappers for block and region erasure

Each operation comes in two variants: one taking its preconditions as
hypotheses, and a `!` variant that checks them and panics if they do not hold.
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
Remove the operands and successors of an operation, panicking if the operation
is out of bounds.
-/
def WfRewriter.dropOperands! (wfCtx : WfIRContext OpInfo) (op : OperationPtr)
    : WfIRContext OpInfo :=
  if hOp : op.InBounds wfCtx.raw then
    WfRewriter.dropOperands wfCtx op hOp
  else
    panic! "WfRewriter.dropOperands! failed: operation is out of bounds"

/-- Detach all regions from an operation. -/
@[inline]
def WfRewriter.detachRegions (wfCtx : WfIRContext OpInfo) (op : OperationPtr)
    (hOp : op.InBounds wfCtx.raw := by grind)
    : WfIRContext OpInfo :=
  ⟨Rewriter.detachRegions wfCtx op (by grind) hOp,
    by grind [Rewriter.detachRegions_WellFormed]⟩

/-- Detach all regions from an operation, panicking if the operation is out of bounds. -/
def WfRewriter.detachRegions! (wfCtx : WfIRContext OpInfo) (op : OperationPtr)
    : WfIRContext OpInfo :=
  if hOp : op.InBounds wfCtx.raw then
    WfRewriter.detachRegions wfCtx op hOp
  else
    panic! "WfRewriter.detachRegions! failed: operation is out of bounds"

/-- Unlink a block from its parent region. -/
@[inline]
def WfRewriter.detachBlock (wfCtx : WfIRContext OpInfo) (block : BlockPtr)
    (hIn : block.InBounds wfCtx.raw)
    (hasParent : (block.getParent! wfCtx.raw).isSome)
    : WfIRContext OpInfo :=
  ⟨Rewriter.detachBlock wfCtx block (by grind) hIn (by grind),
    by grind [Rewriter.detachBlock_WellFormed]⟩

/--
Unlink a block from its parent region, panicking if the block is out of bounds
or does not have a parent.
-/
def WfRewriter.detachBlock! (wfCtx : WfIRContext OpInfo) (block : BlockPtr)
    : WfIRContext OpInfo :=
  if hIn : block.InBounds wfCtx.raw then
    if hasParent : (block.getParent! wfCtx.raw).isSome then
      WfRewriter.detachBlock wfCtx block hIn hasParent
    else
      panic! "WfRewriter.detachBlock! failed: block does not have a parent"
  else
    panic! "WfRewriter.detachBlock! failed: block is out of bounds"

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
Unlink a block from its parent region if it has one, panicking if the block is
out of bounds.
-/
def WfRewriter.detachBlockIfAttached! (wfCtx : WfIRContext OpInfo) (block : BlockPtr)
    : WfIRContext OpInfo :=
  if hIn : block.InBounds wfCtx.raw then
    WfRewriter.detachBlockIfAttached wfCtx block hIn
  else
    panic! "WfRewriter.detachBlockIfAttached! failed: block is out of bounds"

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
Deallocate a block, panicking if the block is out of bounds, has a parent,
contains operations, has predecessors, or has arguments with uses.
-/
def WfRewriter.deallocBlock! (wfCtx : WfIRContext OpInfo) (block : BlockPtr)
    : WfIRContext OpInfo :=
  if hIn : block.InBounds wfCtx.raw then
    if noParent : block.getParent! wfCtx.raw = none then
      if noOps : block.getFirstOp! wfCtx.raw = none then
        if noPreds : block.hasPredecessor! wfCtx.raw = false then
          if noArgUses : block.hasArgumentUses! wfCtx.raw = false then
            WfRewriter.deallocBlock wfCtx block hIn noParent noOps noPreds noArgUses
          else
            panic! "WfRewriter.deallocBlock! failed: block arguments have uses"
        else
          panic! "WfRewriter.deallocBlock! failed: block has predecessors"
      else
        panic! "WfRewriter.deallocBlock! failed: block contains operations"
    else
      panic! "WfRewriter.deallocBlock! failed: block has a parent"
  else
    panic! "WfRewriter.deallocBlock! failed: block is out of bounds"

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
Deallocate a region, panicking if the region is out of bounds, has a parent, or
contains blocks.
-/
def WfRewriter.deallocRegion! (wfCtx : WfIRContext OpInfo) (region : RegionPtr)
    : WfIRContext OpInfo :=
  if hIn : region.InBounds wfCtx.raw then
    if noParent : region.getParent! wfCtx.raw = none then
      if noBlocks : region.getFirstBlock! wfCtx.raw = none then
        WfRewriter.deallocRegion wfCtx region hIn noParent noBlocks
      else
        panic! "WfRewriter.deallocRegion! failed: region contains blocks"
    else
      panic! "WfRewriter.deallocRegion! failed: region has a parent"
  else
    panic! "WfRewriter.deallocRegion! failed: region is out of bounds"

end Veir
