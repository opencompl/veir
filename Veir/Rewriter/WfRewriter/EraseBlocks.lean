module

public import Veir.Rewriter.EraseBlocks
public import Veir.Rewriter.WfRewriter.Basic

import Veir.Rewriter.WellFormed
import Veir.Rewriter.WellFormed.EraseBlocks

/-!
# Well-formed wrappers for block and region erasure

Each operation checks its preconditions and panics if they do not hold.
-/

public section
namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]

/--
Remove the operands and successors of an operation, panicking if the operation
is out of bounds.
-/
def WfRewriter.dropOperands! (wfCtx : WfIRContext OpInfo) (op : OperationPtr)
    : WfIRContext OpInfo :=
  if hOp : op.InBounds wfCtx.raw then
    ⟨Rewriter.dropOperands wfCtx op (by grind) hOp,
      by grind [Rewriter.dropOperands_WellFormed]⟩
  else
    panic! "WfRewriter.dropOperands! failed: operation is out of bounds"

/-- Detach all regions from an operation, panicking if the operation is out of bounds. -/
def WfRewriter.detachRegions! (wfCtx : WfIRContext OpInfo) (op : OperationPtr)
    : WfIRContext OpInfo :=
  if hOp : op.InBounds wfCtx.raw then
    ⟨Rewriter.detachRegions wfCtx op (by grind) hOp,
      by grind [Rewriter.detachRegions_WellFormed]⟩
  else
    panic! "WfRewriter.detachRegions! failed: operation is out of bounds"

/--
Unlink a block from its parent region, panicking if the block is out of bounds
or does not have a parent.
-/
def WfRewriter.detachBlock! (wfCtx : WfIRContext OpInfo) (block : BlockPtr)
    : WfIRContext OpInfo :=
  if hIn : block.InBounds wfCtx.raw then
    if hasParent : (block.getParent! wfCtx.raw).isSome then
      ⟨Rewriter.detachBlock wfCtx block (by grind) hIn (by grind),
        by grind [Rewriter.detachBlock_WellFormed]⟩
    else
      panic! "WfRewriter.detachBlock! failed: block does not have a parent"
  else
    panic! "WfRewriter.detachBlock! failed: block is out of bounds"

/--
Unlink a block from its parent region if it has one, panicking if the block is
out of bounds. If it has no parent, return the context unchanged.
-/
def WfRewriter.detachBlockIfAttached! (wfCtx : WfIRContext OpInfo) (block : BlockPtr)
    : WfIRContext OpInfo :=
  if hIn : block.InBounds wfCtx.raw then
    ⟨Rewriter.detachBlockIfAttached wfCtx block (by grind) hIn,
      by grind [Rewriter.detachBlockIfAttached_WellFormed]⟩
  else
    panic! "WfRewriter.detachBlockIfAttached! failed: block is out of bounds"

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
            ⟨block.dealloc wfCtx hIn,
              IRContext.wellFormed_BlockPtr_dealloc wfCtx.wellFormed
                noParent noOps noPreds noArgUses⟩
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

/--
Deallocate a region, panicking if the region is out of bounds, has a parent, or
contains blocks.
-/
def WfRewriter.deallocRegion! (wfCtx : WfIRContext OpInfo) (region : RegionPtr)
    : WfIRContext OpInfo :=
  if hIn : region.InBounds wfCtx.raw then
    if noParent : region.getParent! wfCtx.raw = none then
      if noBlocks : region.getFirstBlock! wfCtx.raw = none then
        ⟨region.dealloc wfCtx hIn,
          IRContext.wellFormed_RegionPtr_dealloc wfCtx.wellFormed noParent noBlocks⟩
      else
        panic! "WfRewriter.deallocRegion! failed: region contains blocks"
    else
      panic! "WfRewriter.deallocRegion! failed: region has a parent"
  else
    panic! "WfRewriter.deallocRegion! failed: region is out of bounds"

end Veir
