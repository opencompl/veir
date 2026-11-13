module

public import Veir.Rewriter.EraseBlocks

import all Veir.Rewriter.EraseBlocks
import Veir.Rewriter.WellFormed.Operation

/-!
# Well-formedness of the block and region erasure primitives

Each primitive in `Veir.Rewriter.EraseBlocks` preserves `IRContext.WellFormed`
with empty missing-use sets. The deallocation lemmas list exactly the conditions
under which nothing in the context still points to the deallocated block or
region.
-/

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : IRContext OpInfo}

/--
After `dropOperands`, the context is well formed with no missing uses: the
operands of `op` have been removed from their use chains and from `op` itself.
-/
axiom Rewriter.dropOperands_WellFormed (ctx : IRContext OpInfo) (wf : ctx.WellFormed)
    (hctx : ctx.FieldsInBounds) (op : OperationPtr) (hOp : op.InBounds ctx) :
    (Rewriter.dropOperands ctx op hctx hOp).WellFormed

axiom Rewriter.detachRegions_WellFormed (ctx : IRContext OpInfo) (wf : ctx.WellFormed)
    (hctx : ctx.FieldsInBounds) (op : OperationPtr) (hOp : op.InBounds ctx) :
    (Rewriter.detachRegions ctx op hctx hOp).WellFormed

axiom Rewriter.detachBlock_WellFormed (ctx : IRContext OpInfo) (wf : ctx.WellFormed)
    (hctx : ctx.FieldsInBounds) (block : BlockPtr) (hIn : block.InBounds ctx)
    (hasParent : (block.getParent ctx hIn).isSome) :
    (Rewriter.detachBlock ctx block hctx hIn hasParent).WellFormed

/--
A block can be deallocated when it is detached from its region, contains no
operations, is not the successor of any operation, and its arguments are unused.
-/
axiom IRContext.wellFormed_BlockPtr_dealloc {block : BlockPtr} {inBounds : block.InBounds ctx}
    (wf : ctx.WellFormed)
    (hparent : block.getParent! ctx = none)
    (hops : block.getFirstOp! ctx = none)
    (hpreds : block.hasPredecessor! ctx = false)
    (hargs : block.hasArgumentUses! ctx = false) :
    (block.dealloc ctx inBounds).WellFormed

/-- A region can be deallocated when it is detached from its operation and has no blocks. -/
axiom IRContext.wellFormed_RegionPtr_dealloc {region : RegionPtr}
    {inBounds : region.InBounds ctx}
    (wf : ctx.WellFormed)
    (hparent : region.getParent! ctx = none)
    (hblocks : region.getFirstBlock! ctx = none) :
    (region.dealloc ctx inBounds).WellFormed

end Veir
