module

public import Veir.Rewriter.Basic

/-!
# Primitives for erasing blocks and regions

These are the raw building blocks used to erase a set of blocks, together with
every operation, block, and region nested in them:

* `Rewriter.dropOperands` removes an operation's operands and successors from
  their use chains, and then empties its operand and successor arrays, so that
  no stale pointers remain in the operation.
* `Rewriter.detachRegions` detaches all regions from an operation.
* `Rewriter.detachBlock` unlinks a block from its parent region.

Deallocation itself is done with `OperationPtr.dealloc` (through
`Rewriter.eraseOp`), `BlockPtr.dealloc`, and `RegionPtr.dealloc`.
-/

public section
namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : IRContext OpInfo}

/-- Returns true if any argument of the block has a use. -/
def BlockPtr.hasArgumentUses! (block : BlockPtr) (ctx : IRContext OpInfo) : Bool :=
  (block.getNumArguments! ctx).any fun index _ =>
    (ValuePtr.blockArgument (block.getArgument index)).hasUses! ctx

/--
  Remove the operands and successors of an operation from their use chains,
  and empty the operand and successor arrays of the operation.

  Unlike `detachOperands`, this does not leave operands with stale `value`,
  `back`, and `nextUse` pointers in the operation, so other operations can be
  deallocated afterwards in any order.
-/
@[irreducible]
def Rewriter.dropOperands (ctx : IRContext OpInfo) (op : OperationPtr)
    (hCtx : ctx.FieldsInBounds := by grind)
    (hOp : op.InBounds ctx := by grind) : IRContext OpInfo :=
  let ctx := Rewriter.detachOperands ctx op
  let ctx := Rewriter.detachBlockOperands ctx op (by grind) (by grind)
  let ctx := op.setOperands! ctx #[]
  op.setBlockOperands! ctx #[]

@[irreducible, inline]
def Rewriter.detachRegions.loop (ctx : IRContext OpInfo) (op : OperationPtr) (index : Nat)
    (hCtx : ctx.FieldsInBounds := by grind)
    (hOp : op.InBounds ctx := by grind)
    (hIndex : index < op.getNumRegions! ctx := by grind) : IRContext OpInfo :=
  let ctx' := (op.getRegion! ctx index).setParent ctx none (by grind)
  match index with
  | .succ index => Rewriter.detachRegions.loop ctx' op index (by grind) (by grind) (by grind)
  | 0 => ctx'

@[grind .]
theorem Rewriter.detachRegions.loop_inBounds (ptr : GenericPtr) :
    ptr.InBounds (detachRegions.loop ctx op index hCtx hOp hIndex) ↔ ptr.InBounds ctx := by
  induction index generalizing ctx <;> simp only [detachRegions.loop] <;> grind

@[grind .]
theorem Rewriter.detachRegions.loop_fieldsInBounds :
    ctx.FieldsInBounds → (detachRegions.loop ctx op index hCtx hOp hIndex).FieldsInBounds := by
  induction index generalizing ctx <;> simp only [detachRegions.loop] <;> grind

/--
  Detach all regions from an operation: the parent of each region is set to
  `none`, and the operation is left without regions.
-/
@[irreducible, inline]
def Rewriter.detachRegions (ctx : IRContext OpInfo) (op : OperationPtr)
    (hCtx : ctx.FieldsInBounds := by grind)
    (hOp : op.InBounds ctx := by grind) : IRContext OpInfo :=
  let numRegions := op.getNumRegions ctx (by grind)
  let ctx' :=
    if h : numRegions = 0 then
      ctx
    else
      Rewriter.detachRegions.loop ctx op (numRegions - 1) (by grind) (by grind) (by grind)
  op.setRegions ctx' #[] (by grind)

@[grind .]
theorem Rewriter.detachRegions_inBounds (ptr : GenericPtr) :
    ptr.InBounds (detachRegions ctx op hCtx hOp) ↔ ptr.InBounds ctx := by
  grind [detachRegions]

@[grind .]
theorem Rewriter.detachRegions_fieldsInBounds :
    ctx.FieldsInBounds → (detachRegions ctx op hCtx hOp).FieldsInBounds := by
  intro h
  simp only [detachRegions]
  apply OperationPtr.setRegions_fieldsInBounds <;> grind

/--
  Set the parent, previous, and next block pointers of a block to `none`.
  This method should not be used from outside the rewriter, and is only used to
  make proofs easier for grind.
-/
@[irreducible]
def Rewriter.unsetBlockParentAndNeighbors (ctx : IRContext OpInfo) (block : BlockPtr)
    (hIn : block.InBounds ctx) :=
  let ctx := block.setParent ctx none
  let ctx := block.setPrevBlock ctx none
  block.setNextBlock ctx none

@[grind =]
theorem Rewriter.unsetBlockParentAndNeighbors_inBounds (ptr : GenericPtr) :
    ptr.InBounds (unsetBlockParentAndNeighbors ctx block hIn) ↔ ptr.InBounds ctx := by
  simp only [unsetBlockParentAndNeighbors]
  grind

@[grind .]
theorem Rewriter.unsetBlockParentAndNeighbors_fieldsInBounds (hctx : ctx.FieldsInBounds) :
    (unsetBlockParentAndNeighbors ctx block hIn).FieldsInBounds := by
  simp only [unsetBlockParentAndNeighbors]
  grind

/-- Unlink a block from its parent region. -/
@[irreducible]
def Rewriter.detachBlock (ctx : IRContext OpInfo) (block : BlockPtr)
    (hctx : ctx.FieldsInBounds) (hIn : block.InBounds ctx)
    (hasParent : (block.getParent ctx hIn).isSome) : IRContext OpInfo :=
  let parent := (block.getParent ctx hIn).get hasParent
  let prevBlock := block.getPrevBlock ctx hIn
  let nextBlock := block.getNextBlock ctx hIn
  let ctx := unsetBlockParentAndNeighbors ctx block hIn
  match _ : prevBlock with
    | some prevBlock =>
      let ctx := prevBlock.setNextBlock ctx nextBlock (by grind (ematch := 10))
      match _ : nextBlock with
      | some nextBlock => nextBlock.setPrevBlock ctx prevBlock (by grind (ematch := 10))
      | none => parent.setLastBlock ctx prevBlock (by grind (ematch := 10))
    | none =>
      let ctx := parent.setFirstBlock ctx nextBlock (by grind (ematch := 10))
      match _ : nextBlock with
      | some nextBlock => nextBlock.setPrevBlock ctx prevBlock (by grind (ematch := 10))
      | none => parent.setLastBlock ctx prevBlock (by grind (ematch := 10))

@[grind .]
theorem Rewriter.detachBlock_inBounds (ptr : GenericPtr) :
    ptr.InBounds (detachBlock ctx block hctx hIn hasParent) ↔ ptr.InBounds ctx := by
  grind [detachBlock]

@[grind .]
theorem Rewriter.detachBlock_fieldsInBounds (hctx : ctx.FieldsInBounds) :
    (detachBlock ctx block hctx hIn hasParent).FieldsInBounds := by
  simp only [detachBlock]
  grind

end Veir
