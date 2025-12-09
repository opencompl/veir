import Mlir.Core.Basic
import Mlir.WellFormedness.WellFormed
import Mlir.Rewriter
import Mlir.Lemmas.Rewriter

namespace Mlir

@[grind =]
theorem OperationPtr.get!_linkBetween (op : OperationPtr)
    (hneq : (nextOp = none ∧ prevOp = none) ∨ nextOp ≠ prevOp) (hnew : nextOp ≠ some self ∧ prevOp ≠ some self) (h₁ h₂ h₃) :
    op.get! (linkBetween self ctx prevOp nextOp h₁ h₂ h₃) =
    if op = self then
      { op.get! ctx with prev := prevOp, next := nextOp }
    else if prevOp = some op then
      { op.get! ctx with next := self }
    else if nextOp = some op then
      { op.get! ctx with prev := self }
    else
      op.get! ctx := by
  unfold linkBetween
  split
  · grind
  · split <;> grind

theorem OperationPtr.get!_linkBetweenWithParent (op : OperationPtr)
    (hneq : (nextOp = none ∧ prevOp = none) ∨ nextOp ≠ prevOp) (hnew : nextOp ≠ some self ∧ prevOp ≠ some self) (h₁ h₂ h₃)
    (heq : linkBetweenWithParent self ctx prevOp nextOp parent h₁ h₂ h₃ h₄ = some newCtx) :
    op.get! newCtx =
    if op = self then
      { op.get! ctx with prev := prevOp, next := nextOp, parent := parent }
    else if prevOp = some op then
      { op.get! ctx with next := self }
    else if nextOp = some op then
      { op.get! ctx with prev := self }
    else
      op.get! ctx := by
  unfold linkBetweenWithParent at heq
  grind (splits := 20)

@[simp, grind →]
theorem OperationPtr.get!_linkBetweenWithParent_same
    (hneq : (nextOp = none ∧ prevOp = none) ∨ nextOp ≠ prevOp) (hnew : nextOp ≠ some self ∧ prevOp ≠ some self) (h₁ h₂ h₃)
    (heq : linkBetweenWithParent self ctx prevOp nextOp parent h₁ h₂ h₃ h₄ = some newCtx) :
    self.get! newCtx = { self.get! ctx with prev := prevOp, next := nextOp, parent := parent } := by
  simp [OperationPtr.get!_linkBetweenWithParent (hneq := hneq) (hnew := hnew) (heq := heq)]

@[grind =>]
theorem OperationPtr.get!_linkBetweenWithParent_parent (op : OperationPtr)
  (hneq : (nextOp = none ∧ prevOp = none) ∨ nextOp ≠ prevOp) (hnew : nextOp ≠ some self ∧ prevOp ≠ some self)
  (heq : linkBetweenWithParent self ctx prevOp nextOp parent h₁ h₂ h₃ h₄ = some newCtx) :
  (op.get! newCtx).parent =
  if op = self then
    some parent
  else
    (op.get! ctx).parent := by
  rw [get!_linkBetweenWithParent _ hneq hnew (heq := heq)]
  grind

@[grind =>]
theorem OperationPtr.get!_linkBetweenWithParent_prev (op : OperationPtr)
  (hneq : (nextOp = none ∧ prevOp = none) ∨ nextOp ≠ prevOp) (hnew : nextOp ≠ some self ∧ prevOp ≠ some self)
  (heq : linkBetweenWithParent self ctx prevOp nextOp parent h₁ h₂ h₃ h₄ = some newCtx) :
  (op.get! newCtx).prev =
  if op = self then
    prevOp
  else if nextOp = some op then
    some self
  else
    (op.get! ctx).prev := by
  rw [get!_linkBetweenWithParent _ hneq hnew (heq := heq)]
  grind

@[grind =>]
theorem OperationPtr.get!_linkBetweenWithParent_next (op : OperationPtr)
  (hneq : (nextOp = none ∧ prevOp = none) ∨ nextOp ≠ prevOp) (hnew : nextOp ≠ some self ∧ prevOp ≠ some self)
  (heq : linkBetweenWithParent self ctx prevOp nextOp parent h₁ h₂ h₃ h₄ = some newCtx) :
  (op.get! newCtx).next =
  if op = self then
    nextOp
  else if prevOp = some op then
    some self
  else
    (op.get! ctx).next := by
  rw [get!_linkBetweenWithParent _ hneq hnew (heq := heq)]
  grind

@[simp, grind →]
theorem OperationPtr.get!_linkBetweenWithParent_parent_same
  (hneq : (nextOp = none ∧ prevOp = none) ∨ nextOp ≠ prevOp) (hnew : nextOp ≠ some self ∧ prevOp ≠ some self)
  (heq : linkBetweenWithParent self ctx prevOp nextOp parent h₁ h₂ h₃ h₄ = some newCtx) :
  (self.get! newCtx).parent = parent := by
  grind

@[simp, grind →]
theorem OperationPtr.get_linkBetweenWithParent_parent_same
  (hneq : (nextOp = none ∧ prevOp = none) ∨ nextOp ≠ prevOp) (hnew : nextOp ≠ some self ∧ prevOp ≠ some self)
  (heq : linkBetweenWithParent self ctx prevOp nextOp parent h₁ h₂ h₃ h₄ = some newCtx) :
  (self.get newCtx).parent = parent := by
  grind

@[simp]
theorem OperationPtr.get!_linkBetweenWithParent_parent_other
  (hneq : (nextOp = none ∧ prevOp = none) ∨ nextOp ≠ prevOp) (hnew : nextOp ≠ some self ∧ prevOp ≠ some self)
  (heq : linkBetweenWithParent self ctx prevOp nextOp parent h₁ h₂ h₃ h₄ = some newCtx) (hnn : op ≠ self) :
  (op.get! newCtx).parent = (op.get! ctx).parent := by
  grind

@[simp]
theorem OperationPtr.get_linkBetweenWithParent_parent_other
  (hneq : (nextOp = none ∧ prevOp = none) ∨ nextOp ≠ prevOp) (hnew : nextOp ≠ some self ∧ prevOp ≠ some self)
  (heq : linkBetweenWithParent self ctx prevOp nextOp parent h₁ h₂ h₃ h₄ = some newCtx) (hnn : op ≠ self) :
  (op.get newCtx).parent = (op.get ctx hop).parent := by
  have := @OperationPtr.get!_linkBetweenWithParent_parent_other (heq := heq) (hneq := hneq) (hnew := hnew) (hnn := hnn)
  grind

@[grind]
def InsertPoint.Wf (insertionPoint : InsertPoint) (ctx : IRContext) (newOp : OperationPtr) :=
  match insertionPoint with
  | Before op => newOp ≠ op ∧ newOp ≠ (op.get! ctx).prev ∧ op ≠ (op.get! ctx).prev
  | AtEnd bl => newOp ≠ (bl.get! ctx).lastOp

theorem OperationPtr.get!_insertOp? {op : OperationPtr}
    (hipWf : ip.Wf ctx newOp) (heq : Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx) :
    op.get! newCtx =
    match ip with
    | .AtEnd bl =>
      if op = newOp then
        { op.get! ctx with prev := (bl.get! ctx).lastOp, next := none, parent := some bl }
      else if (bl.get! ctx).lastOp = some op then
        { op.get! ctx with next := newOp }
      else
        op.get! ctx
    | .Before op' =>
      if op = newOp then
        { op.get! ctx with prev := (op'.get! ctx).prev, next := op', parent := (op'.get! ctx).parent }
      else if op = op' then
        { op.get! ctx with prev := .some newOp }
      else if op = (op'.get! ctx).prev then
        { op.get! ctx with next := .some newOp }
      else
        op.get! ctx := by
  simp only [Rewriter.insertOp?] at heq
  grind (splits := 25) [=> OperationPtr.get!_linkBetweenWithParent]

theorem OperationPtr.get!_insertOp?_other (op : OperationPtr)
    (hipWf : ip.Wf ctx newOp) (hother : ip.block! ctx ≠ (op.get! ctx).parent) (hnn : newOp ≠ op)
    (heq : Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx) :
    op.get! newCtx = op.get! ctx := by
  rw [get!_insertOp? hipWf heq]
  split
  · simp
    split
    · simp_all
    · split
      · sorry -- need WF
      · grind
  · split
    · simp_all
    · split
      · grind
      · split
        · simp_all [InsertPoint.block!]
          sorry -- need WF
        · grind

@[grind =>]
theorem OperationPtr.get!_insertOp?_parent (op : OperationPtr)
    (hipWf : ip.Wf ctx newOp) (heq : Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx) :
    (op.get! newCtx).parent =
    if op = newOp then
      ip.block! ctx
    else
      (op.get! ctx).parent := by
  simp only [Rewriter.insertOp?] at heq
  rw [get!_insertOp? hipWf heq] <;> grind

@[simp, grind →]
theorem OperationPtr.get!_insertOp?_parent_same
    (hipWf : ip.Wf ctx newOp) (heq : Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx) :
    (newOp.get! newCtx).parent = ip.block! ctx := by
  grind

@[simp, grind →]
theorem OperationPtr.get_insertOp?_parent_same
  (hipWf : ip.Wf ctx newOp) (heq : Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx) :
  (newOp.get newCtx).parent = ip.block! ctx := by
  grind

@[simp]
theorem OperationPtr.get!_insertOp?_parent_other
    (hipWf : ip.Wf ctx newOp) (heq : Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx) (hnn : op ≠ newOp) :
    (op.get! newCtx).parent = (op.get! ctx).parent := by
  grind

@[simp, grind =>]
theorem OperationPtr.get!_insertOp?_operands {op : OperationPtr}
    (hipWf : ip.Wf ctx newOp) (heq : Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx) :
    (op.get! newCtx).operands = (op.get! ctx).operands := by
  grind [OperationPtr.get!_insertOp? hipWf heq]

@[simp, grind =>]
theorem OperationPtr.get!_insertOp?_results {op : OperationPtr}
    (hipWf : ip.Wf ctx newOp) (heq : Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx) :
    (op.get! newCtx).results = (op.get! ctx).results := by
  grind [OperationPtr.get!_insertOp? hipWf heq]

@[simp, grind =>]
theorem OperationPtr.get!_insertOp?_blockOperands {op : OperationPtr}
    (hipWf : ip.Wf ctx newOp) (heq : Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx) :
    (op.get! newCtx).blockOperands = (op.get! ctx).blockOperands := by
  grind [OperationPtr.get!_insertOp? hipWf heq]

@[simp, grind =>]
theorem OperationPtr.get!_insertOp?_regions {op : OperationPtr}
    (hipWf : ip.Wf ctx newOp) (heq : Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx) :
    (op.get! newCtx).regions = (op.get! ctx).regions := by
  grind [OperationPtr.get!_insertOp? hipWf heq]

@[simp, grind =>]
theorem OperationPtr.get_insertOp?_other (op : OperationPtr) (hop : op.InBounds ctx)
    (hipWf : ip.Wf ctx newOp) (hother : ip.block! ctx ≠ (op.get! ctx).parent) (hnn : newOp ≠ op)
    (heq : Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx) :
    op.get newCtx = op.get ctx hop := by
  have := @get!_insertOp?_other
  grind

@[simp, grind =]
theorem BlockPtr.get!_linkBetween (block : BlockPtr) h₁ h₂ h₃ :
    block.get! (OperationPtr.linkBetween self ctx prevOp nextOp h₁ h₂ h₃) = block.get! ctx := by
  unfold OperationPtr.linkBetween
  grind

@[simp, grind =]
theorem RegionPtr.get!_linkBetween (region : RegionPtr) h₁ h₂ h₃ :
    region.get! (OperationPtr.linkBetween self ctx prevOp nextOp h₁ h₂ h₃) = region.get! ctx := by
  unfold OperationPtr.linkBetween
  grind

@[simp, grind .]
theorem BlockOperandPtr.get!_insertOp? {blockOp : BlockOperandPtr}
    (hipWf : ip.Wf ctx newOp) (heq : Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx) :
    blockOp.get! newCtx = blockOp.get! ctx := by
  simp [get!, OperationPtr.get!_insertOp?_blockOperands hipWf heq]

@[grind =>]
theorem BlockPtr.get!_linkBetweenWithParent (block : BlockPtr) h₁ h₂ h₃ h₄
    (heq : OperationPtr.linkBetweenWithParent self ctx prevOp nextOp parent h₁ h₂ h₃ h₄ = some newCtx) :
    block.get! newCtx =
    if parent = some block then
      { block.get! ctx with firstOp := if prevOp.isSome then (block.get! ctx).firstOp else self,
                            lastOp := if nextOp.isSome then (block.get! ctx).lastOp else self }
    else
      block.get! ctx := by
  sorry -- TODO
  -- simp only [OperationPtr.linkBetweenWithParent] at heq
  -- split at heq
  -- · grind
  -- · split at heq
  --   · split at heq
  --     · grind
  --     · grind
  --   · split
  --     · simp
  --       split at heq
  --       · grind
  --       · simp_all
  --         simp [BlockPtr.get!_OperationPtr_setParentWithCheck (by assumption)]
  --     · grind

@[grind =>]
theorem BlockPtr.get_linkBetweenWithParent (block : BlockPtr) (hbl : block.InBounds ctx) h₁ h₂ h₃ h₄
    (heq : OperationPtr.linkBetweenWithParent self ctx prevOp nextOp parent h₁ h₂ h₃ h₄ = some newCtx) :
    block.get newCtx =
    if parent = some block then
      { block.get ctx hbl with firstOp := if prevOp.isSome then (block.get ctx hbl).firstOp else self,
                               lastOp := if nextOp.isSome then (block.get ctx hbl).lastOp else self }
    else
      block.get ctx hbl := by
  have := BlockPtr.get!_linkBetweenWithParent block h₁ h₂ h₃ h₄ (heq := heq)
  grind

@[grind =>]
theorem RegionPtr.get!_linkBetweenWithParent (region : RegionPtr) h₁ h₂ h₃ h₄
    (heq : OperationPtr.linkBetweenWithParent self ctx prevOp nextOp parent h₁ h₂ h₃ h₄ = some newCtx) :
    region.get! newCtx = region.get! ctx := by
  simp only [OperationPtr.linkBetweenWithParent] at heq
  grind

@[grind =>]
theorem BlockPtr.get!_insertOp? (block : BlockPtr)
    (hipWf : ip.Wf ctx newOp) (heq : Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx) :
    block.get! newCtx =
    match ip with
    | .AtEnd bl =>
       if block = bl then
         { block.get! ctx with lastOp := some newOp, firstOp := if (block.get! ctx).lastOp = none then some newOp else (block.get! ctx).firstOp }
       else
         block.get! ctx
    | .Before op' =>
       if block = (op'.get! ctx).parent then
         { block.get! ctx with firstOp := if (op'.get! ctx).prev = none then some newOp else (block.get! ctx).firstOp }
       else
         block.get! ctx := by
  simp only [Rewriter.insertOp?] at heq
  split at heq
  · split at heq <;> rename_i existingOp hip
    · grind
    · split
      · grind [OperationPtr.get!_linkBetweenWithParent]
      · split
        · simp
          split
          · grind [OperationPtr.get!_linkBetweenWithParent]
          · simp at *
            rw [BlockPtr.get!_linkBetweenWithParent (heq := heq)]
            simp
            rintro rfl
            split
            · congr
            · simp at *
              rw [OperationPtr.get!_eq_get (by grind)] at *
              cases h : (existingOp.get ctx (by grind)).prev <;> grind
        · grind [OperationPtr.get!_linkBetweenWithParent]
  · split
    · split
      · simp [BlockPtr.get!_linkBetweenWithParent (heq := heq)]
        split
        · split
          · grind
          · rw [BlockPtr.get!_eq_get (by grind)]
            cases h : (block.get ctx (by grind)).lastOp
            · simp
            · rename_i h1 _
              exfalso
              apply h1
              simp_all
        · grind
      · grind
    · grind

@[grind .]
theorem BlockPtr.get!_insertOp?_other (block : BlockPtr)
    (hipWf : ip.Wf ctx newOp) (heq : Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx)
    (hother : ip.block! ctx ≠ some block) :
    block.get! newCtx = block.get! ctx := by
  grind

 @[grind .]
theorem BlockPtr.get_insertOp?_other (block : BlockPtr) (hblock : block.InBounds ctx)
    (hipWf : ip.Wf ctx newOp) (heq : Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx)
    (hother : ip.block! ctx ≠ some block) :
    block.get newCtx = block.get ctx hblock := by
  rw [← BlockPtr.get!_eq_get (by grind)]
  grind

@[grind =>]
theorem BlockPtr.get!_insertOp?_firstuse (block : BlockPtr)
    (hipWf : ip.Wf ctx newOp) (heq : Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx) :
    (block.get! newCtx).firstUse = (block.get! ctx).firstUse := by
  grind

@[grind =>]
theorem BlockPtr.get!_insertOp?_parent (block : BlockPtr)
    (hipWf : ip.Wf ctx newOp) (heq : Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx) :
    (block.get! newCtx).parent = (block.get! ctx).parent := by
  grind

@[grind =>]
theorem BlockPtr.get!_insertOp?_arguments (block : BlockPtr)
    (hipWf : ip.Wf ctx newOp) (heq : Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx) :
    (block.get! newCtx).arguments = (block.get! ctx).arguments := by
  grind

@[grind =>]
theorem BlockOperandPtr.get!_insertOp?_firstuse (block : BlockOperandPtr)
    (hipWf : ip.Wf ctx newOp) (heq : Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx) :
    block.get! newCtx = block.get! ctx := by
  unfold Rewriter.insertOp? at heq
  grind

@[grind =>]
theorem RegionPtr.get!_insertOp?_firstuse (region : RegionPtr)
    (heq : Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx) :
    region.get! newCtx = region.get! ctx := by
  unfold Rewriter.insertOp? at heq
  grind

theorem OperationPtr.no_parent_of_get_insertBetweenWithParent_some
    (hneq : (nextOp = none ∧ prevOp = none) ∨ nextOp ≠ prevOp) (hnew : nextOp ≠ some self ∧ prevOp ≠ some self)
    (heq : OperationPtr.linkBetweenWithParent self ctx prevOp nextOp parent h₁ h₂ h₃ h₄ = some newCtx) :
    (self.get ctx).parent = none := by
  unfold OperationPtr.linkBetweenWithParent at heq
  unfold OperationPtr.setParentWithCheck at heq
  simp at heq
  split at heq
  · grind
  · rename_i h
    split at h
    · grind
    · rename_i h g
      rw [← OperationPtr.get!_eq_get (by grind), get!_linkBetween] at g
      all_goals grind

theorem OperationPtr.no_parent_of_get_insertOp?_some
    (hipWf : ip.Wf ctx newOp) (heq : Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx) :
    (newOp.get ctx).parent = none := by
  unfold Rewriter.insertOp? at heq
  unfold InsertPoint.Wf at hipWf
  split at heq
  · split at heq
    · grind
    · simp at heq
      apply no_parent_of_get_insertBetweenWithParent_some (heq := heq) <;> grind
  · grind [no_parent_of_get_insertBetweenWithParent_some]

/--
 - Get the index of the insertion point in the operation list of the block.
 - The index is where a new operation would be inserted.
 -/
noncomputable def InsertPoint.idxInOperationList (insertPoint : InsertPoint) (ctx : IRContext)
    (blockPtr : BlockPtr)
    (blockInBounds : blockPtr.InBounds ctx := by grind)
    (ctxWf : ctx.WellFormed := by grind) : Nat :=
  match insertPoint with
  | InsertPoint.Before op =>
    let opList := BlockPtr.operationList blockPtr ctx (by grind) blockInBounds
    opList.idxOf op
  | InsertPoint.AtEnd b =>
    (BlockPtr.operationList blockPtr ctx (by grind) blockInBounds).size

@[simp, grind =]
theorem InsertPoint.idxInOperationList_Before :
    InsertPoint.idxInOperationList (InsertPoint.Before op) ctx blockPtr blockInBounds ctxWf =
    (BlockPtr.operationList blockPtr ctx ctxWf blockInBounds).idxOf op := by
  simp [InsertPoint.idxInOperationList]

@[simp, grind =]
theorem InsertPoint.idxInOperationList_AtEnd :
    InsertPoint.idxInOperationList (InsertPoint.AtEnd blockPtr) ctx blockPtr blockInBounds ctxWf =
    (BlockPtr.operationList blockPtr ctx ctxWf blockInBounds).size := by
  simp [InsertPoint.idxInOperationList]

@[grind .]
theorem InsertPoint.idxInOperationList_inBounds :
    InsertPoint.idxInOperationList ip ctx blockPtr blockInBounds ctxWf ≤ (BlockPtr.operationList blockPtr ctx ctxWf blockInBounds).size := by
  simp only [InsertPoint.idxInOperationList]
  grind

@[grind =]
theorem InsertPoint.idxInOperationList_getElem? {op : OperationPtr} (hop : op.InBounds ctx)
    (hin : (op.get ctx).parent = some blockPtr ) :
    (blockPtr.operationList ctx ctxWf blockInBounds)[
      InsertPoint.idxInOperationList (.Before op) ctx blockPtr blockInBounds ctxWf]? = some op := by
  simp only [InsertPoint.idxInOperationList]
  rw [Array.getElem?_idxOf]
  suffices _ : op ∈ blockPtr.operationList ctx ctxWf blockInBounds by grind
  have := @BlockPtr.operationListWF ctx blockPtr blockInBounds ctxWf
  have := this.allOpsInChain
  grind

def InsertPoint.prev (ip : InsertPoint) (ctx : IRContext) : Option OperationPtr :=
  match ip with
  | InsertPoint.Before op => (op.get! ctx).prev
  | InsertPoint.AtEnd block => (block.get! ctx).lastOp

def InsertPoint.next (ip : InsertPoint) : Option OperationPtr :=
  match ip with
  | InsertPoint.Before op => op
  | InsertPoint.AtEnd _ => none

theorem InsertPoint.idxInOperationList_InsertPoint_prev_none
    (ipInBounds : ip.InBounds ctx) :
    InsertPoint.block ip ctx ipInBounds = some blockPtr →
    (InsertPoint.prev ip ctx = none ↔
    InsertPoint.idxInOperationList ip ctx blockPtr blockInBounds ctxWf = 0) := by
  have ⟨array, harray⟩ := ctxWf.opChain blockPtr blockInBounds
  simp (disch := grind) only [BlockPtr.operationList_iff_BlockPtr_OperationChainWellFormed] at harray
  have blockWF := @BlockPtr.operationListWF ctx blockPtr (by grind) (by grind)
  intro hblock
  cases ip
  case Before op =>
    simp_all only [idxInOperationList_Before, InsertPoint.block, InsertPoint.prev]
    grind [BlockPtr.OperationChainWellFormed]
  case AtEnd bl =>
    simp_all only [InsertPoint.block, InsertPoint.prev, InsertPoint.idxInOperationList]
    grind [BlockPtr.OperationChainWellFormed, Array.size_eq_zero_iff]

theorem InsertPoint.next_idxInOperationList ctxWf ip :
    BlockPtr.OperationChainWellFormed blockPtr ctx array blockInBounds →
    array[InsertPoint.idxInOperationList ip ctx blockPtr blockInBounds ctxWf]? = ip.next := by
  sorry

theorem InsertPoint.next_ne_firstOp (hWF : ctx.WellFormed) (ipInBounds : ip.InBounds ctx) :
    (BlockPtr.get blockPtr ctx blockInBounds).firstOp = some firstOp →
    InsertPoint.prev ip ctx ≠ none →
    InsertPoint.next ip ≠ some firstOp
    := by
  intro hfirst hprev
  have ⟨array, harray⟩ := hWF.opChain blockPtr blockInBounds
  have := InsertPoint.next_idxInOperationList hWF ip harray
  cases ip <;> grind [InsertPoint.prev, InsertPoint.next, BlockPtr.OperationChainWellFormed]


theorem InsertPoint.prev_idxInOperationList :
    let idx := InsertPoint.idxInOperationList ip ctx blockPtr blockInBounds ctxWf
    BlockPtr.OperationChainWellFormed blockPtr ctx array blockInBounds →
    idx > 0 →
    ip.prev ctx = some array[idx - 1]! := by
  sorry

theorem BlockPtr.get!_insertOp?_firstOp
    (hipWf : ip.Wf ctx newOp) (heq : Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx) :
    (BlockPtr.get! block newCtx).firstOp =
    if ip.block! ctx ≠ some block then
      (block.get! ctx).firstOp
    else if ip.prev ctx = none then
        some newOp
    else
      (block.get! ctx).firstOp := by
  sorry

theorem OperationPtr.get!_insertOp?_prev {op : OperationPtr}
    (hipWf : ip.Wf ctx newOp) (heq : Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx) :
    (op.get! newCtx).prev =
    if op ≠ newOp then
      if ip.next = some op then
        some newOp
      else
        (op.get! ctx).prev
    else
      ip.prev ctx
    := by
  have : (newOp.get ctx (by grind)).parent = none := by grind [OperationPtr.no_parent_of_get_insertOp?_some]
  by_cases h: op = newOp
  · subst op
    simp only [ne_eq, not_true_eq_false, ↓reduceIte]
    simp [OperationPtr.get!_insertOp? hipWf heq]
    grind [InsertPoint.prev]
  · simp [OperationPtr.get!_insertOp? hipWf heq]
    grind [InsertPoint.next]

theorem OperationPtr.get!_insertOp?_next {op : OperationPtr}
    (hipWf : ip.Wf ctx newOp) (heq : Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx) :
    (op.get! newCtx).next =
    if op = newOp then ip.next else
      if ip.prev ctx = some op then some newOp else (op.get! ctx).next := by
  have : (newOp.get ctx (by grind)).parent = none := by grind [OperationPtr.no_parent_of_get_insertOp?_some]
  by_cases h: op = newOp
  · grind [OperationPtr.get!_insertOp? hipWf heq, InsertPoint.next]
  · grind (splits := 20) [get!_insertOp? hipWf heq, InsertPoint.prev]

@[grind .]
theorem InsertPoint.idxInOperationList_Before_lt_size :
    InsertPoint.idxInOperationList (InsertPoint.Before op) ctx blockPtr blockInBounds ctxWf <
    (BlockPtr.operationList blockPtr ctx ctxWf blockInBounds).size := by
  sorry

@[grind! <=]
theorem OperationPtr.getParent_insertOp?_previousCtx
    (heq : Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx) :
    (newOp.get ctx).parent = none := by
  simp only [Rewriter.insertOp?, OperationPtr.linkBetweenWithParent, OperationPtr.setParentWithCheck] at heq
  split at heq <;> grind

@[grind .]
theorem InsertPoint.Wf_insertOp?_isSome (hWF : ctx.WellFormed) {ipInBounds : ip.InBounds ctx} :
    Rewriter.insertOp? ctx newOp ip newOpIn insIn ctxInBounds = some ctx' →
    ip.block ctx ipInBounds = some blockPtr →
    ip.Wf ctx newOp := by
  intro ctx' hipBlock
  have : (newOp.get ctx).parent = none := by grind
  have ⟨array, arrayWF⟩ := hWF.opChain blockPtr (by grind)
  simp only [InsertPoint.Wf]
  cases ip
  case Before existingOp =>
    have : (existingOp.get ctx).parent = some blockPtr := by grind
    simp only
    constructor
    · grind
    · cases hprev : (existingOp.get! ctx).prev
      case none => grind
      case some prev =>
        have : (prev.get ctx (by grind [BlockPtr.OperationChainWellFormed])).parent = some blockPtr := by
          rw [OperationPtr.get!_eq_get (by grind)] at hprev
          apply OperationPtr.getParent_prev_eq (opPtr := existingOp) (array := array) <;> grind
        grind [BlockPtr.OperationChainWellFormed_prev_ne]
  case AtEnd bl =>
    simp only
    simp [InsertPoint.block] at hipBlock
    subst bl
    rw [BlockPtr.get!_eq_get (by grind)]
    cases hlast: (blockPtr.get ctx (by grind)).lastOp
    case none => grind
    case some lastOp =>
      have : (lastOp.get ctx (by grind)).parent = some blockPtr := by grind [BlockPtr.OperationChainWellFormed]
      grind

theorem BlockPtr.OperationChainWellFormed_Rewriter_insertOp?_other
    (hol : BlockPtr.operationList blockPtr ctx ctxWellFormed blockInBounds = array)
    (hctx' : Rewriter.insertOp? ctx newOp ip newOpIn insIn ctxInBounds = some ctx')
    (ipParent : InsertPoint.block ip ctx ipInBounds ≠ some blockPtr) :
      blockPtr.OperationChainWellFormed ctx' array (by grind) := by
  have ipWf : ip.Wf ctx newOp := by rcases ip <;> grind
  apply IRContext.OperationChainWellFormed_unchanged ctx <;> grind

theorem BlockPtr.OperationChainWellFormed_Rewriter_insertOp?_self
    (hWf : BlockPtr.operationList blockPtr ctx ctxWellFormed blockInBounds = array)
    (hctx' : Rewriter.insertOp? ctx newOp ip newOpIn insIn ctxInBounds = some ctx')
    (ipParent : InsertPoint.block ip ctx ipInBounds = some blockPtr) :
      blockPtr.OperationChainWellFormed ctx'
        (array.insertIdx (ip.idxInOperationList ctx blockPtr blockInBounds ctxWellFormed)
          newOp (by grind [InsertPoint.idxInOperationList_inBounds])) (by grind) := by
  have ipWf := InsertPoint.Wf_insertOp?_isSome ctxWellFormed hctx' ipParent
  have chainWf := ctxWellFormed.opChain
  have : (newOp.get ctx (by grind)).parent = none := by grind
  have hOCWF := @BlockPtr.operationListWF ctx blockPtr (by grind) (by grind)
  simp only [hWf] at hOCWF
  simp only [←InsertPoint.block!_eq_block] at ipParent
  constructor
  case opParent =>
    intros op hop
    simp [Array.mem_insertIdx] at hop
    grind [BlockPtr.OperationChainWellFormed]
  case last =>
    simp only [Array.size_insertIdx, Nat.add_one_sub_one, Nat.lt_add_one, getElem?_pos]
    simp [←BlockPtr.get!_eq_get]
    simp [BlockPtr.get!_insertOp? blockPtr ipWf hctx']
    cases hip: ip
    case Before existingOp =>
      subst ip
      simp only [InsertPoint.block!] at ipParent
      simp only [ipParent, ↓reduceIte, InsertPoint.idxInOperationList_Before]
      rw [Array.getElem_insertIdx_of_gt] <;> grind [BlockPtr.OperationChainWellFormed]
    case AtEnd => grind [InsertPoint.idxInOperationList]
  case prevFirst =>
    intros firstOp hFirstOp
    simp only [←BlockPtr.get!_eq_get] at hFirstOp
    simp (disch := grind) only [BlockPtr.get!_insertOp?_firstOp ipWf hctx'] at hFirstOp
    simp only [ipParent, ne_eq, not_true_eq_false, ↓reduceIte] at hFirstOp
    split at hFirstOp
    case isTrue =>
      simp only [Option.some.injEq] at hFirstOp
      subst firstOp
      simp only [←OperationPtr.get!_eq_get, OperationPtr.get!_insertOp?_prev ipWf hctx']
      grind
    case isFalse ipprev =>
      simp only [←OperationPtr.get!_eq_get, OperationPtr.get!_insertOp?_prev ipWf hctx']
      grind [InsertPoint.next_ne_firstOp, BlockPtr.OperationChainWellFormed]
  case allOpsInChain =>
    intros op opInBounds opParent
    simp only [←OperationPtr.get!_eq_get, OperationPtr.get!_insertOp?_parent op ipWf hctx'] at opParent
    simp [Array.mem_insertIdx]
    split at opParent
    · grind
    · grind [BlockPtr.OperationChainWellFormed]
  case arrayInBounds =>
    simp only [Array.mem_insertIdx]
    rintro op (hold | hnew)
    · grind
    · have : op.InBounds ctx := by grind [BlockPtr.OperationChainWellFormed]
      grind
  case first =>
    simp only [←BlockPtr.get!_eq_get, BlockPtr.get!_insertOp?_firstOp ipWf hctx']
    simp only [ipParent, ne_eq, not_true_eq_false, ↓reduceIte, Array.size_insertIdx,
      Nat.zero_lt_succ, getElem?_pos]
    have := InsertPoint.idxInOperationList_InsertPoint_prev_none ipInBounds (ctxWf := ctxWellFormed) (blockPtr := blockPtr) (blockInBounds := by grind)
    split
    case isTrue => grind
    case isFalse h =>
      simp only [h] at this
      have := InsertPoint.idxInOperationList_InsertPoint_prev_none ipInBounds (ctxWf := ctxWellFormed) (blockPtr := blockPtr) (blockInBounds := by grind)
      rw [Array.getElem_insertIdx_of_lt]
      · grind [BlockPtr.OperationChainWellFormed]
      · grind
  case prev =>
    simp only [gt_iff_lt, Array.size_insertIdx]
    simp only [←OperationPtr.get!_eq_get]
    intros i h₁ h₂
    let idx := ip.idxInOperationList ctx blockPtr blockInBounds ctxWellFormed
    simp [OperationPtr.get!_insertOp?_prev ipWf hctx']
    have idxInBounds := @InsertPoint.idxInOperationList_inBounds ip ctx blockPtr (by grind) (by grind)
    simp only [hWf] at idxInBounds
    by_cases hi : i < idx
    · simp (disch := grind) only [Array.getElem_insertIdx_of_lt]
      have : array[i]? ≠ some newOp := by grind [BlockPtr.OperationChainWellFormed]
      simp only [Array.getElem_eq_iff, this, ↓reduceIte]
      have : ip.next = array[idx]? := by grind [InsertPoint.next_idxInOperationList]
      suffices ip.next ≠ some array[i] by grind [BlockPtr.OperationChainWellFormed]
      grind [BlockPtr.OperationChainWellFormed_array_injective]
    by_cases hi' : i = idx
    · subst i idx
      simp only [Array.getElem_insertIdx_self, ↓reduceIte]
      simp (disch := grind) [Array.getElem_insertIdx_of_lt]
      have := @InsertPoint.prev_idxInOperationList
      grind
    by_cases hi'' : i = idx + 1
    · simp (disch := grind) only [Array.getElem_insertIdx_of_gt]
      have : idx = i - 1 := by grind
      have : array[i - 1] ≠ newOp := by grind [BlockPtr.OperationChainWellFormed]
      simp only [this, ↓reduceIte]
      have := InsertPoint.next_idxInOperationList ctxWellFormed ip hOCWF
      grind
    · simp (disch := grind) only [Array.getElem_insertIdx_of_gt]
      have : array[i - 1] ≠ newOp := by grind [BlockPtr.OperationChainWellFormed]
      simp only [this, ↓reduceIte]
      have := InsertPoint.next_idxInOperationList ctxWellFormed ip hOCWF
      suffices ip.next ≠ some array[i - 1] by grind [BlockPtr.OperationChainWellFormed]
      grind [BlockPtr.OperationChainWellFormed_array_injective]
  case next =>
    simp only [Array.size_insertIdx, ←OperationPtr.get!_eq_get]
    intros i hi
    let idx := ip.idxInOperationList ctx blockPtr blockInBounds ctxWellFormed
    simp [OperationPtr.get!_insertOp?_next ipWf hctx']
    have idxInBounds := @InsertPoint.idxInOperationList_inBounds ip ctx blockPtr (by grind) (by grind)
    simp only [hWf] at idxInBounds
    by_cases hi' : i = idx
    · grind [InsertPoint.next_idxInOperationList]
    by_cases hi'' : i + 1 = idx
    · simp (disch := grind) only [Array.getElem_insertIdx_of_lt]
      have : idx = i + 1 := by grind
      have : array[i] ≠ newOp := by grind [BlockPtr.OperationChainWellFormed]
      simp [this, ↓reduceIte]
      have := @InsertPoint.prev_idxInOperationList
      grind
    by_cases hi : i > idx
    · simp (disch := grind) only [Array.getElem_insertIdx_of_gt]
      have : array[i-1]? ≠ some newOp := by grind [BlockPtr.OperationChainWellFormed]
      simp only [Array.getElem_eq_iff, this, ↓reduceIte]
      suffices ip.prev ctx ≠ some array[i - 1] by grind [BlockPtr.OperationChainWellFormed]
      by_cases idx = 0
      · rcases ip
        · have := hOCWF.first
          grind [@hOCWF.prevFirst array[0] (by grind), InsertPoint.prev]
        · grind
      rcases ip with ⟨op⟩ | _
      · simp [InsertPoint.prev]
        have : (array[idx].get ctx (by grind [BlockPtr.OperationChainWellFormed])).prev = some array[idx - 1] := by
          apply BlockPtr.OperationChainWellFormed.prev hOCWF; grind
        grind [BlockPtr.OperationChainWellFormed_array_injective]
      · grind [InsertPoint.next_idxInOperationList]
    · have : i < idx - 1 := by cutsat
      simp (disch := grind) only [Array.getElem_insertIdx_of_lt]
      have : array[i]? ≠ some newOp := by grind [BlockPtr.OperationChainWellFormed]
      simp only [Array.getElem_eq_iff, this, ↓reduceIte]
      have : ip.prev ctx = some array[idx-1]! := by grind [InsertPoint.prev_idxInOperationList]
      suffices ip.prev ctx ≠ some array[i] by grind [BlockPtr.OperationChainWellFormed]
      grind [BlockPtr.OperationChainWellFormed_array_injective]

theorem BlockPtr.operationList_Rewriter_insertOp?
    (hWf : BlockPtr.operationList blockPtr ctx ctxWellFormed blockInBounds = array)
    (hctx' : Rewriter.insertOp? ctx newOp ip newOpIn insIn ctxInBounds = some ctx')
    (ipParent : InsertPoint.block ip ctx ipInBounds = some blockPtr') :
      BlockPtr.operationList blockPtr ctx' ctxWellFormed' blockInBounds' =
      if blockPtr = blockPtr' then
        array.insertIdx (ip.idxInOperationList ctx blockPtr blockInBounds ctxWellFormed) newOp (by grind [InsertPoint.idxInOperationList_inBounds])
      else
        array := by
  split
  · simp only [←BlockPtr.operationList_iff_BlockPtr_OperationChainWellFormed]
    grind [BlockPtr.OperationChainWellFormed_Rewriter_insertOp?_self]
  · simp only [←BlockPtr.operationList_iff_BlockPtr_OperationChainWellFormed]
    grind [BlockPtr.OperationChainWellFormed_Rewriter_insertOp?_other]

@[grind =>]
theorem OpOperandPtr.get!_insertOp?
    (hctx' : Rewriter.insertOp? ctx newOp ip newOpIn insIn ctxInBounds = some ctx') (opr: OpOperandPtr) :
    opr.get! ctx' = opr.get! ctx := by
  simp only [Rewriter.insertOp?] at hctx'
  grind

@[grind =>]
theorem OperationPtr.getNumOperands!_insertOp?
    (hctx' : Rewriter.insertOp? ctx newOp ip newOpIn insIn ctxInBounds = some ctx') (op: OperationPtr) :
    op.getNumOperands! ctx' = op.getNumOperands! ctx := by
  sorry -- We are missing some lemmas to do this

theorem Rewriter.insertOp?_WellFormed (ctx : IRContext) (hctx : ctx.WellFormed)
    (newOp : OperationPtr) (ip : InsertPoint)
    (newOpIn : newOp.InBounds ctx := by grind)
    (hwf : ip.Wf ctx newOp)
    (insIn : ip.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) (newCtx : IRContext) :
    Rewriter.insertOp? ctx newOp ip newOpIn insIn ctxInBounds = some newCtx →
    newCtx.WellFormed := by
  intros heq
  have ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := hctx
  constructor
  case inBounds =>
    grind
  case valueUseDefChains =>
    intros val hval
    have ⟨array, harray⟩ := h₂ val (by grind)
    exists array
    apply IRContext.ValuePtr_UseDefChainWellFormed_unchanged ctx <;> grind [ValuePtr.getFirstUse]
  case blockUseDefChains =>
    intros block hblock
    have ⟨array, harray⟩ := h₃ block (by grind)
    exists array
    apply IRContext.BlockPtr_UseDefChainWellFormed_unchanged ctx <;>
      grind [=_ BlockPtr.get!_eq_get, =_ BlockOperandPtr.get!_eq_get]
  case opChain =>
    intros block hblock
    have ⟨array, harray⟩ := h₄ block (by grind)
    by_cases some block = ip.block ctx insIn
    · exists (array.insertIdx (ip.idxInOperationList ctx block (by grind) (by grind)) newOp (by grind [InsertPoint.idxInOperationList_inBounds]))
      grind [BlockPtr.OperationChainWellFormed_Rewriter_insertOp?_self]
    · exists array
      grind [BlockPtr.OperationChainWellFormed_Rewriter_insertOp?_other]
  case blockChain =>
    intros region hregion
    have ⟨array, harray⟩ := h₅ region (by grind)
    exists array
    apply IRContext.BlockChainWellFormed_unchanged (by grind) (by grind) harray <;>
      grind [=_ RegionPtr.get!_eq_get, =_ BlockPtr.get!_eq_get]
  case operations =>
    intros op hop
    have : op.InBounds ctx := by grind
    have ⟨ha, hb, hc, hd, he, hf⟩ := h₆ op this
    -- Add the correct lemmas so we don't manually unfold definitions here
    constructor <;> grind [=_ RegionPtr.get!_eq_get, =_ OperationPtr.get!_eq_get, OperationPtr.getResult, OperationPtr.nextResult, OperationPtr.getNumResults]
  case blocks =>
    intros bl hbl
    have : bl.InBounds ctx := by grind
    have ⟨ha, hb, hc⟩ := h₇ bl this
    constructor <;> grind [=_ BlockPtr.get!_eq_get]
  case regions =>
    intros rg hrg
    have : rg.InBounds ctx := by grind
    have ⟨ha, hb⟩ := h₈ rg this
    constructor <;> grind [=_ RegionPtr.get!_eq_get]

theorem Rewriter.detachOp_WellFormed (ctx : IRContext) (wf : ctx.WellFormed)
    (hctx : ctx.FieldsInBounds) (op : OperationPtr)
    (hIn : op.InBounds ctx)
    (hasParent : (op.get ctx hIn).parent.isSome)
    (newCtx : IRContext) :
    Rewriter.detachOp ctx hctx op hIn hasParent = newCtx →
    newCtx.WellFormed := by
  sorry

theorem BlockPtr.operationList_Rewriter_detachOp
    (hWf : BlockPtr.operationList blockPtr ctx ctxWellFormed blockInBounds = array) :
      BlockPtr.operationList blockPtr (Rewriter.detachOp ctx hctx op hIn hasParent) ctxWellFormed' blockInBounds' =
      if blockPtr = blockPtr' then
        array.erase op
      else
        array := by
  sorry

theorem Rewriter.eraseOp_WellFormed (ctx : IRContext) (wf : ctx.WellFormed)
    (hctx : ctx.FieldsInBounds) (op : OperationPtr)
    (hop : op.InBounds ctx)
    (hasParent : (op.get ctx hop).parent.isSome)
    (newCtx : IRContext) :
    Rewriter.eraseOp ctx op hctx hop hasParent = newCtx →
    newCtx.WellFormed := by
  sorry

theorem BlockPtr.operationList_Rewriter_eraseOp
    (hWf : BlockPtr.operationList blockPtr ctx ctxWellFormed blockInBounds = array) :
      BlockPtr.operationList blockPtr (Rewriter.eraseOp ctx op hctx hop hasParent) ctxWellFormed' blockInBounds' =
      if blockPtr = blockPtr' then
        array.erase op
      else
        array := by
  sorry

theorem OperationPtr.getOperand_Rewriter_eraseOp
    (heq : Rewriter.eraseOp ctx op hctx hop hasParent = newCtx) (hne : op ≠ op'):
    OperationPtr.getOperand op' newCtx idx inBounds idxInBounds =
    OperationPtr.getOperand op' ctx idx (by sorry) (by sorry) := by
  sorry

end Mlir
