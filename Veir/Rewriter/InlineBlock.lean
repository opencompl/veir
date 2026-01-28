import Veir.Rewriter.Basic
import Veir.Rewriter.WellFormed.Rewriter.Operation
import Veir.Rewriter.GetSetInBounds

namespace Veir

theorem Rewriter.insertOp?.operationList {block : BlockPtr}
  (blockIn : block.InBounds ctx) (ctxWf : ctx.WellFormed)
  (hwf : ip.block! ctx = some block')
  (h : Rewriter.insertOp? ctx op ip opIn ipIn ctxIn = some ctx') :
  block.operationList ctx' (by grind [Rewriter.insertOp?_WellFormed]) (by grind) =
  if h: block = block' then
    (block.operationList ctx ctxWf blockIn).insertIdx (ip.idxIn ctx block' (by grind) (by grind) (by grind)) op (by apply InsertPoint.idxIn.le_size_array; grind)
  else
    block.operationList ctx ctxWf blockIn := by
  have ⟨array, hArray⟩ := ctxWf.opChain block (by grind)
  have ⟨array', hArray'⟩ := ctxWf.opChain block' (by grind)
  simp only [Rewriter.insertOp?] at h
  split at h; grind; rename_i parent hparent
  have : block' = parent := by grind
  subst parent
  by_cases heq : block = block'
  · subst block'
    simp only [↓reduceDIte]
    have := BlockPtr.opChain_OperationPtr_linkBetweenWithParent_self (ctx := ctx) (by grind)
      h (ip := ip) (by grind) (by grind) (by grind) (by grind) hArray
    simp [BlockPtr.operationList_iff_BlockPtr_OpChain.mp this,
          BlockPtr.operationList_iff_BlockPtr_OpChain.mp hArray]
  · have h := BlockPtr.opChain_OperationPtr_linkBetweenWithParent_other (ctx := ctx) h (array := array) (block' := block)
    simp only [← InsertPoint.prev!_eq_prev] at h
    have h := h (by grind [InsertPoint.prev.maybe₁_parent])
    have h := h (by grind [InsertPoint.next.maybe₁_parent])
    have h := h (by grind) (by grind)
    simp [BlockPtr.operationList_iff_BlockPtr_OpChain.mp h,
          BlockPtr.operationList_iff_BlockPtr_OpChain.mp hArray]
    grind

theorem Rewriter.detachOp.operationList_size
  {block : BlockPtr}
  (blockIn : block.InBounds ctx) (ctxWf : ctx.WellFormed) :
  (block.operationList (Rewriter.detachOp ctx op hctx hin hparent) (by grind [Rewriter.detachOp_WellFormed]) (by grind)).size =
  if (op.get! ctx).parent = block then
    (block.operationList ctx ctxWf blockIn).size - 1
  else
    (block.operationList ctx ctxWf blockIn).size := by
  have ⟨array, hArray⟩ := ctxWf.opChain block (by grind)
  cases hparent : (op.get! ctx).parent; grind
  rename_i block'
  by_cases heq : block' = block
  · subst block'
    simp only [↓reduceIte]
    simp only [BlockPtr.operationList_iff_BlockPtr_OpChain.mp (BlockPtr.opChain_detachOp_self hArray hparent)]
    simp only [BlockPtr.operationList_iff_BlockPtr_OpChain.mp hArray]
    have : op ∈ array := by grind [IRContext.WellFormed, BlockPtr.OpChain]
    grind
  · simp only [Option.some.injEq, heq, ↓reduceIte]
    have ⟨array', hArray'⟩ := ctxWf.opChain block' (by grind [IRContext.WellFormed])
    simp only [BlockPtr.operationList_iff_BlockPtr_OpChain.mp (BlockPtr.opChain_detachOp_other hArray hArray' hparent (by grind))]
    simp [BlockPtr.operationList_iff_BlockPtr_OpChain.mp hArray]

@[grind =]
theorem InsertPoint.block!_detachOp_of_ne {ip : InsertPoint} (ipBlock : ip.block! ctx ≠ (op.get! ctx).parent) :
    ip.block! (Rewriter.detachOp ctx op hctx hin hparent) = ip.block! ctx := by
  cases ip
  case before op' =>
    grind
  · grind [InsertPoint.block!]

@[grind <=]
theorem Rewriter.wellFormed_insertOp?_detachOp
    (ctxWf : ctx.WellFormed)
    (hip : ip.block! ctx = some block')
    (hparent' : (op.get! ctx).parent ≠ some block') :
    Rewriter.insertOp? (Rewriter.detachOp ctx op hctx hin hparent) op ip opIn ipIn ctxIn = some ctx' →
    ctx'.WellFormed := by
  intro h
  apply Rewriter.insertOp?_WellFormed (Rewriter.detachOp ctx op hctx hin hparent) (ip := ip) (block := block') (newOp := op)
    <;> grind [Rewriter.detachOp_WellFormed]

theorem Rewriter.detachOp.operationList
  {block : BlockPtr}
  (blockIn : block.InBounds ctx) (ctxWf : ctx.WellFormed) :
  block.operationList (Rewriter.detachOp ctx op hctx hin hparent) (by grind [Rewriter.detachOp_WellFormed]) (by grind) =
  if (op.get! ctx).parent = block then
    (block.operationList ctx ctxWf blockIn).erase op
  else
    block.operationList ctx ctxWf blockIn := by
  have ⟨array, hArray⟩ := ctxWf.opChain block (by grind)
  cases hparent : (op.get! ctx).parent; grind
  rename_i block'
  by_cases heq : block' = block
  · subst block'
    simp only [↓reduceIte]
    simp only [BlockPtr.operationList_iff_BlockPtr_OpChain.mp (BlockPtr.opChain_detachOp_self hArray hparent)]
    simp only [BlockPtr.operationList_iff_BlockPtr_OpChain.mp hArray]
  · simp only [Option.some.injEq, heq, ↓reduceIte]
    have ⟨array', hArray'⟩ := ctxWf.opChain block' (by grind [IRContext.WellFormed])
    simp only [BlockPtr.operationList_iff_BlockPtr_OpChain.mp (BlockPtr.opChain_detachOp_other hArray hArray' hparent (by grind))]
    simp [BlockPtr.operationList_iff_BlockPtr_OpChain.mp hArray]

theorem Rewriter.insertOp?_detachOp_operationList {block : BlockPtr}
  (blockIn : block.InBounds ctx) (ctxWf : ctx.WellFormed)
  (ipIn' : ip.InBounds ctx)
  (hwf : ip.block! ctx = some block')
  (hparent' : (op.get! ctx).parent ≠ some block')
  (h : Rewriter.insertOp? (Rewriter.detachOp ctx op hctx hin hparent) op ip opIn ipIn ctxIn = some ctx') :
  block.operationList ctx' (by grind) (by simp [← GenericPtr.iff_block]; rw [← Rewriter.insertOp?_inBounds_mono _ h]; grind) =
  if h: block = block' then
    (block.operationList ctx ctxWf blockIn).insertIdx (ip.idxIn ctx block' (by grind) (by grind) (by grind)) op (by apply InsertPoint.idxIn.le_size_array; grind)
  else if (op.get! ctx).parent = block then
    (block.operationList ctx ctxWf blockIn).erase op
  else
    block.operationList ctx ctxWf blockIn := by
  rw [Rewriter.insertOp?.operationList (h := h) (ctx := Rewriter.detachOp ctx op hctx hin hparent) (block' := block') (ctxWf := (by grind [Rewriter.detachOp_WellFormed])) (blockIn := by grind) (by grind)]
  sorry
  --rw [Rewriter.detachOp.operationList]

theorem InsertPoint.idxIn_insertOp?_detachOp
  (ctxWf : ctx.WellFormed)
  (ipIn' : ip.InBounds ctx)
  (hwf : ip.block! ctx = some blockTo)
  (hparent' : (op.get! ctx).parent ≠ some blockTo)
  (h : Rewriter.insertOp? (Rewriter.detachOp ctx op hctx hin hparent) op ip opIn ipIn ctxIn = some ctx') :
  ip.idxIn ctx' blockTo inBounds parent wf =
  (ip.idxIn ctx blockTo (by grind) (by grind) (by grind)) + 1 := by sorry

def Rewriter.inlineBlock (ctx : IRContext) (block : BlockPtr)
    (ip : InsertPoint) (ipIn : ip.InBounds ctx := by grind)
    (ipBlock : ip.block! ctx = some block' := by grind)
    (blockNe : block ≠ block' := by grind)
    (blockIn : block.InBounds ctx := by grind)
    (ctxWf : ctx.WellFormed := by grind) := do
  match h: (block.get ctx).firstOp with
  | none => some ctx
  | some firstOpPtr => do
  let ctx₀ := detachOp ctx firstOpPtr (by grind) (by grind) (by grind [IRContext.WellFormed])
  rlet hctx: ctx₁ ← insertOp? ctx₀ firstOpPtr ip (by grind) (by cases ip <;> grind [InsertPoint.InBounds]) (by grind)
  inlineBlock ctx₁ block ip
    (by cases ip <;> grind [InsertPoint.InBounds])
    (block' := block')
    (by
      simp only [InsertPoint.block!] at ipBlock |-
      have : (firstOpPtr.get! ctx).parent = block := by grind [IRContext.WellFormed]
      grind
    )
    (by grind)
    (by (have : block.InBounds ctx₀ := by grind); grind)
    (by
      apply Rewriter.insertOp?_WellFormed ctx₀ (by grind [Rewriter.detachOp_WellFormed])
        firstOpPtr ip (block := block') (by grind) (by grind)
      · simp only [InsertPoint.block!] at ipBlock |-
        have : (firstOpPtr.get! ctx).parent = block := by grind [IRContext.WellFormed]
        grind
      · grind
      · grind
    )
termination_by (block.operationList ctx ctxWf blockIn).size
decreasing_by
  rw [Rewriter.insertOp?.operationList (h := hctx) (block' := block')]
  · simp only [blockNe, ↓reduceDIte, ctx₀]
    rw [Rewriter.detachOp.operationList_size (block := block)]
    · have : (firstOpPtr.get! ctx).parent = block := by grind [IRContext.WellFormed]
      simp only [this, ↓reduceIte, gt_iff_lt]
      apply Nat.sub_one_lt
      have ⟨array, hArray⟩ := ctxWf.opChain block (by grind)
      grind [BlockPtr.OpChain]
    · grind
    · grind
  · grind
  · grind [Rewriter.insertOp?_WellFormed, Rewriter.detachOp_WellFormed]
  · simp only [InsertPoint.block!] at ipBlock |-
    have : (firstOpPtr.get! ctx).parent = block := by grind [IRContext.WellFormed]
    grind

def Rewriter.inlineBlock_wellFormed :
    Rewriter.inlineBlock ctx block ip ipIn ipBlock blockNe blockIn ctxWf = some newCtx →
    newCtx.WellFormed := by
  rename_i block'
  induction hind: (block.operationList ctx ctxWf blockIn).size generalizing newCtx ctx
  case zero =>
    intro h
    unfold inlineBlock at h
    have ⟨array, hArray⟩ := ctxWf.opChain block blockIn
    have : array = #[] := by grind
    have : (block.get! ctx).firstOp = none := by grind [BlockPtr.OpChain]
    grind
  case succ n ih =>
    intro h
    unfold inlineBlock at h
    split at h
    · grind
    · simp only at h
      split at h
      · grind
      · rename_i firstOpPtr heq ctx₁ h'
        apply @ih ctx₁ (by grind) (by grind) (by grind) (by grind) newCtx _ (by grind)
        rw [Rewriter.insertOp?.operationList (h := h') (block' := block')]
        · simp only [blockNe, ↓reduceDIte]
          rw [Rewriter.detachOp.operationList_size]
          · have : (firstOpPtr.get! ctx).parent = block := by grind [BlockPtr.OpChain, IRContext.WellFormed]
            simp only [this, ↓reduceIte]
            grind
          · grind
          · grind
        · grind
        · grind [Rewriter.detachOp_WellFormed]
        · simp only [InsertPoint.block!] at ipBlock |-
          grind

theorem Rewriter.inlineBlock_inBounds_block :
    Rewriter.inlineBlock ctx block ip ipIn ipBlock blockNe blockIn ctxWf = some newCtx →
    (BlockPtr.InBounds block₀ ctx ↔
    BlockPtr.InBounds block₀ newCtx) := by
  intro h
  rename_i block'
  induction hind: (block.operationList ctx ctxWf blockIn).size generalizing newCtx ctx
  case zero =>
    unfold inlineBlock at h
    have ⟨array, hArray⟩ := ctxWf.opChain block blockIn
    have : array = #[] := by grind
    have : (block.get! ctx).firstOp = none := by grind [BlockPtr.OpChain]
    grind
  case succ n ih =>
    unfold inlineBlock at h
    split at h
    · grind
    · simp only at h
      split at h
      · grind
      · rename_i firstOpPtr heq ctx₁ h'
        have : block₀.InBounds ctx ↔ block₀.InBounds ctx₁ := by grind
        simp only [this]
        apply @ih ctx₁ (by grind) (by grind) (by grind) (by grind) newCtx (by grind)
        rw [Rewriter.insertOp?.operationList (h := h') (block' := block')]
        · simp only [blockNe, ↓reduceDIte]
          rw [Rewriter.detachOp.operationList_size]
          · have : (firstOpPtr.get! ctx).parent = block := by grind [BlockPtr.OpChain, IRContext.WellFormed]
            simp only [this, ↓reduceIte]
            grind
          · grind
          · grind
        · grind
        · grind [Rewriter.detachOp_WellFormed]
        · simp only [InsertPoint.block!] at ipBlock |-
          grind

theorem BlockPtr.operationList_Rewriter_inlineBlock_from
    (hWF : ctx.WellFormed) (hblockTo : ip.block ctx ipIn = some blockTo)
    (hNewCtx : Rewriter.inlineBlock ctx blockFrom ip ipIn ipBlock blockNe blockIn ctxWf = some newCtx) :
    blockFrom.operationList newCtx (Rewriter.inlineBlock_wellFormed hNewCtx) (by
      have := Rewriter.inlineBlock_inBounds_block hNewCtx (block₀ := blockFrom); grind) =
    #[] := by
  have ⟨array, hArray⟩ := ctxWf.opChain blockFrom blockIn
  have fromNeTo : blockFrom ≠ blockTo := by grind [BlockPtr.OpChain]
  induction hind: (blockFrom.operationList ctx ctxWf blockIn).size generalizing newCtx ctx array
  case zero =>
    unfold Rewriter.inlineBlock at hNewCtx
    have ⟨array, hArray⟩ := ctxWf.opChain blockFrom blockIn
    have : array = #[] := by grind
    have : (blockFrom.get! ctx).firstOp = none := by grind [BlockPtr.OpChain]
    grind
  case succ n ih =>
    simp only [BlockPtr.operationList_iff_BlockPtr_OpChain.mp hArray] at hind
    cases hFirst: (blockFrom.get ctx).firstOp; grind [BlockPtr.OpChain]
    rename_i firstOpPtr
    unfold Rewriter.inlineBlock at hNewCtx
    split at hNewCtx; grind
    simp only at hNewCtx
    split at hNewCtx; grind
    rename_i firstOpPtr heq ctx₀ h'
    have ctx₀Wf : ctx₀.WellFormed := by grind
    have ⟨arrayFrom, hArrayFrom⟩ := ctx₀Wf.opChain blockFrom (by grind)
    apply @ih ctx₀ (by grind) (by grind) (by grind) (by grind) newCtx _ (by grind)
    · apply hNewCtx
    · apply hArrayFrom
    · rw [Rewriter.insertOp?.operationList (h := h') (block' := blockTo)]
      · simp only [fromNeTo, ↓reduceDIte]
        rw [Rewriter.detachOp.operationList_size] <;> grind
      · grind
      · grind [Rewriter.detachOp_WellFormed]
      · simp only [InsertPoint.block!] at ipBlock |-
        have : (firstOpPtr.get! ctx).parent = blockFrom := by grind [IRContext.WellFormed]
        grind
    · grind

@[simp]
theorem Array.extract_insertIdx_zero_succ {l : Array α} {inBounds} :
    (Array.insertIdx l idx elem inBounds).extract 0 (idx + 1) =
    l.extract 0 idx ++ #[elem] := by
  sorry

@[simp]
theorem Array.extract_insertIdx_succ_ub {l : Array α} {inBounds} :
    (Array.insertIdx l idx elem inBounds).extract (idx + 1) ub =
    l.extract idx ub := by
  sorry

theorem Array.append_singleton_erase_of_getElem?_zero [BEq α] {l : Array α} :
    l[0]? = some x →
    #[x] ++ (l.erase x) = l := by
  sorry


theorem BlockPtr.operationList_Rewriter_inlineBlock_to
    (hWF : ctx.WellFormed) (hblockTo : ip.block ctx ipIn = some blockTo)
    (hNewCtx : Rewriter.inlineBlock ctx blockFrom ip ipIn ipBlock blockNe blockIn ctxWf = some newCtx) :
    blockTo.operationList newCtx (Rewriter.inlineBlock_wellFormed hNewCtx) (by
      have := Rewriter.inlineBlock_inBounds_block hNewCtx (block₀ := blockTo); grind) =
    let array := blockTo.operationList ctx hWF (by grind)
    let idx := ip.idxIn ctx blockTo (by grind) (by grind) (by grind)
    (array.take idx ++ (blockFrom.operationList ctx hWF (by grind)) ++ array.drop idx) := by
  have fromNeTo : blockFrom ≠ blockTo := by grind [BlockPtr.OpChain]
  induction hind: (blockFrom.operationList ctx ctxWf blockIn).size generalizing newCtx ctx
  case zero =>
    unfold Rewriter.inlineBlock at hNewCtx
    have ⟨array, hArray⟩ := ctxWf.opChain blockFrom blockIn
    have : array = #[] := by grind
    have : (blockFrom.get! ctx).firstOp = none := by grind [BlockPtr.OpChain]
    grind
  case succ n ih =>
    have ⟨array, hArray⟩ := ctxWf.opChain blockFrom blockIn
    simp only
    simp only [BlockPtr.operationList_iff_BlockPtr_OpChain.mp hArray] at hind
    cases hFirst: (blockFrom.get ctx).firstOp; grind [BlockPtr.OpChain]
    rename_i firstOpPtr
    unfold Rewriter.inlineBlock at hNewCtx
    split at hNewCtx; grind
    simp only at hNewCtx
    split at hNewCtx; grind
    rename_i firstOpPtr heq ctx₀ h'
    have ctx₀Wf : ctx₀.WellFormed := by grind
    have ctx₁Wf : (Rewriter.detachOp ctx firstOpPtr (by grind) (by grind) (by grind)).WellFormed := by grind [Rewriter.detachOp_WellFormed]
    have ⟨arrayFrom, hArrayFrom⟩ := ctx₀Wf.opChain blockFrom (by grind)
    have hparent : (firstOpPtr.get! ctx).parent = some blockFrom := by grind
    have : (blockFrom.operationList ctx₀ (by grind) (by grind)).size = n := by
      have := @Rewriter.insertOp?_detachOp_operationList ctx blockTo firstOpPtr (by grind) (by grind) (by grind) ip (by grind) (by grind) (by grind) ctx₀ blockFrom (by grind) (by grind) (by grind) (by grind) (by grind) h'
      rw [this]
      simp [fromNeTo, hparent]
      have : firstOpPtr ∈ array := by grind [BlockPtr.OpChain]
      grind
    have ih := @ih ctx₀ (by grind) (by grind) (by grind) (by grind) newCtx (by grind) (by grind) hNewCtx (by grind)
    simp only [ih, Array.take_eq_extract, Array.drop_eq_extract, Array.append_assoc]
    have := @Rewriter.insertOp?_detachOp_operationList ctx blockTo firstOpPtr (by grind) (by grind) (by grind) ip (by grind) (by grind) (by grind) ctx₀ blockTo (by grind) (by grind) (by grind) (by grind) (by grind) h'
    rw [this]
    have := @Rewriter.insertOp?_detachOp_operationList ctx blockTo firstOpPtr (by grind) (by grind) (by grind) ip (by grind) (by grind) (by grind) ctx₀ blockFrom (by grind) (by grind) (by grind) (by grind) (by grind) h'
    rw [this]
    simp only [↓reduceDIte, Array.size_insertIdx]
    have := @InsertPoint.idxIn_insertOp?_detachOp blockTo ctx firstOpPtr (by grind) (by grind) (by grind) ip (by grind) (by grind) (by grind) ctx₀ (by grind) (by grind) (by grind) (by grind) (by grind) (by grind) (by grind) h'
    rw [this]
    simp only [Array.extract_insertIdx_zero_succ, Array.append_singleton, fromNeTo, ↓reduceDIte,
      hparent, ↓reduceIte, Array.extract_insertIdx_succ_ub, Nat.lt_add_one,
      Array.extract_of_size_lt]
    have : (blockFrom.operationList ctx (by grind) (by grind))[0]? = firstOpPtr := by grind [BlockPtr.OpChain]
    simp only [← Array.append_singleton]
    simp only [Array.append_assoc]
    rw [Array.append_right_inj]
    suffices #[firstOpPtr] ++ ((blockFrom.operationList ctx (by grind) (by grind)).erase firstOpPtr) = (blockFrom.operationList ctx (by grind) (by grind)) by grind
    grind [Array.append_singleton_erase_of_getElem?_zero]

theorem BlockPtr.operationList_Rewriter_inlineBlock_other
    {blockTo} {ip} {blockNe} {ipIn}
    (hWF : ctx.WellFormed) {ipBlock : ip.block! ctx = some blockTo}
    (hNewCtx : Rewriter.inlineBlock (block' := blockTo) ctx blockFrom ip ipIn ipBlock blockNe blockIn ctxWf = some newCtx)
    (blockIn' : block.InBounds ctx)
    (neFrom : block ≠ blockFrom) (neTo : block ≠ blockTo) :
    block.operationList newCtx (Rewriter.inlineBlock_wellFormed hNewCtx) (by
      have := Rewriter.inlineBlock_inBounds_block hNewCtx (block₀ := block); grind) =
    block.operationList ctx hWF (by grind) := by
  have fromNeTo : blockFrom ≠ blockTo := by grind [BlockPtr.OpChain]
  induction hind: (blockFrom.operationList ctx ctxWf (by grind)).size generalizing newCtx ctx
  case zero =>
    unfold Rewriter.inlineBlock at hNewCtx
    have ⟨array, hArray⟩ := ctxWf.opChain blockFrom (by grind)
    have : array = #[] := by grind
    have : (blockFrom.get! ctx).firstOp = none := by grind [BlockPtr.OpChain]
    grind
  case succ n ih =>
    have ⟨array, hArray⟩ := ctxWf.opChain blockFrom (by grind)
    simp only [BlockPtr.operationList_iff_BlockPtr_OpChain.mp hArray] at hind
    cases hFirst: (blockFrom.get ctx).firstOp; grind [BlockPtr.OpChain]
    rename_i firstOpPtr
    unfold Rewriter.inlineBlock at hNewCtx
    split at hNewCtx; grind
    simp only at hNewCtx
    split at hNewCtx; grind
    rename_i firstOpPtr heq ctx₀ h'
    have ctx₀Wf : ctx₀.WellFormed := by grind
    have ctx₁Wf : (Rewriter.detachOp ctx firstOpPtr (by grind) (by grind) (by grind)).WellFormed := by grind [Rewriter.detachOp_WellFormed]
    have ⟨arrayFrom, hArrayFrom⟩ := ctx₀Wf.opChain blockFrom (by grind)
    have hparent : (firstOpPtr.get! ctx).parent = some blockFrom := by grind
    have : (blockFrom.operationList ctx₀ (by grind) (by grind)).size = n := by
      have := @Rewriter.insertOp?_detachOp_operationList ctx blockTo firstOpPtr (by grind) (by grind) (by grind) ip (by grind) (by grind) (by grind) ctx₀ blockFrom (by grind) (by grind) (by grind) (by grind) (by grind) h'
      rw [this]
      simp [fromNeTo, hparent]
      have : firstOpPtr ∈ array := by grind [BlockPtr.OpChain]
      grind
    have ih := @ih ctx₀ (by grind) (by grind) newCtx (by grind) (by grind) (by grind) hNewCtx (by grind [Rewriter.inlineBlock_inBounds_block]) (by grind)
    rw [ih]
    have := @Rewriter.insertOp?_detachOp_operationList ctx blockTo firstOpPtr (by grind) (by grind) (by grind) ip (by grind) (by grind) (by grind) ctx₀ block (by grind) (by grind) (by grind) (by grind) (by grind) h'
    rw [this]
    grind

theorem BlockPtr.operationList_Rewriter_inlineBlock
    (hWF : ctx.WellFormed) (hblockTo : ip.block ctx ipIn = some blockTo)
    (hNewCtx : Rewriter.inlineBlock ctx blockFrom ip ipIn ipBlock blockNe blockIn ctxWf = some newCtx)
    (blockIn : block.InBounds ctx) :
  block.operationList newCtx (Rewriter.inlineBlock_wellFormed hNewCtx) (by
    have := Rewriter.inlineBlock_inBounds_block hNewCtx (block₀ := block); grind) =
  if block = blockFrom then
    #[]
  else if block = blockTo then
    let array := blockTo.operationList ctx hWF (by grind)
    let idx := ip.idxIn ctx blockTo (by grind) (by grind) (by grind)
    (array.take idx ++ (blockFrom.operationList ctx hWF (by grind)) ++ array.drop idx)
  else
    block.operationList ctx hWF (by grind) := by
  split
  · grind [BlockPtr.operationList_Rewriter_inlineBlock_from]
  · split
    · grind [BlockPtr.operationList_Rewriter_inlineBlock_to]
    · grind [BlockPtr.operationList_Rewriter_inlineBlock_other]
