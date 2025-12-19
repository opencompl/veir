import Veir.IR.Basic
import Veir.IR.WellFormed
import Veir.Rewriter.Basic
import Veir.Rewriter.GetSetInBounds

namespace Veir

@[grind]
def InsertPoint.Wf (insertionPoint : InsertPoint) (ctx : IRContext) (newOp : OperationPtr) :=
  match insertionPoint with
  | before op => newOp ≠ op ∧ newOp ≠ (op.get! ctx).prev ∧ op ≠ (op.get! ctx).prev
  | atEnd bl => newOp ≠ (bl.get! ctx).lastOp

/--
 - Get the index of the insertion point in the operation list of the block.
 - The index is where a new operation would be inserted.
 -/
noncomputable def InsertPoint.idxInOperationList (insertPoint : InsertPoint) (ctx : IRContext)
    (blockPtr : BlockPtr)
    (blockInBounds : blockPtr.InBounds ctx := by grind)
    (ctxWf : ctx.WellFormed := by grind) : Nat :=
  match insertPoint with
  | before op =>
    let opList := BlockPtr.operationList blockPtr ctx (by grind) blockInBounds
    opList.idxOf op
  | atEnd b =>
    (BlockPtr.operationList blockPtr ctx (by grind) blockInBounds).size

@[simp, grind =]
theorem InsertPoint.idxInOperationList_Before :
    InsertPoint.idxInOperationList (before op) ctx blockPtr blockInBounds ctxWf =
    (BlockPtr.operationList blockPtr ctx ctxWf blockInBounds).idxOf op := by
  simp [InsertPoint.idxInOperationList]

@[simp, grind =]
theorem InsertPoint.idxInOperationList_AtEnd :
    InsertPoint.idxInOperationList (atEnd blockPtr) ctx blockPtr blockInBounds ctxWf =
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
      InsertPoint.idxInOperationList (before op) ctx blockPtr blockInBounds ctxWf]? = some op := by
  simp only [InsertPoint.idxInOperationList]
  rw [Array.getElem?_idxOf]
  suffices _ : op ∈ blockPtr.operationList ctx ctxWf blockInBounds by grind
  have := @BlockPtr.operationListWF ctx blockPtr blockInBounds ctxWf
  have := this.allOpsInChain
  grind

theorem InsertPoint.idxInOperationList_InsertPoint_prev_none
    (ipInBounds : ip.InBounds ctx) :
    InsertPoint.block ip ctx ipInBounds = some blockPtr →
    (InsertPoint.prev! ip ctx = none ↔
    InsertPoint.idxInOperationList ip ctx blockPtr blockInBounds ctxWf = 0) := by
  have ⟨array, harray⟩ := ctxWf.opChain blockPtr blockInBounds
  simp (disch := grind) only [BlockPtr.operationList_iff_BlockPtr_OpChain] at harray
  have blockWF := @BlockPtr.operationListWF ctx blockPtr (by grind) (by grind)
  intro hblock
  cases ip
  case before op =>
    simp_all only [idxInOperationList_Before, InsertPoint.block, InsertPoint.prev!]
    grind [BlockPtr.OpChain]
  case atEnd bl =>
    simp_all only [InsertPoint.block, InsertPoint.prev!, InsertPoint.idxInOperationList]
    grind [BlockPtr.OpChain, Array.size_eq_zero_iff]

theorem InsertPoint.next_idxInOperationList ctxWf ip blockInBounds :
    BlockPtr.OpChain blockPtr ctx array →
    array[InsertPoint.idxInOperationList ip ctx blockPtr blockInBounds ctxWf]? = ip.next := by
  sorry

theorem InsertPoint.next_ne_firstOp (hWF : ctx.WellFormed) (ipInBounds : ip.InBounds ctx) :
    (BlockPtr.get blockPtr ctx blockInBounds).firstOp = some firstOp →
    InsertPoint.prev! ip ctx ≠ none →
    InsertPoint.next ip ≠ some firstOp := by
  intro hfirst hprev
  have ⟨array, harray⟩ := hWF.opChain blockPtr blockInBounds
  have := InsertPoint.next_idxInOperationList hWF ip blockInBounds harray
  cases ip <;> grind [InsertPoint.prev!, InsertPoint.next, BlockPtr.OpChain]


theorem InsertPoint.prev_idxInOperationList :
    let idx := InsertPoint.idxInOperationList ip ctx blockPtr blockInBounds ctxWf
    BlockPtr.OpChain blockPtr ctx array →
    idx > 0 →
    ip.prev! ctx = some array[idx - 1]! := by
  sorry

@[grind .]
theorem InsertPoint.idxInOperationList_Before_lt_size :
    InsertPoint.idxInOperationList (before op) ctx blockPtr blockInBounds ctxWf <
    (BlockPtr.operationList blockPtr ctx ctxWf blockInBounds).size := by
  sorry

unseal Rewriter.insertOp? in
@[grind! <=]
theorem OperationPtr.getParent_insertOp?_previousCtx
    (heq : Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx) :
    (newOp.get ctx).parent = none := by
  simp only [Rewriter.insertOp?, OperationPtr.linkBetweenWithParent] at heq
  split at heq <;> grind [setParentWithCheck]

unseal Rewriter.insertOp? in
theorem Rewriter.isSome_parent_insertOp?_before
    (heq : Rewriter.insertOp? ctx newOp (.before op) h₁ h₂ h₃ = some newCtx) :
    (op.get ctx).parent.isSome := by
  simp only [Rewriter.insertOp?, OperationPtr.linkBetweenWithParent] at heq
  split at heq <;> grind

@[grind .]
theorem InsertPoint.wf_insertOp?_isSome (hWF : ctx.WellFormed) {ipInBounds : ip.InBounds ctx} :
    Rewriter.insertOp? ctx newOp ip newOpIn insIn ctxInBounds = some ctx' →
    ip.block ctx ipInBounds = some blockPtr →
    ip.Wf ctx newOp := by
  intro ctx' hipBlock
  have : (newOp.get ctx).parent = none := by grind
  have ⟨array, arrayWF⟩ := hWF.opChain blockPtr (by grind)
  simp only [InsertPoint.Wf]
  cases ip
  case before existingOp =>
    have : (existingOp.get ctx).parent = some blockPtr := by grind
    simp only
    constructor
    · grind
    · cases hprev : (existingOp.get! ctx).prev
      case none => grind
      case some prev =>
        have : (prev.get! ctx).parent = some blockPtr := by
          apply OperationPtr.getParent_prev_eq (opPtr := existingOp) (array := array) <;> grind
        grind [BlockPtr.OpChain_prev_ne]
  case atEnd bl =>
    simp only
    simp [InsertPoint.block] at hipBlock
    subst bl
    rw [BlockPtr.get!_eq_get (by grind)]
    cases hlast: (blockPtr.get ctx (by grind)).lastOp
    case none => grind
    case some lastOp =>
      have : (lastOp.get ctx (by grind)).parent = some blockPtr := by grind [BlockPtr.OpChain]
      grind

unseal Rewriter.insertOp? in
theorem BlockPtr.operationChainWellFormed_Rewriter_insertOp?_other
    (hol : BlockPtr.operationList blockPtr ctx ctxWellFormed blockInBounds = array)
    (hctx' : Rewriter.insertOp? ctx newOp ip newOpIn insIn ctxInBounds = some ctx')
    (ipParent : InsertPoint.block! ip ctx ≠ some blockPtr) :
      blockPtr.OpChain ctx' array := by
  have ipWf : ip.Wf ctx newOp := by rcases ip <;> grind [Rewriter.insertOp?] -- TODO: missing lemmas?
  apply BlockPtr.OpChain_unchanged (ctx := ctx) <;> try grind
  · intros opPtr opInBounds opParent
    simp only [OperationPtr.parent!_insertOp? hctx']
    simp only [OperationPtr.prev!_insertOp? hctx']
    simp only [OperationPtr.next!_insertOp? hctx']
    constructor
    · grind
    · constructor
      · grind
      · constructor
        · split
          · simp_all [InsertPoint.block!, InsertPoint.next]
            grind [BlockPtr.OpChain]
          · grind
        · split
          · suffices (opPtr.get! ctx).parent = ip.block! ctx by grind
            simp_all [InsertPoint.block!, InsertPoint.prev!]
            cases ip
            · rename_i op' _
              simp_all only
              cases hop'parent : (op'.get ctx).parent
              · grind [Rewriter.isSome_parent_insertOp?_before]
              · rename_i parent'
                have ⟨array', harray'⟩ := ctxWellFormed.opChain parent' (by grind)
                have : op' ∈ array' := by grind [IRContext.WellFormed, BlockPtr.OpChain]
                have ⟨i, hi⟩ := Array.getElem?_of_mem this
                have := harray'.prev i (by grind [IRContext.WellFormed, BlockPtr.OpChain]) (by grind)
                grind [IRContext.WellFormed, BlockPtr.OpChain]
            · simp_all only
              grind [IRContext.WellFormed, BlockPtr.OpChain]
          · grind

theorem BlockPtr.operationChainWellFormed_Rewriter_insertOp?_self
    (hWf : BlockPtr.operationList blockPtr ctx ctxWellFormed blockInBounds = array)
    (hctx' : Rewriter.insertOp? ctx newOp ip newOpIn insIn ctxInBounds = some ctx')
    (ipParent : InsertPoint.block ip ctx ipInBounds = some blockPtr) :
      blockPtr.OpChain ctx'
        (array.insertIdx (ip.idxInOperationList ctx blockPtr blockInBounds ctxWellFormed)
          newOp (by grind [InsertPoint.idxInOperationList_inBounds])) := by
  have ipWf := InsertPoint.wf_insertOp?_isSome ctxWellFormed hctx' ipParent
  have chainWf := ctxWellFormed.opChain
  have : (newOp.get ctx (by grind)).parent = none := by grind
  have hOCWF := @BlockPtr.operationListWF ctx blockPtr (by grind) (by grind)
  simp only [hWf] at hOCWF
  simp only [←InsertPoint.block!_eq_block] at ipParent
  constructor
  case blockInBounds => grind
  case opParent =>
    intros op hop
    simp [Array.mem_insertIdx] at hop
    grind [BlockPtr.OpChain]
  case last =>
    simp only [Array.size_insertIdx, Nat.add_one_sub_one, Nat.lt_add_one, getElem?_pos]
    simp [BlockPtr.lastOp!_insertOp? hctx']
    simp_all [InsertPoint.block!, InsertPoint.next]
    cases hip: ip
    case before existingOp =>
      subst ip
      simp only [InsertPoint.idxInOperationList_Before]
      rw [Array.getElem_insertIdx_of_gt] <;> grind [BlockPtr.OpChain]
    case atEnd => grind [InsertPoint.idxInOperationList]
  case prevFirst =>
    intros firstOp hFirstOp
    simp only [BlockPtr.firstOp!_insertOp? hctx'] at hFirstOp
    simp only [ipParent, true_and] at hFirstOp
    split at hFirstOp
    case isTrue =>
      simp only [Option.some.injEq] at hFirstOp
      subst firstOp
      simp only [OperationPtr.prev!_insertOp? hctx', ↓reduceIte]
      simp_all only [InsertPoint.Wf, InsertPoint.next]
      grind
    case isFalse ipprev =>
      simp only [OperationPtr.prev!_insertOp? hctx']
      grind [InsertPoint.next_ne_firstOp, BlockPtr.OpChain]
  case allOpsInChain =>
    intros op opInBounds opParent
    simp only [←OperationPtr.get!_eq_get, OperationPtr.parent!_insertOp? hctx'] at opParent
    simp [Array.mem_insertIdx]
    split at opParent
    · grind
    · grind [BlockPtr.OpChain]
  case arrayInBounds =>
    simp only [Array.mem_insertIdx]
    rintro op (hold | hnew)
    · grind
    · have : op.InBounds ctx := by grind [BlockPtr.OpChain]
      grind
  case first =>
    simp only [BlockPtr.firstOp!_insertOp? hctx']
    simp only [ipParent, true_and, Array.size_insertIdx, Nat.zero_lt_succ, getElem?_pos]
    have := InsertPoint.idxInOperationList_InsertPoint_prev_none ipInBounds (ctxWf := ctxWellFormed) (blockPtr := blockPtr) (blockInBounds := by grind)
    split
    case isTrue => grind
    case isFalse h =>
      simp only [h] at this
      have := InsertPoint.idxInOperationList_InsertPoint_prev_none ipInBounds (ctxWf := ctxWellFormed) (blockPtr := blockPtr) (blockInBounds := by grind)
      rw [Array.getElem_insertIdx_of_lt]
      · grind [BlockPtr.OpChain]
      · grind
  case prev =>
    simp only [gt_iff_lt, Array.size_insertIdx]
    intros i h₁ h₂
    let idx := ip.idxInOperationList ctx blockPtr blockInBounds ctxWellFormed
    simp [OperationPtr.prev!_insertOp? hctx']
    have idxInBounds := @InsertPoint.idxInOperationList_inBounds ip ctx blockPtr (by grind) (by grind)
    simp only [hWf] at idxInBounds
    by_cases hi : i < idx
    · simp (disch := grind) only [Array.getElem_insertIdx_of_lt]
      have : array[i]? ≠ some newOp := by grind [BlockPtr.OpChain]
      simp only [Array.getElem_eq_iff, this, ↓reduceIte]
      have : ip.next = array[idx]? := by grind [InsertPoint.next_idxInOperationList]
      suffices ip.next ≠ some array[i] by grind [BlockPtr.OpChain]
      grind [BlockPtr.OpChain_array_injective]
    by_cases hi' : i = idx
    · subst i idx
      simp only [Array.getElem_insertIdx_self, ↓reduceIte]
      simp (disch := grind) [Array.getElem_insertIdx_of_lt]
      simp_all only [InsertPoint.Wf, InsertPoint.next]
      have := @InsertPoint.prev_idxInOperationList
      grind
    by_cases hi'' : i = idx + 1
    · simp (disch := grind) only [Array.getElem_insertIdx_of_gt]
      have : idx = i - 1 := by grind
      have : array[i - 1] ≠ newOp := by grind [BlockPtr.OpChain]
      simp only [this, ↓reduceIte]
      have := InsertPoint.next_idxInOperationList ctxWellFormed ip (by grind) hOCWF
      grind
    · simp (disch := grind) only [Array.getElem_insertIdx_of_gt]
      have : array[i - 1] ≠ newOp := by grind [BlockPtr.OpChain]
      simp only [this, ↓reduceIte]
      have := InsertPoint.next_idxInOperationList ctxWellFormed ip (by grind) hOCWF
      suffices ip.next ≠ some array[i - 1] by grind [BlockPtr.OpChain]
      grind [BlockPtr.OpChain_array_injective]
  case next =>
    simp only [Array.size_insertIdx]
    intros i hi
    let idx := ip.idxInOperationList ctx blockPtr blockInBounds ctxWellFormed
    simp only [OperationPtr.next!_insertOp? hctx']
    have idxInBounds := @InsertPoint.idxInOperationList_inBounds ip ctx blockPtr (by grind) (by grind)
    simp only [hWf] at idxInBounds
    by_cases hi' : i = idx
    · subst i
      rw [Array.getElem_insertIdx_self]
      simp only [↓reduceIte]
      have : some newOp ≠ ip.prev! ctx := by simp_all [InsertPoint.Wf, InsertPoint.prev!]; grind
      grind [InsertPoint.next_idxInOperationList]
    by_cases hi'' : i + 1 = idx
    · simp (disch := grind) only [Array.getElem_insertIdx_of_lt]
      have : idx = i + 1 := by grind
      have : array[i] ≠ newOp := by grind [BlockPtr.OpChain]
      simp [this, ↓reduceIte]
      have := @InsertPoint.prev_idxInOperationList
      grind
    by_cases hi : i > idx
    · simp (disch := grind) only [Array.getElem_insertIdx_of_gt]
      have : array[i-1]? ≠ some newOp := by grind [BlockPtr.OpChain]
      simp only [Array.getElem_eq_iff, this, ↓reduceIte]
      suffices ip.prev! ctx ≠ some array[i - 1] by grind [BlockPtr.OpChain]
      by_cases idx = 0
      · rcases ip
        · have := hOCWF.first
          grind [@hOCWF.prevFirst array[0] (by grind), InsertPoint.prev!]
        · grind
      rcases ip with ⟨op⟩ | _
      · simp [InsertPoint.prev!]
        have : (array[idx].get! ctx).prev = some array[idx - 1] := by
          apply BlockPtr.OpChain.prev hOCWF; grind
        grind [BlockPtr.OpChain_array_injective]
      · grind [InsertPoint.next_idxInOperationList]
    · have : i < idx - 1 := by cutsat
      simp (disch := grind) only [Array.getElem_insertIdx_of_lt]
      have : array[i]? ≠ some newOp := by grind [BlockPtr.OpChain]
      simp only [Array.getElem_eq_iff, this, ↓reduceIte]
      have : ip.prev! ctx = some array[idx-1]! := by grind [InsertPoint.prev_idxInOperationList]
      suffices ip.prev! ctx ≠ some array[i] by grind [BlockPtr.OpChain]
      grind [BlockPtr.OpChain_array_injective]

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
  · simp only [←BlockPtr.operationList_iff_BlockPtr_OpChain]
    grind [BlockPtr.operationChainWellFormed_Rewriter_insertOp?_self]
  · simp only [←BlockPtr.operationList_iff_BlockPtr_OpChain]
    grind [BlockPtr.operationChainWellFormed_Rewriter_insertOp?_other]

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
  case valueDefUseChains =>
    intros val hval
    have ⟨array, harray⟩ := h₂ val (by grind)
    exists array
    apply ValuePtr.DefUse.unchanged (ctx := ctx) <;> grind [ValuePtr.getFirstUse]
  case blockDefUseChains =>
    intros block hblock
    have ⟨array, harray⟩ := h₃ block (by grind)
    exists array
    apply BlockPtr.DefUse_unchanged (ctx := ctx) <;>
      grind
  case opChain =>
    intros block hblock
    have ⟨array, harray⟩ := h₄ block (by grind)
    by_cases some block = ip.block ctx insIn
    · exists (array.insertIdx (ip.idxInOperationList ctx block (by grind) (by grind)) newOp (by grind [InsertPoint.idxInOperationList_inBounds]))
      grind [BlockPtr.operationChainWellFormed_Rewriter_insertOp?_self]
    · exists array
      grind [BlockPtr.operationChainWellFormed_Rewriter_insertOp?_other]
  case blockChain =>
    intros region hregion
    have ⟨array, harray⟩ := h₅ region (by grind)
    exists array
    apply RegionPtr.BlockChainWellFormed_unchanged harray <;> grind
  case operations =>
    intros op hop
    have : op.InBounds ctx := by grind
    have ⟨ha, hb, hc, hd, he, hf⟩ := h₆ op this
    -- Add the correct lemmas so we don't manually unfold definitions here
    sorry
  case blocks =>
    intros bl hbl
    have : bl.InBounds ctx := by grind
    have ⟨ha, hb, hc⟩ := h₇ bl this
    constructor <;> sorry -- Missing lemmas here
  case regions =>
    intros rg hrg
    have : rg.InBounds ctx := by grind
    have ⟨ha, hb⟩ := h₈ rg this
    sorry

theorem Rewriter.detachOp_WellFormed (ctx : IRContext) (wf : ctx.WellFormed)
    (hctx : ctx.FieldsInBounds) (op : OperationPtr)
    (hIn : op.InBounds ctx)
    (hasParent : (op.get ctx hIn).parent.isSome)
    (newCtx : IRContext) :
    Rewriter.detachOp ctx op hctx hIn hasParent = newCtx →
    newCtx.WellFormed := by
  sorry

theorem BlockPtr.operationList_Rewriter_detachOp
    (hWf : BlockPtr.operationList blockPtr ctx ctxWellFormed blockInBounds = array) :
      BlockPtr.operationList blockPtr (Rewriter.detachOp ctx op hctx hIn hasParent) ctxWellFormed' blockInBounds' =
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

end Veir
