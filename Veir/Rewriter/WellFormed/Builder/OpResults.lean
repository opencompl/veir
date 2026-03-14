import Veir.IR.Basic
import Veir.IR.WellFormed
import Veir.Rewriter.Basic
import Veir.Rewriter.GetSetInBounds

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : IRContext OpInfo}

/-! ## Rewriter.pushResult -/

theorem BlockPtr.opChain_Rewriter_pushResult
    (hWf : BlockPtr.OpChain block ctx array) :
    BlockPtr.OpChain block (Rewriter.pushResult ctx op type hop) array := by
  apply BlockPtr.OpChain_unchanged (ctx := ctx) <;> grind

theorem ValuePtr.defUse_Rewriter_pushResult
    (hWf : ValuePtr.DefUse value ctx array missingUses) :
    ValuePtr.DefUse value (Rewriter.pushResult ctx op type hop) array missingUses := by
  apply ValuePtr.DefUse.unchanged (ctx := ctx) <;> grind

theorem ValuePtr.defUse_Rewriter_pushResult_newResult (ctxFIB : ctx.FieldsInBounds) :
    ValuePtr.DefUse (op.nextResult ctx) (Rewriter.pushResult ctx op type hop) #[] ∅ := by
  constructor <;> grind

theorem BlockPtr.defUse_Rewriter_pushResult
    (hWf : BlockPtr.DefUse block ctx array missingUses) :
    BlockPtr.DefUse block (Rewriter.pushResult ctx op type hop) array missingUses := by
  apply BlockPtr.DefUse.unchanged (ctx := ctx) <;> grind

theorem RegionPtr.blockChain_Rewriter_pushResult
    (hWf : RegionPtr.BlockChain region ctx array) :
    RegionPtr.BlockChain region (Rewriter.pushResult ctx op type hop) array := by
  apply RegionPtr.blockChain_unchanged (ctx := ctx) hWf <;> grind

theorem IRContext.wellFormed_Rewriter_pushResult :
    ctx.WellFormed →
    (Rewriter.pushResult ctx op type hop).WellFormed := by
  intro wf
  have ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := wf
  constructor
  case inBounds => grind
  case valueDefUseChains =>
    intros val hval
    have valCases : val.InBounds ctx ∨ val = op.nextResult ctx := by grind
    cases valCases
    case inl valInBounds =>
      have ⟨array, harray⟩ := h₂ val (by grind)
      exists array
      grind [ValuePtr.defUse_Rewriter_pushResult]
    case inr hvalEq =>
      grind [ValuePtr.defUse_Rewriter_pushResult_newResult]
  case blockDefUseChains =>
    intros block hblock
    have ⟨array, harray⟩ := h₃ block (by grind)
    exists array
    grind [BlockPtr.defUse_Rewriter_pushResult]
  case opChain =>
    intros block' hBlock'
    have ⟨array', harray'⟩ := h₄ block' (by grind)
    exists array'
    grind [BlockPtr.opChain_Rewriter_pushResult]
  case blockChain =>
    intros region hregion
    have ⟨array, harray⟩ := h₅ region (by grind)
    exists array
    apply RegionPtr.blockChain_unchanged harray <;> grind
  case operations =>
    intros op' hop'
    have : op'.InBounds ctx := by grind
    have ⟨ha, hb, hc, hd, he, hf, hg, hh⟩ := h₆ op' this
    constructor <;> grind
  case blocks =>
    intros bl hbl
    have : bl.InBounds ctx := by grind
    grind [Block.WellFormed_unchanged]
  case regions =>
    grind [Region.WellFormed_unchanged]

/-! ## Rewriter.initOpResults -/

theorem IRContext.wellFormed_Rewriter_initOpResults :
    ctx.WellFormed →
    (Rewriter.initOpResults ctx opPtr resultTypes index hop hindex).WellFormed := by
  fun_induction Rewriter.initOpResults <;> grind [IRContext.wellFormed_Rewriter_pushResult]
