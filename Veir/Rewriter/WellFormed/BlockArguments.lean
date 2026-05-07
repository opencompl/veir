module

public import Veir.IR.Basic
public import Veir.Rewriter.Basic

import all Veir.Rewriter.Basic
import Veir.IR.WellFormed
import Veir.Rewriter.GetSet

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : IRContext OpInfo}

/-! ## Rewriter.pushBlockArgument -/

theorem BlockPtr.opChain_Rewriter_pushBlockArgument
    (hWf : BlockPtr.OpChain block' ctx array) :
    BlockPtr.OpChain block' (Rewriter.pushBlockArgument ctx block type hblock) array := by
  apply BlockPtr.OpChain_unchanged (ctx := ctx) <;> grind

theorem ValuePtr.defUse_Rewriter_pushBlockArgument
    (hWf : ValuePtr.DefUse value ctx array missingUses) :
    ValuePtr.DefUse value (Rewriter.pushBlockArgument ctx block type hblock) array missingUses := by
  apply ValuePtr.DefUse.unchanged (ctx := ctx) <;> grind

theorem ValuePtr.defUse_Rewriter_pushBlockArgument_newResult (ctxFIB : ctx.FieldsInBounds) :
    ValuePtr.DefUse (block.nextArgument ctx) (Rewriter.pushBlockArgument ctx block type hblock) #[] ∅ := by
  constructor <;> grind

theorem BlockPtr.defUse_Rewriter_pushBlockArgument
    (hWf : BlockPtr.DefUse block' ctx array missingUses) :
    BlockPtr.DefUse block' (Rewriter.pushBlockArgument ctx block type hblock) array missingUses := by
  apply BlockPtr.DefUse.unchanged (ctx := ctx) <;> grind

theorem RegionPtr.blockChain_Rewriter_pushBlockArgument
    (hWf : RegionPtr.BlockChain region ctx array) :
    RegionPtr.BlockChain region (Rewriter.pushBlockArgument ctx block type hblock) array := by
  apply RegionPtr.blockChain_unchanged (ctx := ctx) hWf <;> grind

theorem IRContext.wellFormed_Rewriter_pushBlockArgument :
    ctx.WellFormed →
    (Rewriter.pushBlockArgument ctx block type hblock).WellFormed := by
  intro wf
  have ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := wf
  constructor
  case inBounds => grind
  case valueDefUseChains =>
    intros val hval
    have valCases : val.InBounds ctx ∨ val = block.nextArgument ctx := by grind
    cases valCases
    case inl valInBounds =>
      have ⟨array, harray⟩ := h₂ val (by grind)
      exists array
      grind [ValuePtr.defUse_Rewriter_pushBlockArgument]
    case inr hvalEq =>
      grind [ValuePtr.defUse_Rewriter_pushBlockArgument_newResult]
  case blockDefUseChains =>
    intros block hblock
    have ⟨array, harray⟩ := h₃ block (by grind)
    exists array
    grind [BlockPtr.defUse_Rewriter_pushBlockArgument]
  case opChain =>
    intros block' hBlock'
    have ⟨array', harray'⟩ := h₄ block' (by grind)
    exists array'
    grind [BlockPtr.opChain_Rewriter_pushBlockArgument]
  case blockChain =>
    intros region hregion
    have ⟨array, harray⟩ := h₅ region (by grind)
    exists array
    apply RegionPtr.blockChain_unchanged harray <;> grind
  case operations =>
    intros op' hop'
    apply OperationPtr.WellFormed_unchanged (ctx := ctx) <;> grind
  case blocks =>
    intros bl hbl
    have : bl.InBounds ctx := by grind
    have ⟨ha, hb, hc, hd, he⟩ := h₇ bl (by grind)
    constructor <;> grind
  case regions =>
    grind [RegionPtr.WellFormed_unchanged]

/-! ## Rewriter.initBlockArguments -/

theorem IRContext.wellFormed_Rewriter_initBlockArguments :
    ctx.WellFormed →
    (Rewriter.initBlockArguments ctx opPtr resultTypes index hop hindex).WellFormed := by
  fun_induction Rewriter.initBlockArguments <;> grind [IRContext.wellFormed_Rewriter_pushBlockArgument]
