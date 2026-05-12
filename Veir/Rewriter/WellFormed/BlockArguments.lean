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

/-! ## Rewriter.setBlockArguments -/

theorem IRContext.fieldsInBounds_Rewriter_setBlockArguments (ctxWf : ctx.WellFormed)
    (noUses : ∀ blockArg ∈ block.getArguments! ctx, ¬ blockArg.hasUses! ctx) :
    (Rewriter.setBlockArguments ctx block type hblock).FieldsInBounds := by
  constructor
  · intro op opInBounds
    have : Operation.FieldsInBounds op ctx (by grind) := by grind
    have ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := this
    constructor
    case results_inBounds => intros; constructor <;> grind [Option.maybe_def]
    case blockOperands_inBounds => intros; constructor <;> grind [Option.maybe_def]
    case operands_inBounds =>
      intros; constructor <;>
        grind (gen := 20) [BlockArgumentPtr.inBounds_def, ValuePtr.hasUses!_def, Option.maybe_def,
          BlockArgumentPtr.block_of_mem_getArguments!]
    all_goals try grind [Option.maybe_def]
  · intros; constructor <;> grind [BlockArgument.FieldsInBounds, Option.maybe_def]
  · intros; constructor <;> grind [Option.maybe_def]

theorem BlockPtr.opChain_Rewriter_setBlockArguments
    (hWf : BlockPtr.OpChain block' ctx array) :
    BlockPtr.OpChain block' (Rewriter.setBlockArguments ctx block type hblock) array := by
  apply BlockPtr.OpChain_unchanged (ctx := ctx) <;> grind

theorem ValuePtr.defUse_Rewriter_setBlockArguments_preserves
    (hWf : ValuePtr.DefUse value ctx array missingUses) :
    value ∉ block.getArguments! (Rewriter.setBlockArguments ctx block type hblock) →
    value.InBounds (Rewriter.setBlockArguments ctx block type hblock) →
    ValuePtr.DefUse value (Rewriter.setBlockArguments ctx block type hblock) array missingUses := by
  intros
  apply ValuePtr.DefUse.unchanged (ctx := ctx) <;>
    grind [BlockArgumentPtr.block_of_mem_getArguments!]

theorem ValuePtr.defUse_Rewriter_setBlockArguments_new (ctxWf : ctx.WellFormed)
    (noUses : ∀ blockArg ∈ block.getArguments! ctx, ¬ blockArg.hasUses! ctx) :
    value ∈ block.getArguments! (Rewriter.setBlockArguments ctx block type hblock) →
    ValuePtr.DefUse value (Rewriter.setBlockArguments ctx block type hblock) #[] ∅ := by
  intros
  have : (Rewriter.setBlockArguments ctx block type hblock).FieldsInBounds :=
    IRContext.fieldsInBounds_Rewriter_setBlockArguments ctxWf noUses
  constructor <;> grind [BlockArgumentPtr.block_of_mem_getArguments!,
      BlockArgumentPtr.exists_blockArgument_of_mem_getArguments!]

theorem BlockPtr.defUse_Rewriter_setBlockArguments
    (hWf : BlockPtr.DefUse block' ctx array missingUses) :
    BlockPtr.DefUse block' (Rewriter.setBlockArguments ctx block type hblock) array missingUses := by
  apply BlockPtr.DefUse.unchanged (ctx := ctx) <;> grind

theorem RegionPtr.blockChain_Rewriter_setBlockArguments
    (hWf : RegionPtr.BlockChain region ctx array) :
    RegionPtr.BlockChain region (Rewriter.setBlockArguments ctx block type hblock) array := by
  apply RegionPtr.blockChain_unchanged (ctx := ctx) hWf <;> grind

theorem IRContext.wellFormed_Rewriter_setBlockArguments
    (noUses : ∀ blockArg ∈ block.getArguments! ctx, ¬ blockArg.hasUses! ctx)
    (ctxWf : ctx.WellFormed) :
    (Rewriter.setBlockArguments ctx block type hblock).WellFormed := by
  have ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := ctxWf
  have : (Rewriter.setBlockArguments ctx block type hblock).FieldsInBounds :=
    by grind [IRContext.fieldsInBounds_Rewriter_setBlockArguments]
  constructor
  case inBounds => grind
  case valueDefUseChains =>
    intros value hvalue
    cases hInArgs : decide (value ∈ block.getArguments! (Rewriter.setBlockArguments ctx block type hblock))
    · have ⟨array, harray⟩ := h₂ value (by grind [BlockArgumentPtr.block_of_mem_getArguments!])
      exists array
      grind [ValuePtr.defUse_Rewriter_setBlockArguments_preserves]
    · exists #[]
      grind [ValuePtr.defUse_Rewriter_setBlockArguments_new]
  case blockDefUseChains =>
    intros block hblock
    have ⟨array, harray⟩ := h₃ block (by grind)
    exists array
    grind [BlockPtr.defUse_Rewriter_setBlockArguments]
  case opChain =>
    intros block' hBlock'
    have ⟨array', harray'⟩ := h₄ block' (by grind)
    exists array'
    grind [BlockPtr.opChain_Rewriter_setBlockArguments]
  case blockChain =>
    intros region hregion
    have ⟨array, harray⟩ := h₅ region (by grind)
    exists array
    apply RegionPtr.blockChain_unchanged harray <;> grind
  case operations =>
    intros op' hop'
    apply OperationPtr.WellFormed_unchanged (ctx := ctx) <;>
      grind
  case blocks =>
    intros bl hbl
    have : bl.InBounds ctx := by grind
    have ⟨ha, hb, hc, hd, he⟩ := h₇ bl (by grind)
    constructor <;> grind
  case regions =>
    grind [RegionPtr.WellFormed_unchanged]
