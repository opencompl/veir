module

public import Veir.Rewriter.WellFormed.BlockConstruction
public import Veir.IR.Basic
public import Veir.Rewriter.Basic

import all Veir.Rewriter.Basic
import Veir.IR.WellFormed
import Veir.Rewriter.GetSet

public section

namespace Veir
namespace Construction

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : IRContext OpInfo}

attribute [local grind] Rewriter.pushBlockArgument

/-! Construction of block arguments. -/

theorem BlockPtr.opChain_Rewriter_pushBlockArgument
    (hWf : BlockPtr.OpChain block' ctx array) :
    BlockPtr.OpChain block' (Rewriter.pushBlockArgument ctx block type hblock) array := by
  apply BlockPtr.OpChain_unchanged (ctx := ctx) <;> grind

theorem ValuePtr.defUse_Rewriter_pushBlockArgument
    (hWf : ValuePtr.DefUse value ctx array missingUses) :
    ValuePtr.DefUse value (Rewriter.pushBlockArgument ctx block type hblock) array missingUses := by
  apply ValuePtr.DefUse.unchanged (ctx := ctx) <;> grind [BlockArgumentPtr.inBounds_def]

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


theorem pushBlockArgument_fieldsInBounds (hctx : ctx.FieldsInBounds) :
    (Rewriter.pushBlockArgument ctx block type hblock).FieldsInBounds := by
  unfold Rewriter.pushBlockArgument
  apply BlockPtr.pushArgument_fieldsInBounds
  · constructor <;> grind
  · exact hctx

theorem pushBlockArgument_constructionWellFormed
    (wf : BlockConstructionWellFormed ctx block ∅ ∅) :
    BlockConstructionWellFormed (Rewriter.pushBlockArgument ctx block type hblock) block ∅ ∅ := by
  have ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := wf
  have hfib := pushBlockArgument_fieldsInBounds (block := block) (type := type) (hblock := hblock) h₁
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · grind
  · intros val hval
    have valCases : val.InBounds ctx ∨ val = block.nextArgument ctx := by grind
    cases valCases
    case inl valInBounds =>
      have ⟨array, harray⟩ := h₂ val (by grind)
      exists array
      grind [ValuePtr.defUse_Rewriter_pushBlockArgument]
    case inr hvalEq =>
      grind [ValuePtr.defUse_Rewriter_pushBlockArgument_newResult]
  · intros block' hblock'
    have ⟨array, harray⟩ := h₃ block' (by grind)
    exists array
    grind [BlockPtr.defUse_Rewriter_pushBlockArgument]
  · intros block' hBlock'
    have ⟨array', harray'⟩ := h₄ block' (by grind)
    exists array'
    grind [BlockPtr.opChain_Rewriter_pushBlockArgument]
  · intros region hregion
    have ⟨array, harray⟩ := h₅ region (by grind)
    exists array
    apply RegionPtr.blockChain_unchanged harray <;> grind
  · intros op' hop'
    apply OperationPtr.WellFormed_unchanged (ctx := ctx) <;> grind
  · intros bl hbl
    have ⟨ha, hb, hc, hd, he, hf⟩ := h₇ bl (by grind)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> grind
  · grind [RegionPtr.WellFormed_unchanged]

end Construction
variable {OpInfo : Type} [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo]

theorem Rewriter.pushBlockArgumentAt_constructionWellFormed {blockPtr : Sim.BlockPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {index type h₁ h₂ h₃}
    (wf : BlockConstructionWellFormed ctx.spec blockPtr.spec ∅ ∅)
    (heq : pushBlockArgumentAt blockPtr ctx index type h₁ h₂ h₃ = some ctx') :
    BlockConstructionWellFormed ctx'.spec blockPtr.spec ∅ ∅ := by
  rw [pushBlockArgumentAt_spec heq]
  exact Construction.pushBlockArgument_constructionWellFormed wf

theorem Rewriter.initBlockArgumentsLoop_constructionWellFormed {blockPtr : Sim.BlockPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {types index h₁ h₂ h₃ h₄}
    (wf : BlockConstructionWellFormed ctx.spec blockPtr.spec ∅ ∅)
    (heq : initBlockArgumentsLoop blockPtr ctx types index h₁ h₂ h₃ h₄ = some ctx') :
    BlockConstructionWellFormed ctx'.spec blockPtr.spec ∅ ∅ := by
  simp only [initBlockArgumentsLoop_def] at heq
  fun_induction initBlockArgumentsLoopSim
  · cases Option.some.inj heq
    exact wf
  · simp at heq
  · rename_i hpush ih
    exact ih (pushBlockArgumentAt_constructionWellFormed wf hpush) heq

theorem Rewriter.initBlockArguments_constructionWellFormed {blockPtr : Sim.BlockPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {types index h₁ h₂ h₃ h₄}
    (wf : BlockConstructionWellFormed ctx.spec blockPtr.spec ∅ ∅)
    (heq : initBlockArguments blockPtr ctx types index h₁ h₂ h₃ h₄ = some ctx') :
    BlockConstructionWellFormed ctx'.spec blockPtr.spec ∅ ∅ := by
  simp only [initBlockArguments_def, initBlockArgumentsSim] at heq
  exact initBlockArgumentsLoop_constructionWellFormed wf heq

theorem Rewriter.initBlockArguments_numArguments {blockPtr : Sim.BlockPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {types index h₁ h₂ h₃ h₄}
    (heq : initBlockArguments blockPtr ctx types index h₁ h₂ h₃ h₄ = some ctx')
    (hindex : index.toNat ≤ types.size) :
    blockPtr.spec.getNumArguments! ctx'.spec = types.size := by
  simp only [initBlockArguments_def, initBlockArgumentsSim, initBlockArgumentsLoop_def] at heq
  fun_induction initBlockArgumentsLoopSim <;>
    grind [Array.usize_toUInt64_toNat, UInt64.le_iff_toNat_le, UInt64.toNat_add, UInt64.toNat_mod_size]

theorem Rewriter.initBlockArguments_preserves_capArguments (ptr : Veir.BlockPtr)
    {blockPtr : Sim.BlockPtr} {ctx ctx' : Sim.IRContext OpInfo} {types index h₁ h₂ h₃ h₄}
    (heq : initBlockArguments blockPtr ctx types index h₁ h₂ h₃ h₄ = some ctx') :
    (ptr.get! ctx'.spec).capArguments = (ptr.get! ctx.spec).capArguments := by
  simp only [initBlockArguments_def, initBlockArgumentsSim, initBlockArgumentsLoop_def] at heq
  fun_induction initBlockArgumentsLoopSim
  · grind
  · simp at heq
  · rename_i hpush ih
    rw [ih heq, Rewriter.pushBlockArgumentAt_spec hpush]
    grind [Rewriter.pushBlockArgument]

theorem Rewriter.initBlockArguments_preserves_parent (ptr : Veir.BlockPtr)
    {blockPtr : Sim.BlockPtr} {ctx ctx' : Sim.IRContext OpInfo} {types index h₁ h₂ h₃ h₄}
    (heq : initBlockArguments blockPtr ctx types index h₁ h₂ h₃ h₄ = some ctx') :
    (ptr.get! ctx'.spec).parent = (ptr.get! ctx.spec).parent := by
  simp only [initBlockArguments_def, initBlockArgumentsSim, initBlockArgumentsLoop_def] at heq
  fun_induction initBlockArgumentsLoopSim
  · grind
  · simp at heq
  · rename_i hpush ih
    rw [ih heq, Rewriter.pushBlockArgumentAt_spec hpush]
    grind [Rewriter.pushBlockArgument]

/-- Filling the preallocated argument array restores full well-formedness. -/
theorem Rewriter.initBlockArguments_wellFormed {blockPtr : Sim.BlockPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {types index h₁ h₂ h₃ h₄}
    (wf : BlockConstructionWellFormed ctx.spec blockPtr.spec ∅ ∅)
    (hcapacity : (blockPtr.spec.get! ctx.spec).capArguments = types.size)
    (hindex : index.toNat ≤ types.size)
    (heq : initBlockArguments blockPtr ctx types index h₁ h₂ h₃ h₄ = some ctx') :
    ctx'.spec.WellFormed := by
  apply IRContext.BlockConstructionWellFormed.to_wellFormed
    (initBlockArguments_constructionWellFormed wf heq)
  rw [initBlockArguments_preserves_capArguments blockPtr.spec heq,
    initBlockArguments_numArguments heq hindex]
  exact hcapacity

end Veir
