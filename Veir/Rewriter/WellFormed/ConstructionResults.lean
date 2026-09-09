module

public import Veir.Rewriter.WellFormed.Construction
public import Veir.IR.Basic
public import Veir.Rewriter.Basic

import all Veir.Rewriter.Basic
import Veir.IR.WellFormed
import Veir.Rewriter.Basic
import Veir.Rewriter.GetSet

public section

namespace Veir
namespace Construction

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

theorem pushResult_wellFormed :
    ConstructionWellFormed ctx op ∅ ∅ →
    ConstructionWellFormed (Rewriter.pushResult ctx op type hop) op ∅ ∅ := by
  intro wf
  have ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := wf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · grind
  ·
    intros val hval
    have valCases : val.InBounds ctx ∨ val = op.nextResult ctx := by grind
    cases valCases
    case inl valInBounds =>
      have ⟨array, harray⟩ := h₂ val (by grind)
      exists array
      grind [ValuePtr.defUse_Rewriter_pushResult]
    case inr hvalEq =>
      grind [ValuePtr.defUse_Rewriter_pushResult_newResult]
  ·
    intros block hblock
    have ⟨array, harray⟩ := h₃ block (by grind)
    exists array
    grind [BlockPtr.defUse_Rewriter_pushResult]
  ·
    intros block' hBlock'
    have ⟨array', harray'⟩ := h₄ block' (by grind)
    exists array'
    grind [BlockPtr.opChain_Rewriter_pushResult]
  ·
    intros region hregion
    have ⟨array, harray⟩ := h₅ region (by grind)
    exists array
    apply RegionPtr.blockChain_unchanged harray <;> grind
  ·
    intros op' hop'
    have : op'.InBounds ctx := by grind
    have ⟨ha, hb, hc, hd, he, hf, hg, hh, hcapR, hcapG, hcapO, hcapB⟩ := h₆ op' this
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case refine_7 =>
      intro region regionInBounds
      apply OperationPtr.WellFormed.region_parent.unchanged (ctx := ctx) <;> grind
    all_goals grind
  ·
    intros bl hbl
    have : bl.InBounds ctx := by grind
    grind [BlockPtr.WellFormed_unchanged]
  ·
    grind [RegionPtr.WellFormed_unchanged]


end Construction

variable {OpInfo : Type} [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo]

theorem Rewriter.initOpResults_constructionWellFormed {opPtr : Sim.OperationPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {resultTypes index h₁ h₂ h₃ h₄ h₅}
    (heq : initOpResults opPtr ctx resultTypes index h₁ h₂ h₃ h₄ h₅ = ctx') :
    ConstructionWellFormed ctx.spec opPtr.spec ∅ ∅ →
    ConstructionWellFormed ctx'.spec opPtr.spec ∅ ∅ := by
  simp only [initOpResults_def] at heq
  fun_induction initOpResultsSim
  · subst ctx'
    exact id
  · rename_i ih
    intro hwf
    apply ih heq
    rw [Rewriter.pushResultAt_spec (heq := rfl)]
    exact Construction.pushResult_wellFormed hwf

theorem Rewriter.initOpResults_numResults {opPtr : Sim.OperationPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {resultTypes index h₁ h₂ h₃ h₄ h₅}
    (heq : initOpResults opPtr ctx resultTypes index h₁ h₂ h₃ h₄ h₅ = ctx')
    (hindex : index.toNat ≤ resultTypes.size) :
    opPtr.spec.getNumResults! ctx'.spec = resultTypes.size := by
  simp only [initOpResults_def] at heq
  fun_induction initOpResultsSim <;> grind [Array.usize_toUInt64_toNat, UInt64.le_iff_toNat_le]

theorem Rewriter.initOpResults_preserves_capResults (ptr : Veir.OperationPtr)
    {opPtr : Sim.OperationPtr} {ctx ctx' : Sim.IRContext OpInfo} {resultTypes index h₁ h₂ h₃ h₄ h₅}
    (heq : initOpResults opPtr ctx resultTypes index h₁ h₂ h₃ h₄ h₅ = ctx') :
    (ptr.get! ctx'.spec).capResults = (ptr.get! ctx.spec).capResults := by
  simp only [initOpResults_def] at heq
  fun_induction initOpResultsSim <;> grind [Rewriter.pushResultAt_spec]

theorem Rewriter.initOpResults_preserves_parent (ptr : Veir.OperationPtr)
    {opPtr : Sim.OperationPtr} {ctx ctx' : Sim.IRContext OpInfo} {resultTypes index h₁ h₂ h₃ h₄ h₅}
    (heq : initOpResults opPtr ctx resultTypes index h₁ h₂ h₃ h₄ h₅ = ctx') :
    (ptr.get! ctx'.spec).parent = (ptr.get! ctx.spec).parent := by
  simp only [initOpResults_def] at heq
  fun_induction initOpResultsSim <;> grind [Rewriter.pushResultAt_spec]

/-- Completing the result loop restores the result capacity equality. -/
theorem Rewriter.initOpResults_finishesResults {opPtr : Sim.OperationPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {resultTypes index h₁ h₂ h₃ h₄ h₅}
    (heq : initOpResults opPtr ctx resultTypes index h₁ h₂ h₃ h₄ h₅ = ctx')
    (hwf : ConstructionWellFormed ctx.spec opPtr.spec ∅ ∅)
    (hindex : index.toNat ≤ resultTypes.size)
    (hcapacity : (opPtr.spec.get! ctx.spec).capResults = resultTypes.size) :
    ConstructionWellFormed ctx'.spec opPtr.spec ∅ ∅ ∧
      (opPtr.spec.get! ctx'.spec).capResults = opPtr.spec.getNumResults! ctx'.spec := by
  refine ⟨initOpResults_constructionWellFormed heq hwf, ?_⟩
  rw [initOpResults_preserves_capResults opPtr.spec heq, initOpResults_numResults heq hindex]
  exact hcapacity

end Veir
