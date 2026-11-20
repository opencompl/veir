module

public import Veir.Interpreter.CTreeStateRefinement
public import Veir.Interpreter.Lemmas
public import Veir.PatternRewriter.Puddle.ScopeEdges
import all Veir.Interpreter.Refinement.Basic
import all Veir.Interpreter.VariableState

namespace Veir.Puddle.CTree
public section

theorem exists_setArgumentValues_of_refined
    {sourceCtx targetCtx : WfIRContext OpCode} {block : BlockPtr}
    {source source' : VariableState sourceCtx} (target : VariableState targetCtx)
    {sourceValues targetValues : Array RuntimeValue}
    {sourceIn : block.InBounds sourceCtx.raw} (targetIn : block.InBounds targetCtx.raw)
    (types : block.getArgumentTypes! targetCtx.raw = block.getArgumentTypes! sourceCtx.raw)
    (values : sourceValues ⊒ targetValues)
    (sourceSet : source.setArgumentValues? block sourceValues sourceIn = some source') :
    ∃ target', target.setArgumentValues? block targetValues targetIn = some target' := by
  have sourceSize : sourceValues.size = block.getNumArguments! sourceCtx.raw := by
    unfold VariableState.setArgumentValues? at sourceSet
    split at sourceSet <;> simp_all
  have count := congrArg Array.size types
  simp only [BlockPtr.getArgumentTypes!.size_eq_getNumArguments!] at count
  have targetSize : targetValues.size = block.getNumArguments! targetCtx.raw := by
    grind [RuntimeValue.arrayIsRefinedBy]
  apply (VariableState.setArgumentValues?_isSome_iff_conforms target targetSize).mp
  intro index bound
  have sourceBound : index < block.getNumArguments! sourceCtx.raw := by omega
  have sourceLookup := VariableState.getVar?_getArgument_of_setArgumentValues? sourceBound sourceSet
  have sourceConforms := VariableState.getVar?_conforms sourceLookup
  have targetConforms := sourceConforms.of_isRefinedBy (values.2 index (by omega))
  have typeEq := congrArg (fun a : Array TypeAttr => a[index]!) types
  rw [BlockPtr.getArgumentTypes!.getElem!_eq_getArgument bound,
    BlockPtr.getArgumentTypes!.getElem!_eq_getArgument sourceBound] at typeEq
  simpa [typeEq] using targetConforms

/-- Checked block argument installation preserves scoped refinement using local alias and
scope-back facts, without requiring a globally injective SSA mapping. -/
theorem scoped_setArgumentValues_refined
    {sourceCtx targetCtx : WfIRContext OpCode} {sourceBlock targetBlock : BlockPtr}
    {mapping : ValueMapping sourceCtx targetCtx}
    {source newSource : VariableState sourceCtx} {targetVars newTargetVars : VariableState targetCtx}
    {sourcePoint targetPoint nextSourcePoint nextTargetPoint : RefinementPoint}
    {sourcePointIn : sourcePoint.InBounds sourceCtx.raw} {targetPointIn : targetPoint.InBounds targetCtx.raw}
    {nextSourceIn : nextSourcePoint.InBounds sourceCtx.raw} {nextTargetIn : nextTargetPoint.InBounds targetCtx.raw}
    (sourceIn : sourceBlock.InBounds sourceCtx.raw) (targetIn : targetBlock.InBounds targetCtx.raw)
    (related : source.isRefinedByAt targetVars mapping sourcePoint targetPoint sourcePointIn targetPointIn)
    (argumentPointers : targetBlock.getArguments! targetCtx.raw =
      mapping.applyToArray (sourceBlock.getArguments! sourceCtx.raw))
    (noAlias : ∀ (value : ValuePtr) (valueIn : value.InBounds sourceCtx.raw),
      value.InScopeAt nextSourcePoint sourceCtx →
      (mapping ⟨value, valueIn⟩).val.InScopeAt nextTargetPoint targetCtx →
      value ∉ sourceBlock.getArguments! sourceCtx.raw →
      (mapping ⟨value, valueIn⟩).val ∉ targetBlock.getArguments! targetCtx.raw)
    (sourceFrame : ∀ value, value.InBounds sourceCtx.raw →
      value ∉ sourceBlock.getArguments! sourceCtx.raw →
      value.InScopeAt nextSourcePoint sourceCtx → value.InScopeAt sourcePoint sourceCtx)
    (targetFrame : ∀ (value : ValuePtr) (valueIn : value.InBounds sourceCtx.raw),
      value ∉ sourceBlock.getArguments! sourceCtx.raw →
      value.InScopeAt nextSourcePoint sourceCtx →
      (mapping ⟨value, valueIn⟩).val.InScopeAt nextTargetPoint targetCtx →
      (mapping ⟨value, valueIn⟩).val.InScopeAt targetPoint targetCtx)
    {sourceValues targetValues : Array RuntimeValue}
    (values : RuntimeValue.arrayIsRefinedBy sourceValues targetValues)
    (sourceSet : source.setArgumentValues? sourceBlock sourceValues sourceIn = some newSource)
    (targetSet : targetVars.setArgumentValues? targetBlock targetValues targetIn = some newTargetVars) :
    newSource.isRefinedByAt newTargetVars mapping nextSourcePoint nextTargetPoint nextSourceIn nextTargetIn := by
  intro value valueIn sourceScope targetScope sourceValue sourceLookup targetValue targetLookup
  by_cases member : value ∈ sourceBlock.getArguments! sourceCtx.raw
  · obtain ⟨index, indexIn, argumentEq⟩ := BlockPtr.getArguments!.mem_iff_exists_index.mp member
    have sourceSize : sourceValues.size = sourceBlock.getNumArguments! sourceCtx.raw := by
      unfold VariableState.setArgumentValues? at sourceSet
      split at sourceSet <;> simp_all
    have targetSize : targetValues.size = targetBlock.getNumArguments! targetCtx.raw := by
      unfold VariableState.setArgumentValues? at targetSet
      split at targetSet <;> simp_all
    have mapped : (mapping ⟨value, valueIn⟩).val = targetBlock.getArgument index := by
      have h := argumentPointers.symm
      simp only [ValueMapping.applyToArray, Array.ext_iff, Array.size_map, Array.size_attach,
        BlockPtr.getArguments!.size_eq_getNumArguments!, Array.getElem_map,
        Array.getElem_attach] at h
      grind
    have targetIndex : index < targetBlock.getNumArguments! targetCtx.raw := by
      grind [RuntimeValue.arrayIsRefinedBy]
    have sourceArgument := VariableState.getVar?_getArgument_of_setArgumentValues? indexIn sourceSet
    have targetArgument := VariableState.getVar?_getArgument_of_setArgumentValues? targetIndex targetSet
    grind [RuntimeValue.arrayIsRefinedBy]
  · have targetNotArgument := noAlias value valueIn sourceScope targetScope member
    rw [VariableState.getVar?_setArgumentValues?_of_notMem_getArguments! member sourceSet] at sourceLookup
    rw [VariableState.getVar?_setArgumentValues?_of_notMem_getArguments! targetNotArgument targetSet] at targetLookup
    exact related value valueIn (sourceFrame value valueIn member sourceScope)
      (targetFrame value valueIn member sourceScope targetScope) sourceValue sourceLookup targetValue targetLookup

end
end Veir.Puddle.CTree
