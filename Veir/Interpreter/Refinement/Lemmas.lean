import Veir.Interpreter.Refinement.Basic

namespace Veir
open Veir.Data

variable {OpInfo : Type} [HasOpInfo OpInfo]

/-! ## Reflexivity  -/

@[simp, grind .]
theorem RuntimeValue.isRefinedBy_refl (v : RuntimeValue) : v ⊒ v := by
  cases v <;> simp [RuntimeValue.isRefinedBy]

@[simp, grind .]
theorem RuntimeValue.arrayIsRefinedBy_refl (a : Array RuntimeValue) : a ⊒ a := by
  simp [arrayIsRefinedBy]

@[simp, grind .]
theorem FunctionResult.isRefinedBy_refl (r : MemoryState × Array RuntimeValue) : r ⊒ r := by
  simp [FunctionResult.isRefinedBy]

@[simp, grind .]
theorem Interp.isRefinedBy_refl_of_ne_none {α : Type} {R : α → α → Prop}
    (hR : ∀ a, R a a) (x : Interp α) (neNone : x ≠ none) : Interp.isRefinedBy R x x := by
  rcases x with _ | (x | _) <;> grind [Interp.isRefinedBy]

/-- `isRefinedByAt` is reflexive under the identity mapping at any program point. -/
@[simp, grind .]
theorem VariableState.isRefinedByAt_refl
    {ctx : WfIRContext OpInfo} {state : VariableState ctx}
    {p : InsertPoint} {pIn : p.InBounds ctx.raw} :
    state.isRefinedByAt state id p p := by
  grind [VariableState.isRefinedByAt]

/-- `isRefinedByAt` is reflexive for `InterpreterState` under the identity mapping at any point. -/
@[simp, grind .]
theorem InterpreterState.isRefinedByAt_refl
    {ctx : WfIRContext OpInfo} {state : InterpreterState ctx}
    {p : InsertPoint} {pIn : p.InBounds ctx.raw} :
    state.isRefinedByAt state id p p := by
  grind [InterpreterState.isRefinedByAt]

@[simp, grind .]
theorem ControlFlowAction.isRefinedBy_refl (cf : ControlFlowAction) : cf ⊒ cf := by
  cases cf <;> simp [ControlFlowAction.isRefinedBy]

@[simp, grind .]
theorem ControlFlowAction.optionIsRefinedBy_refl (cf : Option ControlFlowAction) :
    ControlFlowAction.optionIsRefinedBy cf cf := by
  cases cf with
  | none => trivial
  | some a => cases a <;> simp [ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy]

/-! ## Transitivity -/

theorem RuntimeValue.isRefinedBy_trans {v₁ v₂ v₃ : RuntimeValue}
    (h12 : v₁ ⊒ v₂) (h23 : v₂ ⊒ v₃) : v₁ ⊒ v₃ := by
  grind [RuntimeValue.isRefinedBy, isRefinedBy_trans, cases RuntimeValue]

theorem RuntimeValue.arrayIsRefinedBy_trans {a b c : Array RuntimeValue}
    (h12 : a ⊒ b) (h23 : b ⊒ c) : a ⊒ c := by
  grind [RuntimeValue.arrayIsRefinedBy, RuntimeValue.isRefinedBy_trans]

theorem FunctionResult.isRefinedBy_trans {r₁ r₂ r₃ : MemoryState × Array RuntimeValue}
    (h12 : r₁ ⊒ r₂) (h23 : r₂ ⊒ r₃) : r₁ ⊒ r₃ := by
  grind [FunctionResult.isRefinedBy, RuntimeValue.arrayIsRefinedBy_trans]

theorem Interp.isRefinedBy_trans {α : Type} {R : α → α → Prop}
    (hR : ∀ a b c, R a b → R b c → R a c)
    {v₁ v₂ v₃ : Interp α}
    (h₁₂ : Interp.isRefinedBy R v₁ v₂) (h₂₃ : Interp.isRefinedBy R v₂ v₃) :
    Interp.isRefinedBy R v₁ v₃ := by
  simp only [isRefinedBy] at h₁₂ h₂₃ ⊢
  rcases v₁ with _ | (v₁ | _) <;>
  rcases v₂ with _ | (v₂ | _) <;>
  rcases v₃ with _ | (v₃ | _) <;>
  grind

theorem OperationPtr.isRefinedByAsFunction_trans
    (h12 : isRefinedByAsFunction op₁ ctx₁ op₂ ctx₂ op₁In op₂In)
    (h23 : isRefinedByAsFunction op₂ ctx₂ op₃ ctx₃ op₂In op₃In) :
    isRefinedByAsFunction op₁ ctx₁ op₃ ctx₃ op₁In op₃In := by
  grind [isRefinedByAsFunction, Interp.isRefinedBy_trans, FunctionResult.isRefinedBy_trans]

theorem OperationPtr.isModuleRefinedBy_trans
    (h12 : isModuleRefinedBy mod₁ ctx₁ mod₂ ctx₂)
    (h23 : isModuleRefinedBy mod₂ ctx₂ mod₃ ctx₃) :
    isModuleRefinedBy mod₁ ctx₁ mod₃ ctx₃ := by
  grind [isModuleRefinedBy, isRefinedByAsFunction_trans]

/-! ## Interp refinements -/

/-- `none` is refined by any value. -/
@[simp, grind .]
theorem Interp.isRefinedBy_none_target :
    Interp.isRefinedBy R none target := by
  simp [Interp.isRefinedBy]

/-- `ub` is refined by any value. -/
@[simp, grind .]
theorem Interp.isRefinedBy_ub_target :
    Interp.isRefinedBy R (some .ub) target := by
  simp only [Interp.isRefinedBy]

/-- `ok` is only refined by `ok` values that satisfy the given refinement relation. -/
@[simp, grind =]
theorem Interp.isRefinedBy_ok_target_iff :
    Interp.isRefinedBy R (some (.ok sourceRes)) target ↔
    ∃ targetRes, target = some (.ok targetRes) ∧ R sourceRes targetRes := by
  simp only [Interp.isRefinedBy]
  rcases target with _ | (_ | _) <;> grind

/-! ## ValueMapping -/

/-- Applying a value mapping to an array preserves its size. -/
@[simp, grind =]
theorem ValueMapping.applyToArray_size {ctx ctx' : WfIRContext OpInfo} (mapping : ValueMapping ctx ctx')
    (vals : Array ValuePtr) (valsIn : ∀ v ∈ vals, v.InBounds ctx.raw) :
    (mapping.applyToArray vals valsIn).size = vals.size := by
  simp [ValueMapping.applyToArray]

/-- Extensibility theorem for value mappings mapping `op` results to `op'` results. -/
theorem ValueMapping.applyToArray_getResults!_ext
    {ctx ctx' : WfIRContext OpInfo} {op op' : OperationPtr}
    {mapping : ValueMapping ctx ctx'}
    (opIn : op.InBounds ctx.raw)
    (hResults : mapping.applyToArray (op.getResults! ctx.raw) = op'.getResults! ctx'.raw) :
    ∀ (i : Nat) (hi : i < op.getNumResults! ctx.raw),
      (mapping ⟨op.getResult i, (by grind)⟩).val = op'.getResult i := by
  intro i hi
  simp only [applyToArray, Array.ext_iff, Array.size_map, Array.size_attach,
    OperationPtr.getResults!.size_eq_getNumResults!, Array.getElem_map,
    Array.getElem_attach] at hResults
  grind

/-- Extensibility theorem for value mappings fixing a block's argument pointers across contexts. -/
theorem ValueMapping.applyToArray_getArguments!_ext
    {ctx ctx' : WfIRContext OpInfo} {block : BlockPtr}
    {mapping : ValueMapping ctx ctx'}
    (blockIn : block.InBounds ctx.raw)
    (hArgs : mapping.applyToArray (block.getArguments! ctx.raw) = block.getArguments! ctx'.raw) :
    ∀ (i : Nat) (hi : i < block.getNumArguments! ctx.raw),
      (mapping ⟨block.getArgument i, (by grind)⟩).val = block.getArgument i := by
  intro i hi
  simp only [applyToArray, Array.ext_iff, Array.size_map, Array.size_attach,
    BlockPtr.getArguments!.size_eq_getNumArguments!, Array.getElem_map,
    Array.getElem_attach] at hArgs
  grind

/-- If a value mapping reflects results from `op` to `op'`, then values that are not in
`op` results are not mapped to values in `op'` results. -/
@[grind .]
theorem ValueMapping.ReflectsResults.not_mem_getResults
    {ctx ctx' : WfIRContext OpInfo} {mapping : ValueMapping ctx ctx'} {op op' : OperationPtr}
    {val : ValuePtr} (valIn : val.InBounds ctx.raw)
    (hReflect : mapping.ReflectsResults op op')
    (hNotMem : val ∉ op.getResults! ctx.raw) :
    (mapping ⟨val, valIn⟩).val ∉ op'.getResults! ctx'.raw := by
  intro hmem
  simp only [OperationPtr.getResults!.mem_iff_exists_index] at hmem
  have ⟨index, hindex, heq⟩ := hmem
  grind [OperationPtr.getResults!.mem_iff_exists_index, hReflect val valIn index heq.symm]

/-! ## Conformance under refinement -/

/-- Refinement preserves conformance to a type: if `sv ⊒ tv` and `sv` conforms to `ty`, then `tv`
conforms to `ty`. -/
@[grind →]
theorem RuntimeValue.Conforms_of_isRefinedBy {sv tv : RuntimeValue} {ty : TypeAttr}
    (href : sv ⊒ tv) (hconf : sv.Conforms ty) : tv.Conforms ty := by
  obtain ⟨attr, hattr⟩ := ty
  cases sv <;> cases attr <;> simp_all [RuntimeValue.isRefinedBy, RuntimeValue.Conforms]
  all_goals cases tv <;> grind
