module

public import Veir.Interpreter.Refinement.Basic

import all Veir.Interpreter.Refinement.Basic

public section

namespace Veir
open Veir.Data
open Veir.Data (Pointer)
open Veir.Data.LLVM (Ptr)

variable {OpInfo : Type} [HasOpInfo OpInfo]

/-! ## Reflexivity  -/

@[simp, grind .]
theorem RuntimeValue.isRefinedBy_refl (v : RuntimeValue) : v ⊒ v := by
  cases v <;> grind [RuntimeValue.isRefinedBy]

@[simp, grind .]
theorem RuntimeValue.arrayIsRefinedBy_refl (a : Array RuntimeValue) : a ⊒ a := by
  simp [arrayIsRefinedBy]

@[simp, grind .]
theorem RuntimeValue.arrayIsRefinedBy_nil :
    #[] ⊒ #[] := by
  simp [arrayIsRefinedBy]

@[simp, grind =]
theorem RuntimeValue.arrayIsRefinedBy_singleton {a b : RuntimeValue} :
    #[a] ⊒ #[b] ↔ a ⊒ b := by
  simp [arrayIsRefinedBy]

@[simp, grind =]
theorem RuntimeValue.arrayIsRefinedBy_cons {a b : RuntimeValue} {as bs : List RuntimeValue} :
    List.toArray (a :: as) ⊒ List.toArray (b :: bs) ↔
    a ⊒ b ∧ List.toArray as ⊒ List.toArray bs := by
  simp [arrayIsRefinedBy]
  constructor
  · rintro ⟨h₁, h₂⟩
    grind [h₂ 0]
  · grind

@[simp, grind .]
theorem MemoryObject.isRefinedBy_refl (m : MemoryObject) :
    m ⊒ m := by
  refine ⟨rfl, ?_⟩
  bv_normalize
  grind

@[simp, grind .]
theorem MemoryState.isRefinedBy_refl (m : MemoryState) :
    m ⊒ m :=
  ⟨rfl, fun _ => MemoryObject.isRefinedBy_refl _⟩

@[simp, grind .]
theorem FunctionResult.isRefinedBy_refl (r : MemoryState × Array RuntimeValue) : r ⊒ r := by
  simp [FunctionResult.isRefinedBy]

@[simp, grind .]
theorem Interp.isRefinedBy_refl_of_ne_fail {α : Type} {R : α → α → Prop}
    (hR : ∀ a, R a a) (x : Interp α) (neFail : x.isFail = false) : Interp.isRefinedBy R x x := by
  rcases x with _ | _ | x <;> grind [Interp.isRefinedBy]

@[simp, grind .]
theorem VariableState.isRefinedBy_refl
    {ctx : WfIRContext OpInfo} {state : VariableState ctx} :
    state.isRefinedBy state id := by
  grind [VariableState.isRefinedBy]

@[simp, grind .]
theorem InterpreterState.isRefinedBy_refl
    {ctx : WfIRContext OpInfo} {state : InterpreterState ctx} :
    state.isRefinedBy state id := by
  grind [InterpreterState.isRefinedBy, VariableState.isRefinedBy]

@[simp, grind .]
theorem ControlFlowAction.isRefinedBy_refl (cf : ControlFlowAction) : cf ⊒ cf := by
  cases cf <;> simp [ControlFlowAction.isRefinedBy]

@[simp, grind .]
theorem ControlFlowAction.optionIsRefinedBy_refl (cf : Option ControlFlowAction) :
    ControlFlowAction.optionIsRefinedBy cf cf := by
  cases cf with
  | none => trivial
  | some a => cases a <;> simp [ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy]

@[simp, grind .]
theorem OperationResult.isRefinedBy_refl
    (r : Array RuntimeValue × MemoryState × Option ControlFlowAction) :
    OperationResult.isRefinedBy r r := by
  simp [OperationResult.isRefinedBy, ControlFlowAction.optionIsRefinedBy_refl]

@[grind .]
theorem Interp.isRefinedBy_refl_operationResult
    (x : Interp (Array RuntimeValue × MemoryState × Option ControlFlowAction)) :
    Interp.isRefinedBy OperationResult.isRefinedBy x x := by
  cases x <;> simp [Interp.isRefinedBy]

/-! ## Transitivity -/

theorem RuntimeValue.isRefinedBy_trans {v₁ v₂ v₃ : RuntimeValue}
    (h12 : v₁ ⊒ v₂) (h23 : v₂ ⊒ v₃) : v₁ ⊒ v₃ := by
  cases v₁ <;>
    grind [RuntimeValue.isRefinedBy, isRefinedBy_trans,
      cases RuntimeValue, LLVM.Byte.isRefinedBy_trans]

theorem MemoryObject.isRefinedBy_trans {m1 m2 m3 : MemoryObject}
    (h12 : m1 ⊒ m2) (h23 : m2 ⊒ m3) : m1 ⊒ m3 := by
  obtain ⟨hb12, h12⟩ := h12
  obtain ⟨hb23, h23⟩ := h23
  refine ⟨hb12.trans hb23, ?_⟩
  intro addr
  specialize h12 addr
  specialize h23 addr
  bv_normalize
  grind

theorem MemoryState.isRefinedBy_trans {m1 m2 m3 : MemoryState}
    (h12 : m1 ⊒ m2) (h23 : m2 ⊒ m3) : m1 ⊒ m3 :=
  ⟨h12.1.trans h23.1, fun i => MemoryObject.isRefinedBy_trans (h12.2 i) (h23.2 i)⟩

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

theorem FunctionOp.isRefinedBy_trans
    (h12 : isRefinedBy func₁ func₂ op₁In op₂In)
    (h23 : isRefinedBy func₂ func₃ op₂In op₃In) :
    isRefinedBy func₁ func₃ op₁In op₃In := by
  grind [isRefinedBy, Interp.isRefinedBy_trans, FunctionResult.isRefinedBy_trans]

theorem OperationPtr.isRefinedByAsFunction_trans
    (h12 : isRefinedByAsFunction op₁ ctx₁ op₂ ctx₂ op₁In op₂In)
    (h23 : isRefinedByAsFunction op₂ ctx₂ op₃ ctx₃ op₂In op₃In) :
    isRefinedByAsFunction op₁ ctx₁ op₃ ctx₃ op₁In op₃In := by
  grind [isRefinedByAsFunction, FunctionOp.isRefinedBy_trans]

theorem OperationPtr.isModuleRefinedBy_trans
    (h12 : isModuleRefinedBy mod₁ ctx₁ mod₂ ctx₂)
    (h23 : isModuleRefinedBy mod₂ ctx₂ mod₃ ctx₃) :
    isModuleRefinedBy mod₁ ctx₁ mod₃ ctx₃ := by
  grind [isModuleRefinedBy, isRefinedByAsFunction_trans]

/-! ## Inversion

Inversion lemmas for `RuntimeValue.isRefinedBy`: given a refinement hypothesis `v ⊒ tv`
where the source value `v` has a known constructor, these lemmas recover the shape of the
target value `tv`.
-/

/--
A runtime value `tv` that refines an integer runtime value `v` is itself an integer of the same
width, and the underlying integer value refines `v`.
-/
theorem RuntimeValue.int_of_isRefinedBy {bw : Nat} {v : Data.LLVM.Int bw} {tv : RuntimeValue}
    (h : RuntimeValue.int bw v ⊒ tv) :
    ∃ t : Data.LLVM.Int bw, tv = RuntimeValue.int bw t ∧ v ⊒ t := by
  cases tv <;> grind [RuntimeValue.isRefinedBy]

/--
A runtime value `tv` that refines a byte runtime value `v` is itself a byte of the same
width, and the underlying byte value refines `v`.
-/
theorem RuntimeValue.byte_of_isRefinedBy {bw : Nat} {v : Data.LLVM.Byte bw} {tv : RuntimeValue}
    (h : RuntimeValue.byte bw v ⊒ tv) :
    ∃ t : Data.LLVM.Byte bw, tv = RuntimeValue.byte bw t ∧ v ⊒ t := by
  cases tv <;> grind [RuntimeValue.isRefinedBy]

/-- A runtime value `tv` that refines a float runtime value `v` is equal to it. -/
theorem RuntimeValue.float_of_isRefinedBy {ty : FloatType} {v : Data.Float.FloatValue ty.format}
    {tv : RuntimeValue}
    (h : RuntimeValue.float ty v ⊒ tv) :
    tv = RuntimeValue.float ty v := by
  cases tv <;> grind [RuntimeValue.isRefinedBy]

/-- A source array of one value fixes the target array to one value that it refines. -/
theorem RuntimeValue.arrayIsRefinedBy_toList_singleton {a b : Array RuntimeValue}
    {v : RuntimeValue} (hEq : a.toList = [v]) (h : a ⊒ b) :
    ∃ w, b.toList = [w] ∧ v ⊒ w := by
  cases a; cases b; grind [arrayIsRefinedBy, List.length_eq_one_iff]

/-- A runtime value `tv` that refines a non-poison pointer value `v` is equal to it. -/
theorem RuntimeValue.addr_val_of_isRefinedBy {p : Data.Pointer} {tv : RuntimeValue}
    (h : RuntimeValue.addr (.val p) ⊒ tv) : tv = RuntimeValue.addr (.val p) := by
  cases tv <;> grind [RuntimeValue.isRefinedBy, Data.LLVM.Ptr.isRefinedBy, cases Data.LLVM.Ptr]

/-- A runtime value `tv` that refines a register runtime value `v` is equal to it. -/
theorem RuntimeValue.reg_of_isRefinedBy {v : Data.RISCV.Reg} {tv : RuntimeValue}
    (h : RuntimeValue.reg v ⊒ tv) :
    tv = RuntimeValue.reg v := by
  cases tv <;> grind [RuntimeValue.isRefinedBy]

/--
A register runtime value can only be refined by itself, so operand arrays that consist purely of
registers are refined only by themselves.
-/
theorem RuntimeValue.eq_of_arrayIsRefinedBy_of_regs {a b : Array RuntimeValue}
    (h : a ⊒ b) (hregs : ∀ v ∈ a, ∃ r, v = .reg r) : b = a := by
  grind [arrayIsRefinedBy, reg_of_isRefinedBy, Array.getElem_mem]

/-! ## Interp refinements -/

/-- `fail` is refined by any value. -/
@[simp, grind .]
theorem Interp.isRefinedBy_fail_target :
    Interp.isRefinedBy R (.fail op) target := by
  simp [Interp.isRefinedBy]

/-- `ub` is refined by any value. -/
@[simp, grind .]
theorem Interp.isRefinedBy_ub_target :
    Interp.isRefinedBy R (.ub op) target := by
  simp only [Interp.isRefinedBy]

/-- `ok` is only refined by `ok` values that satisfy the given refinement relation. -/
@[simp, grind =]
theorem Interp.isRefinedBy_ok_target_iff :
    Interp.isRefinedBy R (.ok sourceRes) target ↔
    ∃ targetRes, target = .ok targetRes ∧ R sourceRes targetRes := by
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

/-- A source array of two values fixes the target array to two values that it refines. -/
theorem RuntimeValue.arrayIsRefinedBy_toList_pair {a b : Array RuntimeValue}
    {v₁ v₂ : RuntimeValue} (hEq : a.toList = [v₁, v₂]) (h : a ⊒ b) :
    ∃ w₁ w₂, b.toList = [w₁, w₂] ∧ v₁ ⊒ w₁ ∧ v₂ ⊒ w₂ := by
  cases a; cases b; subst hEq
  obtain ⟨w₁, w₂, rfl⟩ := List.exists_eq_pair (by simpa using h.1.symm)
  exact ⟨w₁, w₂, rfl, by grind [arrayIsRefinedBy], by grind [arrayIsRefinedBy]⟩

/-- A source array of three values fixes the target array to three values that it refines. -/
theorem RuntimeValue.arrayIsRefinedBy_toList_triple {a b : Array RuntimeValue}
    {v₁ v₂ v₃ : RuntimeValue} (hEq : a.toList = [v₁, v₂, v₃]) (h : a ⊒ b) :
    ∃ w₁ w₂ w₃, b.toList = [w₁, w₂, w₃] ∧ v₁ ⊒ w₁ ∧ v₂ ⊒ w₂ ∧ v₃ ⊒ w₃ := by
  cases a; cases b; subst hEq
  obtain ⟨w₁, w₂, w₃, rfl⟩ := List.exists_eq_triple (by simpa using h.1.symm)
  exact ⟨w₁, w₂, w₃, rfl, by grind [arrayIsRefinedBy], by grind [arrayIsRefinedBy],
    by grind [arrayIsRefinedBy]⟩

/-- A runtime value `tv` that refines a non-poison integer value `v` is equal to it. -/
theorem RuntimeValue.int_val_of_isRefinedBy {bw : Nat} {v : BitVec bw} {tv : RuntimeValue}
    (h : RuntimeValue.int bw (.val v) ⊒ tv) : tv = RuntimeValue.int bw (.val v) := by
  cases tv <;> grind [RuntimeValue.isRefinedBy, isRefinedBy, cases Data.LLVM.Int]

/-- Two integers that refine are refined as runtime values. -/
theorem RuntimeValue.int_isRefinedBy {bw : Nat} {v w : Data.LLVM.Int bw} (h : v ⊒ w) :
    RuntimeValue.int bw v ⊒ RuntimeValue.int bw w :=
  ⟨rfl, by simpa using h⟩

/-- A slice of the source is refined by the same slice of the target. -/
theorem RuntimeValue.arrayIsRefinedBy_extract {a b : Array RuntimeValue} (h : a ⊒ b) (i j : Nat) :
    a.extract i j ⊒ b.extract i j := by
  refine ⟨by simp [h.1], fun k hk => ?_⟩
  simp only [Array.size_extract] at hk
  have hk' := h.2 (i + k) (by omega)
  rw [getElem!_pos _ _ (by omega), getElem!_pos _ _ (by rw [← h.1]; omega)] at hk'
  rw [getElem!_pos _ _ (by simp only [Array.size_extract]; omega),
    getElem!_pos _ _ (by simp only [Array.size_extract, ← h.1]; omega)]
  simpa using hk'

/-- The same, for a slice that runs to the end. -/
theorem RuntimeValue.arrayIsRefinedBy_extract_from {a b : Array RuntimeValue} (h : a ⊒ b)
    (i : Nat) : a.extract i ⊒ b.extract i := by
  have hx := RuntimeValue.arrayIsRefinedBy_extract h i a.size
  rw [show b.extract i a.size = b.extract i by rw [h.1]] at hx
  exact hx

/-- An element of the source has a counterpart in the target that it refines. -/
theorem RuntimeValue.getElem?_of_arrayIsRefinedBy {a b : Array RuntimeValue} (h : a ⊒ b)
    {i : Nat} {v : RuntimeValue} (hv : a[i]? = some v) : ∃ w, b[i]? = some w ∧ v ⊒ w := by
  have hi : i < a.size := by
    apply Classical.byContradiction
    intro hNot
    rw [Array.getElem?_eq_none_iff.mpr (by omega)] at hv
    exact absurd hv (by simp)
  obtain rfl : a[i] = v := by
    rw [Array.getElem?_eq_getElem hi] at hv
    exact Option.some.inj hv
  refine ⟨b[i]!, ?_, ?_⟩
  · rw [getElem!_pos b i (by rw [← h.1]; omega)]
    exact Array.getElem?_eq_getElem _
  · have hh := h.2 i hi
    rwa [getElem!_pos a i hi] at hh

/-- An operation that returns one value, leaves the memory alone and asks for no control flow. -/
theorem OperationResult.isRefinedBy_value {v w : RuntimeValue} {mem : MemoryState} (h : v ⊒ w) :
    OperationResult.isRefinedBy (#[v], mem, none) (#[w], mem, none) :=
  ⟨RuntimeValue.arrayIsRefinedBy_singleton.mpr h, rfl, trivial⟩
