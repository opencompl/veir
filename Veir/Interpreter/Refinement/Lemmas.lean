module

public import Veir.Interpreter.Refinement.Basic

import all Veir.Interpreter.Refinement.Basic
import all Veir.Interpreter.Memory
import all Veir.Data.Refinement
import all Veir.Data.Pointer.Basic
import all Veir.Data.LLVM.Ptr.Basic

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
theorem RuntimeValue.arrayIsRefinedBy_nil {m : RefinementMode} :
    (#[] : Array RuntimeValue) ⊒[m] #[] := by
  simp [arrayIsRefinedBy]

@[simp, grind =]
theorem RuntimeValue.arrayIsRefinedBy_singleton {m : RefinementMode} {a b : RuntimeValue} :
    #[a] ⊒[m] #[b] ↔ a ⊒[m] b := by
  simp [arrayIsRefinedBy]

@[simp, grind =]
theorem RuntimeValue.arrayIsRefinedBy_cons {m : RefinementMode} {a b : RuntimeValue}
    {as bs : List RuntimeValue} :
    List.toArray (a :: as) ⊒[m] List.toArray (b :: bs) ↔
    a ⊒[m] b ∧ List.toArray as ⊒[m] List.toArray bs := by
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
theorem RuntimeValue.int_of_isRefinedBy {m : RefinementMode} {bw : Nat} {v : Data.LLVM.Int bw}
    {tv : RuntimeValue} (h : RuntimeValue.int bw v ⊒[m] tv) :
    ∃ t : Data.LLVM.Int bw, tv = RuntimeValue.int bw t ∧ v ⊒ t := by
  cases tv <;> grind [RuntimeValue.isRefinedBy]

/--
A runtime value `tv` that refines a byte runtime value `v` is itself a byte of the same
width, and the underlying byte value refines `v`.
-/
theorem RuntimeValue.byte_of_isRefinedBy {m : RefinementMode} {bw : Nat} {v : Data.LLVM.Byte bw}
    {tv : RuntimeValue} (h : RuntimeValue.byte bw v ⊒[m] tv) :
    ∃ t : Data.LLVM.Byte bw, tv = RuntimeValue.byte bw t ∧ v ⊒ t := by
  cases tv <;> grind [RuntimeValue.isRefinedBy]

/-- A runtime value `tv` that refines a float runtime value `v` is equal to it. -/
theorem RuntimeValue.float_of_isRefinedBy {m : RefinementMode} {ty : FloatType}
    {v : Data.Float.FloatValue ty.format} {tv : RuntimeValue}
    (h : RuntimeValue.float ty v ⊒[m] tv) :
    tv = RuntimeValue.float ty v := by
  cases tv <;> grind [RuntimeValue.isRefinedBy]

/-- A source array of one value fixes the target array to one value that it refines. -/
theorem RuntimeValue.arrayIsRefinedBy_toList_singleton {m : RefinementMode} {a b : Array RuntimeValue}
    {v : RuntimeValue} (hEq : a.toList = [v]) (h : a ⊒[m] b) :
    ∃ w, b.toList = [w] ∧ v ⊒[m] w := by
  cases a; cases b; grind [arrayIsRefinedBy, List.length_eq_one_iff]

/-- A runtime value `tv` that refines a non-poison pointer value `v` is equal to it. -/
theorem RuntimeValue.addr_val_of_isRefinedBy {p : Data.Pointer} {tv : RuntimeValue}
    (h : RuntimeValue.addr (.val p) ⊒ tv) : tv = RuntimeValue.addr (.val p) := by
  cases tv <;> grind [RuntimeValue.isRefinedBy, Data.LLVM.Ptr.isRefinedBy, cases Data.LLVM.Ptr]

/--
A runtime value `tv` that refines a pointer runtime value `v` is itself a pointer, and the
underlying pointer refines `v`.
-/
theorem RuntimeValue.addr_of_isRefinedBy {v : Data.LLVM.Ptr} {tv : RuntimeValue}
    (h : RuntimeValue.addr v ⊒ tv) : ∃ t, tv = RuntimeValue.addr t ∧ v ⊒ t := by
  cases tv <;> grind [RuntimeValue.isRefinedBy]

/-- A runtime value `tv` that refines a register runtime value `v` is equal to it. -/
theorem RuntimeValue.reg_of_isRefinedBy {m : RefinementMode} {v : Data.RISCV.Reg}
    {tv : RuntimeValue} (h : RuntimeValue.reg v ⊒[m] tv) :
    tv = RuntimeValue.reg v := by
  cases tv <;> grind [RuntimeValue.isRefinedBy]

/--
A register runtime value can only be refined by itself, so operand arrays that consist purely of
registers are refined only by themselves.
-/
theorem RuntimeValue.eq_of_arrayIsRefinedBy_of_regs {m : RefinementMode} {a b : Array RuntimeValue}
    (h : a ⊒[m] b) (hregs : ∀ v ∈ a, ∃ r, v = .reg r) : b = a := by
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
theorem RuntimeValue.arrayIsRefinedBy_toList_pair {m : RefinementMode} {a b : Array RuntimeValue}
    {v₁ v₂ : RuntimeValue} (hEq : a.toList = [v₁, v₂]) (h : a ⊒[m] b) :
    ∃ w₁ w₂, b.toList = [w₁, w₂] ∧ v₁ ⊒[m] w₁ ∧ v₂ ⊒[m] w₂ := by
  cases a; cases b; subst hEq
  obtain ⟨w₁, w₂, rfl⟩ := List.exists_eq_pair (by simpa using h.1.symm)
  exact ⟨w₁, w₂, rfl, by grind [arrayIsRefinedBy], by grind [arrayIsRefinedBy]⟩

/-- A source array of three values fixes the target array to three values that it refines. -/
theorem RuntimeValue.arrayIsRefinedBy_toList_triple {m : RefinementMode} {a b : Array RuntimeValue}
    {v₁ v₂ v₃ : RuntimeValue} (hEq : a.toList = [v₁, v₂, v₃]) (h : a ⊒[m] b) :
    ∃ w₁ w₂ w₃, b.toList = [w₁, w₂, w₃] ∧ v₁ ⊒[m] w₁ ∧ v₂ ⊒[m] w₂ ∧ v₃ ⊒[m] w₃ := by
  cases a; cases b; subst hEq
  obtain ⟨w₁, w₂, w₃, rfl⟩ := List.exists_eq_triple (by simpa using h.1.symm)
  exact ⟨w₁, w₂, w₃, rfl, by grind [arrayIsRefinedBy], by grind [arrayIsRefinedBy],
    by grind [arrayIsRefinedBy]⟩

/-- A runtime value `tv` that refines a non-poison integer value `v` is equal to it. -/
theorem RuntimeValue.int_val_of_isRefinedBy {m : RefinementMode} {bw : Nat} {v : BitVec bw}
    {tv : RuntimeValue} (h : RuntimeValue.int bw (.val v) ⊒[m] tv) :
    tv = RuntimeValue.int bw (.val v) := by
  cases tv <;> grind [RuntimeValue.isRefinedBy, isRefinedBy, cases Data.LLVM.Int]

/-- Two integers that refine are refined as runtime values. -/
theorem RuntimeValue.int_isRefinedBy {m : RefinementMode} {bw : Nat} {v w : Data.LLVM.Int bw}
    (h : v ⊒ w) : RuntimeValue.int bw v ⊒[m] RuntimeValue.int bw w :=
  ⟨rfl, by simpa using h⟩

/-- A slice of the source is refined by the same slice of the target. -/
theorem RuntimeValue.arrayIsRefinedBy_extract {m : RefinementMode} {a b : Array RuntimeValue}
    (h : a ⊒[m] b) (i j : Nat) : a.extract i j ⊒[m] b.extract i j := by
  refine ⟨by simp [h.1], fun k hk => ?_⟩
  simp only [Array.size_extract] at hk
  have hk' := h.2 (i + k) (by omega)
  rw [getElem!_pos _ _ (by omega), getElem!_pos _ _ (by rw [← h.1]; omega)] at hk'
  rw [getElem!_pos _ _ (by simp only [Array.size_extract]; omega),
    getElem!_pos _ _ (by simp only [Array.size_extract, ← h.1]; omega)]
  simpa using hk'

/-- The same, for a slice that runs to the end. -/
theorem RuntimeValue.arrayIsRefinedBy_extract_from {m : RefinementMode} {a b : Array RuntimeValue}
    (h : a ⊒[m] b) (i : Nat) : a.extract i ⊒[m] b.extract i := by
  have hx := RuntimeValue.arrayIsRefinedBy_extract h i a.size
  rw [show b.extract i a.size = b.extract i by rw [h.1]] at hx
  exact hx

/-- An element of the source has a counterpart in the target that it refines. -/
theorem RuntimeValue.getElem?_of_arrayIsRefinedBy {m : RefinementMode} {a b : Array RuntimeValue}
    (h : a ⊒[m] b) {i : Nat} {v : RuntimeValue} (hv : a[i]? = some v) :
    ∃ w, b[i]? = some w ∧ v ⊒[m] w := by
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

/-- Two bytes that refine are refined as runtime values. -/
theorem RuntimeValue.byte_isRefinedBy {m : RefinementMode} {bw : Nat} {v w : Data.LLVM.Byte bw}
    (h : v ⊒ w) : RuntimeValue.byte bw v ⊒[m] RuntimeValue.byte bw w :=
  ⟨rfl, by simpa using h⟩

/-- Two interpretations that begin with the same step refine when their continuations do. -/
theorem Interp.isRefinedBy_bind_same {α β : Type} {R : β → β → Prop} (x : Interp α)
    {f g : α → Interp β} (hR : ∀ a, Interp.isRefinedBy R (f a) (g a)) :
    Interp.isRefinedBy R (x >>= f) (x >>= g) := by
  cases x <;> simp_all [Interp.isRefinedBy]

/-- An operation that returns one value, leaves the memory alone and asks for no control flow. -/
theorem OperationResult.isRefinedBy_value {v w : RuntimeValue} {mem : MemoryState} (h : v ⊒ w) :
    OperationResult.isRefinedBy (#[v], mem, none) (#[w], mem, none) :=
  ⟨RuntimeValue.arrayIsRefinedBy_singleton.mpr h, rfl, trivial, by simp⟩

/-- Decoding an integer into a pointer keeps refinement: poison decodes to a poison pointer. -/
theorem MemoryState.ptrFromInt_mono {mem : MemoryState} {x y : Data.LLVM.Int 64} (h : x ⊒ y) :
    mem.ptrFromInt x ⊒ mem.ptrFromInt y := by
  cases x <;> cases y <;>
    simp_all [MemoryState.ptrFromInt, _root_.isRefinedBy, Data.LLVM.Ptr.isRefinedBy]

/-- The address of a pointer keeps refinement: a poison pointer has a poison address. -/
theorem MemoryState.intFromPtr_mono {mem : MemoryState} {p q : Data.LLVM.Ptr} (h : p ⊒ q) :
    mem.intFromPtr p ⊒ mem.intFromPtr q := by
  cases p <;> cases q <;>
    simp_all [MemoryState.intFromPtr, _root_.isRefinedBy, Data.LLVM.Ptr.isRefinedBy]

/-! ## Across a step -/

/-- A refinement of interpretations survives weakening the relation on their results. -/
theorem Interp.isRefinedBy_mono {α β : Type} {R R' : α → β → Prop} (hR : ∀ a b, R a b → R' a b)
    {x : Interp α} {y : Interp β} (h : Interp.isRefinedBy R x y) : Interp.isRefinedBy R' x y := by
  cases x <;> cases y <;> simp_all [Interp.isRefinedBy]

/-- Assembly-mode refinement of values survives extending the memory. -/
theorem RuntimeValue.isRefinedBy_extends {mem mem' : MemoryState} (hext : mem.Extends mem')
    {v w : RuntimeValue} (h : v ⊒[.asm mem] w) : v ⊒[.asm mem'] w := by
  cases v <;> cases w <;> simp only [RuntimeValue.isRefinedBy] at h ⊢ <;> try exact h
  rename_i s t
  cases s <;> cases t <;> simp only [Data.LLVM.Ptr.isRefinedByIn] at h ⊢
  obtain ⟨hp, hpq⟩ := h
  refine ⟨⟨Nat.lt_of_lt_of_le hp.1 hext.size_le, hp.2⟩, ?_⟩
  rw [hext.address_eq hp.1]
  exact hpq

theorem RuntimeValue.arrayIsRefinedBy_extends {mem mem' : MemoryState} (hext : mem.Extends mem')
    {a b : Array RuntimeValue} (h : a ⊒[.asm mem] b) : a ⊒[.asm mem'] b :=
  ⟨h.1, fun i hi => RuntimeValue.isRefinedBy_extends hext (h.2 i hi)⟩

/-- The state relation, carried to a memory the step extended. -/
theorem VariableState.isRefinedBy_extends {ctx ctx' : WfIRContext OpInfo}
    {state : VariableState ctx} {state' : VariableState ctx'} {mapping : ValueMapping ctx ctx'}
    {asm : Bool} {mem mem' : MemoryState} (hext : asm = true → mem.Extends mem')
    (h : state.isRefinedBy state' mapping (.of asm mem)) :
    state.isRefinedBy state' mapping (.of asm mem') := by
  cases asm
  · simpa using h
  · intro val valIn sv hsv
    obtain ⟨tv, htv, hRef⟩ := h val valIn sv hsv
    exact ⟨tv, htv, RuntimeValue.isRefinedBy_extends (hext rfl) hRef⟩

/-- An LLVM-mode step is a step from any memory: it promises nothing about the layout. -/
theorem Interp.isRefinedBy_operationResultFrom_of_llvm {mem : MemoryState}
    {x y : Interp (Array RuntimeValue × MemoryState × Option ControlFlowAction)}
    (h : Interp.isRefinedBy OperationResult.isRefinedBy x y) :
    Interp.isRefinedBy (OperationResult.isRefinedByFrom mem false) x y :=
  Interp.isRefinedBy_mono (fun _ _ hr => ⟨hr, by simp⟩) h

/-! ## Assembly mode -/

/-- Whether a value may stand in a relation read in `mem`: a pointer names an object of `mem`. -/
@[expose]
def RuntimeValue.ValidIn (mem : MemoryState) : RuntimeValue → Prop
  | .addr (.val p) => p.ValidIn mem
  | _ => True

/-- The null pointer names the null object, which a well-laid-out memory has. -/
theorem RuntimeValue.validIn_null {mem : MemoryState} (h : mem.LayoutWf) :
    (RuntimeValue.addr Data.LLVM.Ptr.null).ValidIn mem := by
  simp [RuntimeValue.ValidIn, Data.Pointer.ValidIn, Data.LLVM.Ptr.null, Data.Pointer.null,
    h.nonempty]

/-- A value that names objects of `mem` refines itself in assembly mode. -/
theorem RuntimeValue.isRefinedBy_refl_asm {mem : MemoryState} {v : RuntimeValue}
    (h : v.ValidIn mem) : v ⊒[.asm mem] v := by
  cases v
  case addr s =>
    cases s
    case val p =>
      simp only [RuntimeValue.isRefinedBy, RuntimeValue.ValidIn, Data.LLVM.Ptr.isRefinedByIn] at h ⊢
      exact ⟨h, Or.inl rfl⟩
    case poison => simp [RuntimeValue.isRefinedBy, Data.LLVM.Ptr.isRefinedByIn]
  all_goals grind [RuntimeValue.isRefinedBy]

/-- Reflexivity in the mode of `mem`, which in assembly mode asks the value to be valid in it. -/
theorem RuntimeValue.isRefinedBy_refl_of {asm : Bool} {mem : MemoryState} {v : RuntimeValue}
    (h : asm = true → v.ValidIn mem) : v ⊒[.of asm mem] v := by
  cases asm
  · simp
  · exact RuntimeValue.isRefinedBy_refl_asm (h rfl)

theorem RuntimeValue.arrayIsRefinedBy_refl_of {asm : Bool} {mem : MemoryState}
    {a : Array RuntimeValue} (h : asm = true → ∀ v ∈ a, v.ValidIn mem) : a ⊒[.of asm mem] a :=
  ⟨rfl, fun i hi => RuntimeValue.isRefinedBy_refl_of fun ha =>
    h ha _ (by rw [getElem!_pos a i hi]; exact Array.getElem_mem hi)⟩

/-- Whether the values an action carries are valid in `mem`. -/
@[expose]
def ControlFlowAction.ValidIn (mem : MemoryState) : Option ControlFlowAction → Prop
  | none => True
  | some (.return vals) => ∀ v ∈ vals, v.ValidIn mem
  | some (.branch vals _) => ∀ v ∈ vals, v.ValidIn mem

theorem ControlFlowAction.optionIsRefinedBy_refl_of {asm : Bool} {mem : MemoryState}
    {act : Option ControlFlowAction} (h : asm = true → ControlFlowAction.ValidIn mem act) :
    ControlFlowAction.optionIsRefinedBy act act (.of asm mem) := by
  rcases act with _ | (_ | _) <;>
    simp only [ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy,
      ControlFlowAction.ValidIn] at h ⊢
  all_goals first
    | exact RuntimeValue.arrayIsRefinedBy_refl_of h
    | exact ⟨trivial, RuntimeValue.arrayIsRefinedBy_refl_of h⟩

/-- A step that returns one value and leaves the memory alone. -/
theorem OperationResult.isRefinedByFrom_value {asm : Bool} {mem : MemoryState}
    {v w : RuntimeValue} (hwf : RefinementMode.Wf asm mem) (h : v ⊒[.of asm mem] w) :
    OperationResult.isRefinedByFrom mem asm (#[v], mem, none) (#[w], mem, none) :=
  ⟨⟨RuntimeValue.arrayIsRefinedBy_singleton.mpr h, rfl, by simp [ControlFlowAction.optionIsRefinedBy],
    hwf⟩, fun _ => MemoryState.Extends.refl mem⟩

/-- A step whose two sides agree and leave the memory alone. -/
theorem OperationResult.isRefinedByFrom_refl {asm : Bool} {mem : MemoryState}
    {vals : Array RuntimeValue} {act : Option ControlFlowAction} (hwf : RefinementMode.Wf asm mem)
    (hvals : asm = true → ∀ v ∈ vals, v.ValidIn mem)
    (hact : asm = true → ControlFlowAction.ValidIn mem act) :
    OperationResult.isRefinedByFrom mem asm (vals, mem, act) (vals, mem, act) :=
  ⟨⟨RuntimeValue.arrayIsRefinedBy_refl_of hvals, rfl,
    ControlFlowAction.optionIsRefinedBy_refl_of hact, hwf⟩, fun _ => MemoryState.Extends.refl mem⟩

/--
The access that makes assembly mode work: when the source accessed through `p`
successfully, the pointer the target holds resolves to the same place.
-/
theorem MemoryState.LayoutWf.resolve_eq_of_isRefinedByIn {mem : MemoryState} (h : mem.LayoutWf)
    {p q : Data.Pointer} (hpq : p.isRefinedByIn mem q) {size : UInt64} {obj : MemoryObject}
    (hacc : mem.checkAccess (mem.resolve p) size = .ok obj) (hsize : size ≠ 0) :
    mem.resolve q = mem.resolve p := by
  obtain ⟨⟨hp, -⟩, hpq⟩ := hpq
  rcases hpq with rfl | ⟨hwild, rfl⟩
  · rfl
  · rw [MemoryState.resolve_of_not_wild hwild] at hacc ⊢
    simp only [MemoryState.resolve, Data.Pointer.ofAddress, ↓reduceIte]
    apply h.decode_address hp _ hwild
    simp only [MemoryState.checkAccess, Array.getElem?_eq_getElem hp, MemoryState.getObject?]
      at hacc
    split at hacc
    · exact absurd ‹_› hsize
    · split at hacc
      · next hin =>
        obtain ⟨hs, ho⟩ := hin
        rw [UInt64.le_iff_toNat_le] at hs ho
        rw [UInt64.toNat_sub_of_le _ _ hs] at ho
        have hmod : (mem.objects[p.object].contents.size.toUInt64).toNat ≤
            mem.objects[p.object].contents.size := by
          first | (simp [Nat.toUInt64]; omega) | simp [Nat.toUInt64]
        simp only [MemoryObject.size]
        omega
      · simp at hacc

/-- Related pointers share their address. -/
theorem MemoryState.LayoutWf.address_eq_of_isRefinedByIn {mem : MemoryState} (h : mem.LayoutWf)
    {p q : Data.Pointer} (hpq : p.isRefinedByIn mem q) : mem.address q = mem.address p := by
  rcases hpq.2 with rfl | ⟨-, rfl⟩
  · rfl
  · exact h.address_ofAddress _

/--
The wild pointer at the address of what the target holds refines the source pointer: a pointer
survives a round trip through its address in assembly mode.
-/
theorem MemoryState.LayoutWf.isRefinedByIn_ofAddress {mem : MemoryState} (h : mem.LayoutWf)
    {p q : Data.Pointer} (hpq : p.isRefinedByIn mem q) :
    p.isRefinedByIn mem (Data.Pointer.ofAddress (mem.address q)) := by
  rw [h.address_eq_of_isRefinedByIn hpq]
  refine ⟨hpq.1, ?_⟩
  cases hw : p.wild
  · exact .inr ⟨rfl, rfl⟩
  · left
    obtain ⟨object, offset, wild⟩ := p
    obtain rfl : object = 0 := hpq.1.2 hw
    obtain rfl : wild = true := hw
    simp [Data.Pointer.ofAddress, MemoryState.address,
      Array.getElem?_eq_getElem h.nonempty, h.base_zero]

/-! ## Steps through memory -/

/-- A bind returns a value only when both halves do. -/
theorem Interp.bind_eq_ok_iff {α β : Type} {x : Interp α} {f : α → Interp β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp

/-- The pointer a source value stands for, as the target holds it. -/
theorem RuntimeValue.addr_val_of_isRefinedBy_of {asm : Bool} {mem : MemoryState} {p : Data.Pointer}
    {w : RuntimeValue} (h : RuntimeValue.addr (.val p) ⊒[.of asm mem] w) :
    ∃ q, w = RuntimeValue.addr (.val q) ∧ (asm = false → q = p) ∧
      (asm = true → p.isRefinedByIn mem q) := by
  cases w <;> simp only [RuntimeValue.isRefinedBy] at h <;> try exact h.elim
  rename_i t
  cases asm <;> simp only [RefinementMode.of_false, RefinementMode.of_true] at h <;>
    cases t <;> simp only [Data.LLVM.Ptr.isRefinedBy, Data.LLVM.Ptr.isRefinedByIn] at h
  · exact ⟨_, rfl, fun _ => h.symm, fun hc => by simp at hc⟩
  · exact ⟨_, rfl, fun hc => by simp at hc, fun _ => h⟩

/-- What refines a pointer is a pointer, in either mode. -/
theorem RuntimeValue.exists_addr_of_isRefinedBy {m : RefinementMode} {v : Data.LLVM.Ptr}
    {w : RuntimeValue} (h : RuntimeValue.addr v ⊒[m] w) : ∃ t, w = RuntimeValue.addr t := by
  cases w <;> simp only [RuntimeValue.isRefinedBy] at h <;> first | exact ⟨_, rfl⟩ | exact h.elim

/-- A pointer related to a non-null pointer is not null. -/
theorem Data.Pointer.ne_null_of_isRefinedByIn {mem : MemoryState} {p q : Data.Pointer}
    (hpq : p.isRefinedByIn mem q) (hp : p ≠ .null) : q ≠ .null := by
  rcases hpq.2 with rfl | ⟨-, rfl⟩
  · exact hp
  · simp [Data.Pointer.ofAddress, Data.Pointer.null]

/-- A load reads the same bytes through two pointers that resolve alike. -/
theorem MemoryState.llvmLoad_eq_of_resolve_eq {mem : MemoryState} {p q : Data.Pointer}
    {type : TypeAttr} (hres : mem.resolve q = mem.resolve p) (hp : p ≠ .null) (hq : q ≠ .null) :
    mem.llvmLoad q type = mem.llvmLoad p type := by
  simp only [MemoryState.llvmLoad, hp, hq, ↓reduceIte, MemoryState.load, MemoryState.loadPoison,
    MemoryState.hasPoison, MemoryState.loadByte64, hres]

/-- A load that returns went through an access of at least a byte. -/
theorem MemoryState.llvmLoad_ok_access {mem : MemoryState} {p : Data.Pointer} {type : TypeAttr}
    {v : RuntimeValue} (hok : mem.llvmLoad p type = .ok v) :
    p ≠ .null ∧ ∃ (n : UInt64) (obj : MemoryObject), n ≠ 0 ∧
      mem.checkAccess (mem.resolve p) n = .ok obj := by
  simp only [MemoryState.llvmLoad] at hok
  split at hok
  · simp at hok
  · next hp =>
    refine ⟨hp, ?_⟩
    split at hok
    all_goals first
      | (simp at hok; done)
      | (simp only [MemoryState.load, MemoryState.loadByte64, Interp.bind_eq_ok_iff,
            Interp.pure_eq, Interp.ok.injEq] at hok
         first
          | (obtain ⟨_, ⟨obj, hobj, -⟩, -⟩ := hok; exact ⟨_, obj, by decide, hobj⟩)
          | (obtain ⟨_, ⟨_, ⟨obj, hobj, -⟩, -⟩, -⟩ := hok; exact ⟨_, obj, by decide, hobj⟩))

/-- A loaded value names objects of a well-laid-out memory. -/
theorem MemoryState.LayoutWf.llvmLoad_validIn {mem : MemoryState} (h : mem.LayoutWf)
    {p : Data.Pointer} {type : TypeAttr} {v : RuntimeValue} (hok : mem.llvmLoad p type = .ok v) :
    v.ValidIn mem := by
  simp only [MemoryState.llvmLoad] at hok
  split at hok
  · simp at hok
  · split at hok
    all_goals first
      | (simp at hok; done)
      | (simp only [Interp.bind_eq_ok_iff, Interp.ok.injEq, Interp.pure_eq] at hok
         first
          | (obtain ⟨_, -, _, -, hv⟩ := hok
             first
              | (split at hv <;> (simp only [Interp.ok.injEq] at hv
                                  subst hv; simp [RuntimeValue.ValidIn]))
              | (subst hv; simp only [RuntimeValue.ValidIn]))
          | (obtain ⟨_, -, hv⟩ := hok; subst hv
             first
              | (simp only [RuntimeValue.ValidIn]; done)
              | (unfold MemoryState.ptrOfByte
                 split <;> simp [RuntimeValue.ValidIn, Data.Pointer.ValidIn,
                   Data.Pointer.ofAddress, h.nonempty])))

/-- Address arithmetic keeps the assembly relation: both sides move by the same amount. -/
theorem Data.Pointer.isRefinedByIn_addOffset {mem : MemoryState}
    {p q : Data.Pointer} (hpq : p.isRefinedByIn mem q) (n : Nat) :
    Data.Pointer.isRefinedByIn mem { p with offset := UInt64.ofNat (p.offset.toNat + n) }
      { q with offset := UInt64.ofNat (q.offset.toNat + n) } := by
  obtain ⟨hp, hpq⟩ := hpq
  refine ⟨hp, ?_⟩
  rcases hpq with rfl | ⟨hw, rfl⟩
  · exact .inl rfl
  · refine .inr ⟨hw, ?_⟩
    simp only [Data.Pointer.ofAddress, MemoryState.address, Array.getElem?_eq_getElem hp.1,
      Option.map_some, Option.getD_some, Data.Pointer.mk.injEq, true_and, and_true]
    rw [← UInt64.toNat_inj]
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat']
    omega

/-! ## The pointer opcodes in either mode -/

/-- Two interpretations refine when their first steps do, and their continuations do from
related results. -/
theorem Interp.isRefinedBy_bind {α α' β β' : Type} {R : α → α' → Prop} {S : β → β' → Prop}
    {x : Interp α} {y : Interp α'} {f : α → Interp β} {g : α' → Interp β'}
    (hxy : Interp.isRefinedBy R x y) (hfg : ∀ a b, R a b → Interp.isRefinedBy S (f a) (g b)) :
    Interp.isRefinedBy S (x >>= f) (y >>= g) := by
  cases x <;> cases y <;> simp only [Interp.isRefinedBy, Interp.bind_ok, Interp.bind_ub,
    Interp.bind_fail] at hxy ⊢ <;> first | trivial | exact hxy.elim | exact hfg _ _ hxy

/-- An interpretation refines itself when each of its results relates to itself. -/
theorem Interp.isRefinedBy_refl_of_ok {α : Type} {R : α → α → Prop} {x : Interp α}
    (h : ∀ a, x = .ok a → R a a) : Interp.isRefinedBy R x x := by
  cases x <;> simp_all [Interp.isRefinedBy]

/-- Poison is refined by any pointer, in either mode. -/
theorem RuntimeValue.addr_poison_isRefinedBy {m : RefinementMode} {t : Data.LLVM.Ptr} :
    RuntimeValue.addr .poison ⊒[m] RuntimeValue.addr t := by
  cases m <;> simp [RuntimeValue.isRefinedBy, Data.LLVM.Ptr.isRefinedByIn]

/-- Address arithmetic keeps refinement of pointers, in either mode. -/
theorem RuntimeValue.addr_addOffset_isRefinedBy {m : RefinementMode} {p q : Data.Pointer}
    (h : RuntimeValue.addr (.val p) ⊒[m] RuntimeValue.addr (.val q)) (n : Nat) :
    RuntimeValue.addr (.val { p with offset := UInt64.ofNat (p.offset.toNat + n) }) ⊒[m]
      RuntimeValue.addr (.val { q with offset := UInt64.ofNat (q.offset.toNat + n) }) := by
  cases m
  · simp only [RuntimeValue.isRefinedBy, Data.LLVM.Ptr.isRefinedBy] at h ⊢
    rw [h]
  · simp only [RuntimeValue.isRefinedBy, Data.LLVM.Ptr.isRefinedByIn] at h ⊢
    exact Data.Pointer.isRefinedByIn_addOffset h n

/-- A pointer cast from an integer keeps refinement, in either mode: it names the null object. -/
theorem MemoryState.ptrFromInt_isRefinedBy_of {asm : Bool} {mem : MemoryState}
    (hwf : RefinementMode.Wf asm mem) {x y : Data.LLVM.Int 64} (h : x ⊒ y) :
    RuntimeValue.addr (mem.ptrFromInt x) ⊒[.of asm mem] RuntimeValue.addr (mem.ptrFromInt y) := by
  cases asm
  · simpa [RuntimeValue.isRefinedBy] using MemoryState.ptrFromInt_mono h
  · have hl : mem.LayoutWf := by simpa using hwf
    cases x <;> cases y <;> simp_all [_root_.isRefinedBy, MemoryState.ptrFromInt,
      RuntimeValue.isRefinedBy, Data.LLVM.Ptr.isRefinedByIn, Data.Pointer.isRefinedByIn,
      Data.Pointer.ValidIn, Data.Pointer.ofAddress, hl.nonempty]

/-- The address of a pointer keeps refinement, in either mode: related pointers share it. -/
theorem MemoryState.intFromPtr_isRefinedBy_of {asm : Bool} {mem : MemoryState}
    (hwf : RefinementMode.Wf asm mem) {p q : Data.LLVM.Ptr}
    (h : RuntimeValue.addr p ⊒[.of asm mem] RuntimeValue.addr q) :
    mem.intFromPtr p ⊒ mem.intFromPtr q := by
  cases asm
  · exact MemoryState.intFromPtr_mono (by simpa [RuntimeValue.isRefinedBy] using h)
  · have hl : mem.LayoutWf := by simpa using hwf
    simp only [RefinementMode.of_true, RuntimeValue.isRefinedBy] at h
    cases p <;> cases q <;> simp only [Data.LLVM.Ptr.isRefinedByIn] at h
    case val.val a b =>
      simp [MemoryState.intFromPtr, _root_.isRefinedBy, hl.address_eq_of_isRefinedByIn h]
    all_goals simp [MemoryState.intFromPtr, _root_.isRefinedBy]

/-- A load through a refined pointer reads what the source read, in either mode. -/
theorem MemoryState.llvmLoad_isRefinedBy_of {asm : Bool} {mem : MemoryState}
    (hwf : RefinementMode.Wf asm mem) {p q : Data.Pointer}
    (h : RuntimeValue.addr (.val p) ⊒[.of asm mem] RuntimeValue.addr (.val q)) (type : TypeAttr) :
    Interp.isRefinedBy (fun (v w : RuntimeValue) => v ⊒[.of asm mem] w) (mem.llvmLoad p type)
      (mem.llvmLoad q type) := by
  cases asm
  · simp only [RefinementMode.of_false, RuntimeValue.isRefinedBy, Data.LLVM.Ptr.isRefinedBy] at h
    subst h
    exact Interp.isRefinedBy_refl_of_ok fun v _ => RuntimeValue.isRefinedBy_refl v
  · have hl : mem.LayoutWf := by simpa using hwf
    simp only [RefinementMode.of_true, RuntimeValue.isRefinedBy, Data.LLVM.Ptr.isRefinedByIn] at h
    cases hok : mem.llvmLoad p type
    case ok v =>
      obtain ⟨hp, n, obj, hn, hacc⟩ := MemoryState.llvmLoad_ok_access hok
      rw [MemoryState.llvmLoad_eq_of_resolve_eq (hl.resolve_eq_of_isRefinedByIn h hacc hn) hp
        (Data.Pointer.ne_null_of_isRefinedByIn h hp), hok]
      exact RuntimeValue.isRefinedBy_refl_asm (hl.llvmLoad_validIn hok)
    all_goals simp [Interp.isRefinedBy]

/-- The step `alloca` takes: an object the memory did not have, valid in the memory it leaves. -/
theorem OperationResult.isRefinedByFrom_alloc {asm : Bool} {mem mem' : MemoryState}
    (hwf : RefinementMode.Wf asm mem) {size : UInt64} {p : Data.Pointer}
    (halloc : mem.alloc size = .ok (mem', p)) :
    OperationResult.isRefinedByFrom mem asm (#[.addr (.val p)], mem', none)
      (#[.addr (.val p)], mem', none) := by
  refine ⟨⟨RuntimeValue.arrayIsRefinedBy_refl_of ?_, rfl,
    ControlFlowAction.optionIsRefinedBy_refl_of (fun _ => trivial), ?_⟩,
    fun _ => MemoryState.alloc_extends halloc⟩
  · intro _ v hv
    simp only [List.mem_toArray, List.mem_singleton] at hv
    subst hv
    exact ⟨MemoryState.alloc_object_lt halloc, fun h => by
      simp [MemoryState.alloc_not_wild halloc] at h⟩
  · intro ha
    exact (hwf ha).alloc halloc
