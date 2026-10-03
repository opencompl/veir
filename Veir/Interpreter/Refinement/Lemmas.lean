module

public import Veir.Interpreter.Refinement.Basic

import all Veir.Interpreter.Refinement.Basic
import all Veir.Interpreter.Memory
import all Veir.Data.Refinement
import all Veir.Data.LLVM.Ptr.Basic
import all Veir.Data.Pointer.Basic
import all Veir.Data.LLVM.Byte.Basic
import Veir.Data.LLVM.Byte.Lemmas

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
theorem MemoryByte.isRefinedBy_refl (b : MemoryByte) : b ⊒ b := by
  simp only [MemoryByte.isRefinedBy]
  bv_decide

@[simp, grind .]
theorem MemoryState.isRefinedBy_refl (m : MemoryState) :
    m ⊒ m :=
  ⟨rfl, fun _ => MemoryByte.isRefinedBy_refl _⟩

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

theorem MemoryByte.isRefinedBy_trans {b1 b2 b3 : MemoryByte}
    (h12 : b1 ⊒ b2) (h23 : b2 ⊒ b3) : b1 ⊒ b3 := by
  simp only [MemoryByte.isRefinedBy] at *
  bv_decide

theorem MemoryState.isRefinedBy_trans {m1 m2 m3 : MemoryState}
    (h12 : m1 ⊒ m2) (h23 : m2 ⊒ m3) : m1 ⊒ m3 :=
  ⟨h12.1.trans h23.1, fun addr => MemoryByte.isRefinedBy_trans (h12.2 addr) (h23.2 addr)⟩

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
  ⟨RuntimeValue.arrayIsRefinedBy_singleton.mpr h, rfl, trivial⟩

/-- Casting an integer to a pointer keeps refinement: poison casts to a poison pointer. -/
theorem Data.LLVM.Ptr.ofInt_mono {x y : Data.LLVM.Int 64} (h : x ⊒ y) :
    Data.LLVM.Ptr.ofInt x ⊒ Data.LLVM.Ptr.ofInt y := by
  cases x <;> cases y <;> simp_all [Data.LLVM.Ptr.ofInt, _root_.isRefinedBy, Data.LLVM.Ptr.isRefinedBy]

/-- The address of a pointer keeps refinement: a poison pointer has a poison address. -/
theorem Data.LLVM.Ptr.toInt_mono {p q : Data.LLVM.Ptr} (h : p ⊒ q) : p.toInt ⊒ q.toInt := by
  cases p <;> cases q <;> simp_all [Data.LLVM.Ptr.toInt, _root_.isRefinedBy, Data.LLVM.Ptr.isRefinedBy]

/-- The bits of a pointer are the bits of its address. -/
theorem Data.LLVM.Ptr.toByte_eq_fromInt (p : Data.LLVM.Ptr) : p.toByte = Data.LLVM.Byte.fromInt p.toInt := by
  cases p <;> simp [Data.LLVM.Ptr.toByte, Data.LLVM.Ptr.toInt, Data.LLVM.Byte.fromInt,
    Data.LLVM.Byte.fromUInt64, Data.LLVM.Byte.fromBitVec, Data.LLVM.Byte.allPoison]

/-- The bits of a pointer keep refinement: a poison pointer has poison bits. -/
theorem Data.LLVM.Ptr.toByte_mono {p q : Data.LLVM.Ptr} (h : p ⊒ q) : p.toByte ⊒ q.toByte := by
  rw [Data.LLVM.Ptr.toByte_eq_fromInt, Data.LLVM.Ptr.toByte_eq_fromInt]
  exact Data.LLVM.Byte.fromInt_mono (Data.LLVM.Ptr.toInt_mono h)

/-! ## Across a step -/

/-- A refinement of interpretations survives weakening the relation on their results. -/
theorem Interp.isRefinedBy_mono {α β : Type} {R R' : α → β → Prop} (hR : ∀ a b, R a b → R' a b)
    {x : Interp α} {y : Interp β} (h : Interp.isRefinedBy R x y) : Interp.isRefinedBy R' x y := by
  cases x <;> cases y <;> simp_all [Interp.isRefinedBy]


/-! ## Assembly mode -/

/-- Refinement is reflexive in either mode. -/
theorem RuntimeValue.isRefinedBy_refl_mode (m : RefinementMode) (v : RuntimeValue) : v ⊒[m] v := by
  cases m
  · exact RuntimeValue.isRefinedBy_refl v
  · cases v <;> grind [RuntimeValue.isRefinedBy, Data.LLVM.Ptr.isRefinedByAsm,
      Data.Pointer.isRefinedByAsm, cases Data.LLVM.Ptr]

theorem RuntimeValue.arrayIsRefinedBy_refl_mode (m : RefinementMode) (a : Array RuntimeValue) :
    a ⊒[m] a :=
  ⟨rfl, fun _ _ => RuntimeValue.isRefinedBy_refl_mode m _⟩

theorem ControlFlowAction.optionIsRefinedBy_refl_mode (m : RefinementMode)
    (cf : Option ControlFlowAction) : ControlFlowAction.optionIsRefinedBy cf cf m := by
  cases cf with
  | none => trivial
  | some cf =>
    cases cf <;> simp [ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy,
      RuntimeValue.arrayIsRefinedBy_refl_mode]

theorem OperationResult.isRefinedBy_refl_mode (asm : Bool)
    (r : Array RuntimeValue × MemoryState × Option ControlFlowAction) :
    OperationResult.isRefinedBy r r asm :=
  ⟨RuntimeValue.arrayIsRefinedBy_refl_mode _ _, rfl, ControlFlowAction.optionIsRefinedBy_refl_mode _ _⟩

theorem Interp.isRefinedBy_refl_operationResult_mode (asm : Bool)
    (x : Interp (Array RuntimeValue × MemoryState × Option ControlFlowAction)) :
    Interp.isRefinedBy (OperationResult.isRefinedBy · · asm) x x := by
  cases x <;> simp [Interp.isRefinedBy, OperationResult.isRefinedBy_refl_mode]

/-- One value, in either mode. -/
theorem OperationResult.isRefinedBy_value_mode {asm : Bool} {v w : RuntimeValue}
    {mem : MemoryState} (h : v ⊒[.of asm] w) :
    OperationResult.isRefinedBy (#[v], mem, none) (#[w], mem, none) asm :=
  ⟨RuntimeValue.arrayIsRefinedBy_singleton.mpr h, rfl, by simp [ControlFlowAction.optionIsRefinedBy]⟩

/-- Related pointers share their address. -/
theorem Data.Pointer.address_eq_of_isRefinedByAsm {p q : Data.Pointer} (hpq : p.isRefinedByAsm q) :
    q.address = p.address := by
  rcases hpq with rfl | ⟨-, h⟩
  · rfl
  · exact h

/-- A pointer survives a round trip through its address in assembly mode. -/
theorem Data.Pointer.isRefinedByAsm_ofAddress {p q : Data.Pointer} (hpq : p.isRefinedByAsm q) :
    p.isRefinedByAsm (Data.Pointer.ofAddress q.address) :=
  .inr ⟨rfl, by simp [Data.Pointer.ofAddress, Data.Pointer.address_eq_of_isRefinedByAsm hpq]⟩

/-- Address arithmetic keeps the assembly relation: both sides move by the same amount. -/
theorem Data.Pointer.isRefinedByAsm_addOffset {p q : Data.Pointer} (hpq : p.isRefinedByAsm q)
    (n : Nat) : Data.Pointer.isRefinedByAsm { p with address := UInt64.ofNat (p.address.toNat + n) }
      { q with address := UInt64.ofNat (q.address.toNat + n) } := by
  rcases hpq with rfl | ⟨hw, h⟩
  · exact .inl rfl
  · exact .inr ⟨hw, by simp [h]⟩

/-- What refines a pointer is a pointer, in either mode. -/
theorem RuntimeValue.exists_addr_of_isRefinedBy {m : RefinementMode} {v : Data.LLVM.Ptr}
    {w : RuntimeValue} (h : RuntimeValue.addr v ⊒[m] w) : ∃ t, w = RuntimeValue.addr t := by
  cases w <;> simp only [RuntimeValue.isRefinedBy] at h <;> first | exact ⟨_, rfl⟩ | exact h.elim

/-- The pointer a source value stands for, as the target holds it. -/
theorem RuntimeValue.addr_val_of_isRefinedBy_of {asm : Bool} {p : Data.Pointer}
    {w : RuntimeValue} (h : RuntimeValue.addr (.val p) ⊒[.of asm] w) :
    ∃ q, w = RuntimeValue.addr (.val q) ∧ (asm = false → q = p) ∧
      (asm = true → p.isRefinedByAsm q) := by
  cases w <;> simp only [RuntimeValue.isRefinedBy] at h <;> try exact h.elim
  rename_i t
  cases asm <;> simp only [RefinementMode.of_false, RefinementMode.of_true] at h <;>
    cases t <;> simp only [Data.LLVM.Ptr.isRefinedBy, Data.LLVM.Ptr.isRefinedByAsm] at h
  · exact ⟨_, rfl, fun _ => h.symm, fun hc => by simp at hc⟩
  · exact ⟨_, rfl, fun hc => by simp at hc, fun _ => h⟩

/-- Poison is refined by any pointer, in either mode. -/
theorem RuntimeValue.addr_poison_isRefinedBy {m : RefinementMode} {t : Data.LLVM.Ptr} :
    RuntimeValue.addr .poison ⊒[m] RuntimeValue.addr t := by
  cases m <;> simp [RuntimeValue.isRefinedBy, Data.LLVM.Ptr.isRefinedByAsm]

/-- Address arithmetic keeps refinement of pointers, in either mode. -/
theorem RuntimeValue.addr_addOffset_isRefinedBy {m : RefinementMode} {p q : Data.Pointer}
    (h : RuntimeValue.addr (.val p) ⊒[m] RuntimeValue.addr (.val q)) (n : Nat) :
    RuntimeValue.addr (.val { p with address := UInt64.ofNat (p.address.toNat + n) }) ⊒[m]
      RuntimeValue.addr (.val { q with address := UInt64.ofNat (q.address.toNat + n) }) := by
  cases m
  · simp only [RuntimeValue.isRefinedBy, Data.LLVM.Ptr.isRefinedBy] at h ⊢
    rw [h]
  · simp only [RuntimeValue.isRefinedBy, Data.LLVM.Ptr.isRefinedByAsm] at h ⊢
    exact Data.Pointer.isRefinedByAsm_addOffset h n

/-- A pointer cast from an integer keeps refinement, in either mode. -/
theorem Data.LLVM.Ptr.ofInt_isRefinedBy {m : RefinementMode} {x y : Data.LLVM.Int 64} (h : x ⊒ y) :
    RuntimeValue.addr (Data.LLVM.Ptr.ofInt x) ⊒[m] RuntimeValue.addr (Data.LLVM.Ptr.ofInt y) := by
  cases m
  · simpa [RuntimeValue.isRefinedBy] using Data.LLVM.Ptr.ofInt_mono h
  · cases x <;> cases y <;> simp_all [_root_.isRefinedBy, Data.LLVM.Ptr.ofInt,
      RuntimeValue.isRefinedBy, Data.LLVM.Ptr.isRefinedByAsm, Data.Pointer.isRefinedByAsm]

/-- The address of a pointer keeps refinement, in either mode: related pointers share it. -/
theorem Data.LLVM.Ptr.toInt_isRefinedBy {m : RefinementMode} {p q : Data.LLVM.Ptr}
    (h : RuntimeValue.addr p ⊒[m] RuntimeValue.addr q) : p.toInt ⊒ q.toInt := by
  cases m
  · exact Data.LLVM.Ptr.toInt_mono (by simpa [RuntimeValue.isRefinedBy] using h)
  · simp only [RuntimeValue.isRefinedBy] at h
    cases p <;> cases q <;> simp only [Data.LLVM.Ptr.isRefinedByAsm] at h
    case val.val a b =>
      simp [Data.LLVM.Ptr.toInt, _root_.isRefinedBy, Data.Pointer.address_eq_of_isRefinedByAsm h]
    all_goals simp [Data.LLVM.Ptr.toInt, _root_.isRefinedBy]

/-- The bits of a pointer keep refinement, in either mode. -/
theorem Data.LLVM.Ptr.toByte_isRefinedBy {m : RefinementMode} {p q : Data.LLVM.Ptr}
    (h : RuntimeValue.addr p ⊒[m] RuntimeValue.addr q) : p.toByte ⊒ q.toByte := by
  rw [Data.LLVM.Ptr.toByte_eq_fromInt, Data.LLVM.Ptr.toByte_eq_fromInt]
  exact Data.LLVM.Byte.fromInt_mono (Data.LLVM.Ptr.toInt_isRefinedBy h)

/-! ## Steps through memory -/

/-- A bind returns a value only when both halves do. -/
theorem Interp.bind_eq_ok_iff {α β : Type} {x : Interp α} {f : α → Interp β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp

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

/--
The access that makes assembly mode work: an access that succeeds through `p`
succeeds through what refines `p`, since a wild pointer at the same address
finds `p`'s object among those that hold the range.
-/
theorem MemoryState.checkAccess_of_isRefinedByAsm {mem : MemoryState} {p q : Data.Pointer}
    (hpq : p.isRefinedByAsm q) {size : UInt64} (hok : mem.checkAccess p size = .ok ()) :
    mem.checkAccess q size = .ok () := by
  rcases hpq with rfl | ⟨hw, ha⟩
  · exact hok
  · simp only [MemoryState.checkAccess, hw, ha, ↓reduceIte]
    by_cases hp : p.wild = true
    · simpa [MemoryState.checkAccess, hp] using hok
    · simp only [MemoryState.checkAccess, hp, Bool.false_eq_true, ↓reduceIte] at hok
      split at hok
      · rename_i obj hobj
        by_cases hsize : size = 0
        · simp [hsize]
        · obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp hobj
          simp only [hsize, false_or] at hok
          split at hok
          · rename_i hholds
            have hany : mem.objects.any (·.holds p.address size.toNat) = true :=
              Array.any_eq_true.mpr ⟨p.object, hi, hholds⟩
            simp [hany]
          · simp at hok
      · simp at hok

/-- Loads read the same bytes through two pointers that refine in assembly mode, once the
source's access succeeds. -/
theorem MemoryState.load_of_isRefinedByAsm {mem : MemoryState} {p q : Data.Pointer}
    (hpq : p.isRefinedByAsm q) {size : UInt64} {bytes : ByteArray}
    (hok : mem.load p size = .ok bytes) : mem.load q size = .ok bytes := by
  simp only [MemoryState.load, Interp.bind_eq_ok_iff] at hok ⊢
  obtain ⟨⟨⟩, hacc, hbytes⟩ := hok
  refine ⟨(), mem.checkAccess_of_isRefinedByAsm hpq hacc, ?_⟩
  rwa [Data.Pointer.address_eq_of_isRefinedByAsm hpq]

theorem MemoryState.loadPoison_of_isRefinedByAsm {mem : MemoryState} {p q : Data.Pointer}
    (hpq : p.isRefinedByAsm q) {size : UInt64} {bytes : ByteArray}
    (hok : mem.loadPoison p size = .ok bytes) : mem.loadPoison q size = .ok bytes := by
  simp only [MemoryState.loadPoison, Interp.bind_eq_ok_iff] at hok ⊢
  obtain ⟨⟨⟩, hacc, hbytes⟩ := hok
  refine ⟨(), mem.checkAccess_of_isRefinedByAsm hpq hacc, ?_⟩
  rwa [Data.Pointer.address_eq_of_isRefinedByAsm hpq]

/-- A pointer related to a non-null pointer is not null. -/
theorem Data.Pointer.ne_null_of_isRefinedByAsm {p q : Data.Pointer} (hpq : p.isRefinedByAsm q)
    (hp : p ≠ .null) : q ≠ .null := by
  rcases hpq with rfl | ⟨hw, -⟩
  · exact hp
  · intro h; subst h; simp [Data.Pointer.null] at hw

/-- A load through a refined pointer reads what the source read, in either mode. -/
theorem MemoryState.llvmLoad_isRefinedBy {asm : Bool} {mem : MemoryState} {p q : Data.Pointer}
    (h : RuntimeValue.addr (.val p) ⊒[.of asm] RuntimeValue.addr (.val q)) (type : TypeAttr) :
    Interp.isRefinedBy (fun (v w : RuntimeValue) => v ⊒[.of asm] w) (mem.llvmLoad p type)
      (mem.llvmLoad q type) := by
  cases asm
  · simp only [RefinementMode.of_false, RuntimeValue.isRefinedBy, Data.LLVM.Ptr.isRefinedBy] at h
    subst h
    exact Interp.isRefinedBy_refl_of_ok fun v _ => RuntimeValue.isRefinedBy_refl v
  · simp only [RefinementMode.of_true, RuntimeValue.isRefinedBy, Data.LLVM.Ptr.isRefinedByAsm] at h
    cases hok : mem.llvmLoad p type
    case ok v =>
      suffices mem.llvmLoad q type = .ok v by
        simp [this, Interp.isRefinedBy, RuntimeValue.isRefinedBy_refl_mode]
      have hq := Data.Pointer.ne_null_of_isRefinedByAsm h
      simp only [MemoryState.llvmLoad] at hok ⊢
      split at hok
      · simp at hok
      · rename_i hp
        split
        · exact absurd ‹q = Data.Pointer.null› (hq hp)
        split at hok
        all_goals first
          | (simp at hok; done)
          | (simp only [MemoryState.hasPoison, MemoryState.loadByte64, Interp.bind_eq_ok_iff]
               at hok ⊢
             first
              | (obtain ⟨b, ⟨ba, hba, ps, hps, hb⟩, hok⟩ := hok
                 exact ⟨b, ⟨ba, mem.load_of_isRefinedByAsm h hba, ps,
                   mem.loadPoison_of_isRefinedByAsm h hps, hb⟩, hok⟩)
              | (obtain ⟨bs, hbs, hok⟩ := hok
                 refine ⟨bs, mem.load_of_isRefinedByAsm h hbs, ?_⟩
                 first
                  | (obtain ⟨ps, hps, hok⟩ := hok
                     exact ⟨ps, mem.loadPoison_of_isRefinedByAsm h hps, hok⟩)
                  | (obtain ⟨b, ⟨ps, hps, hb⟩, hok⟩ := hok
                     exact ⟨b, ⟨ps, mem.loadPoison_of_isRefinedByAsm h hps, hb⟩, hok⟩)
                  | exact hok))
    all_goals simp [Interp.isRefinedBy]
