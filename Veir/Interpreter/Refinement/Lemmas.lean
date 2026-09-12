module

public import Veir.Interpreter.Refinement.Basic

import all Veir.Interpreter.Refinement.Basic

public section

namespace Veir
open Veir.Data

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
theorem MemoryByte.isRefinedBy_refl (b : MemoryByte) : b ⊒ b := by
  cases b <;> simp only [isRefinedBy, and_self]
  bv_decide

@[simp, grind .]
theorem MemoryObject.isRefinedBy_refl (m : MemoryObject) :
    m ⊒ m :=
  ⟨rfl, rfl, fun _ => MemoryByte.isRefinedBy_refl _⟩

@[simp, grind .]
theorem MemoryState.isRefinedBy_refl (m : MemoryState) :
    m ⊒ m :=
  ⟨rfl, fun _ => MemoryObject.isRefinedBy_refl _⟩

@[simp, grind .]
theorem RuntimeValue.isRefinedByUnder_id_refl (v : RuntimeValue) :
    RuntimeValue.isRefinedByUnder id v v := by
  cases v <;> simp [RuntimeValue.isRefinedByUnder]

@[simp, grind .]
theorem RuntimeValue.arrayIsRefinedByUnder_id_refl (a : Array RuntimeValue) :
    RuntimeValue.arrayIsRefinedByUnder id a a := by
  simp [RuntimeValue.arrayIsRefinedByUnder]

@[simp, grind .]
theorem MemoryByte.isRefinedByUnder_id_refl (b : MemoryByte) :
    MemoryByte.isRefinedByUnder id b b := by
  cases b <;> simp only [isRefinedByUnder, id, and_self]
  bv_decide

@[simp, grind .]
theorem MemoryObject.isRefinedByUnder_id_refl (m : MemoryObject) :
    MemoryObject.isRefinedByUnder id m m :=
  ⟨rfl, rfl, id, fun _ => MemoryByte.isRefinedByUnder_id_refl _⟩

/-- Under the identity renaming, value refinement is the plain one. -/
@[simp, grind =]
theorem RuntimeValue.isRefinedByUnder_id_iff {s t : RuntimeValue} :
    RuntimeValue.isRefinedByUnder id s t ↔ s ⊒ t := by
  cases s <;> cases t <;> simp only [RuntimeValue.isRefinedByUnder, RuntimeValue.isRefinedBy, id]
  constructor
  · rintro ⟨h1, h2⟩
    cases ‹Pointer›; cases ‹Pointer›
    simp_all
  · rintro rfl
    exact ⟨rfl, rfl⟩

@[simp, grind =]
theorem RuntimeValue.arrayIsRefinedByUnder_id_iff {a b : Array RuntimeValue} :
    RuntimeValue.arrayIsRefinedByUnder id a b ↔ a ⊒ b := by
  simp [RuntimeValue.arrayIsRefinedByUnder, RuntimeValue.arrayIsRefinedBy]

/-- Equal final memories with refining results refine as function results, under the identity renaming. -/
theorem FunctionResult.isRefinedBy_of_memory_eq {init mem : MemoryState} {vs vs' : Array RuntimeValue}
    (h : vs ⊒ vs') : FunctionResult.isRefinedBy init (mem, vs) (mem, vs') :=
  ⟨id, fun _ _ => rfl, fun _ h => h,
    fun i hi _ => ⟨i, hi, rfl, MemoryObject.isRefinedByUnder_id_refl _⟩,
    RuntimeValue.arrayIsRefinedByUnder_id_iff.mpr h⟩

@[simp, grind .]
theorem FunctionResult.isRefinedBy_refl (init : MemoryState) (r : MemoryState × Array RuntimeValue) :
    FunctionResult.isRefinedBy init r r :=
  ⟨id, fun _ _ => rfl, fun _ h => h,
    fun i hi _ => ⟨i, hi, rfl, MemoryObject.isRefinedByUnder_id_refl _⟩,
    RuntimeValue.arrayIsRefinedByUnder_id_refl _⟩

@[simp, grind .]
theorem Interp.isRefinedBy_refl_of_ne_fail {α : Type} {R : α → α → Prop}
    (hR : ∀ a, R a a) (x : Interp α) (neFail : x ≠ .fail) : Interp.isRefinedBy R x x := by
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

/-! ## Transitivity -/

theorem RuntimeValue.isRefinedBy_trans {v₁ v₂ v₃ : RuntimeValue}
    (h12 : v₁ ⊒ v₂) (h23 : v₂ ⊒ v₃) : v₁ ⊒ v₃ := by
  cases v₁ <;>
    grind [RuntimeValue.isRefinedBy, isRefinedBy_trans,
      cases RuntimeValue, LLVM.Byte.isRefinedBy_trans]

theorem MemoryByte.isRefinedBy_trans {b1 b2 b3 : MemoryByte}
    (h12 : b1 ⊒ b2) (h23 : b2 ⊒ b3) : b1 ⊒ b3 := by
  cases b1 <;> cases b2 <;> cases b3 <;> simp only [isRefinedBy] at * <;> try grind
  all_goals bv_decide

theorem MemoryObject.isRefinedBy_trans {m1 m2 m3 : MemoryObject}
    (h12 : m1 ⊒ m2) (h23 : m2 ⊒ m3) : m1 ⊒ m3 :=
  ⟨h12.1.trans h23.1, h12.2.1.trans h23.2.1,
    fun i => MemoryByte.isRefinedBy_trans (h12.2.2 i) (h23.2.2 i)⟩

theorem MemoryState.isRefinedBy_trans {m1 m2 m3 : MemoryState}
    (h12 : m1 ⊒ m2) (h23 : m2 ⊒ m3) : m1 ⊒ m3 :=
  ⟨h12.1.trans h23.1, fun i => MemoryObject.isRefinedBy_trans (h12.2 i) (h23.2 i)⟩

theorem RuntimeValue.arrayIsRefinedBy_trans {a b c : Array RuntimeValue}
    (h12 : a ⊒ b) (h23 : b ⊒ c) : a ⊒ c := by
  grind [RuntimeValue.arrayIsRefinedBy, RuntimeValue.isRefinedBy_trans]

theorem RuntimeValue.isRefinedByUnder_trans {f g : Nat → Nat} {v₁ v₂ v₃ : RuntimeValue}
    (h12 : RuntimeValue.isRefinedByUnder f v₁ v₂) (h23 : RuntimeValue.isRefinedByUnder g v₂ v₃) :
    RuntimeValue.isRefinedByUnder (fun j => f (g j)) v₁ v₃ := by
  cases v₁ <;> cases v₂ <;> cases v₃ <;>
    simp only [RuntimeValue.isRefinedByUnder] at * <;>
    grind [RuntimeValue.isRefinedBy, RuntimeValue.isRefinedBy_trans]

theorem RuntimeValue.arrayIsRefinedByUnder_trans {f g : Nat → Nat} {a b c : Array RuntimeValue}
    (h12 : RuntimeValue.arrayIsRefinedByUnder f a b) (h23 : RuntimeValue.arrayIsRefinedByUnder g b c) :
    RuntimeValue.arrayIsRefinedByUnder (fun j => f (g j)) a c := by
  grind [RuntimeValue.arrayIsRefinedByUnder, RuntimeValue.isRefinedByUnder_trans]

theorem MemoryByte.isRefinedByUnder_trans {f g : Nat → Nat} {b₁ b₂ b₃ : MemoryByte}
    (h12 : MemoryByte.isRefinedByUnder f b₁ b₂) (h23 : MemoryByte.isRefinedByUnder g b₂ b₃) :
    MemoryByte.isRefinedByUnder (fun j => f (g j)) b₁ b₃ := by
  cases b₁ <;> cases b₂ <;> cases b₃ <;> simp only [isRefinedByUnder] at * <;> try grind
  all_goals bv_decide

theorem MemoryObject.isRefinedByUnder_trans {f g : Nat → Nat} {m₁ m₂ m₃ : MemoryObject}
    (h12 : MemoryObject.isRefinedByUnder f m₁ m₂) (h23 : MemoryObject.isRefinedByUnder g m₂ m₃) :
    MemoryObject.isRefinedByUnder (fun j => f (g j)) m₁ m₃ :=
  ⟨h12.1.trans h23.1, h12.2.1.trans h23.2.1, fun h => h23.2.2.1 (h12.2.2.1 h),
    fun i => MemoryByte.isRefinedByUnder_trans (h12.2.2.2 i) (h23.2.2.2 i)⟩

theorem FunctionResult.isRefinedBy_trans {init : MemoryState}
    {r₁ r₂ r₃ : MemoryState × Array RuntimeValue}
    (h12 : FunctionResult.isRefinedBy init r₁ r₂) (h23 : FunctionResult.isRefinedBy init r₂ r₃) :
    FunctionResult.isRefinedBy init r₁ r₃ := by
  obtain ⟨f, hfId, hfLocal, hfObj, hfVals⟩ := h12
  obtain ⟨g, hgId, hgLocal, hgObj, hgVals⟩ := h23
  refine ⟨fun j => f (g j), ?_, ?_, ?_, RuntimeValue.arrayIsRefinedByUnder_trans hfVals hgVals⟩
  · intro i hi
    show f (g i) = i
    rw [hgId i hi, hfId i hi]
  · intro j hj
    show init.objects.size ≤ f (g j)
    exact hfLocal _ (hgLocal j hj)
  · intro i hi hObs
    obtain ⟨j, hj, hfj, hObj12⟩ := hfObj i hi hObs
    /- `j` is observable in `r₂`: it is a pre-existing object, or it inherited the escape. -/
    have hObs2 : r₂.1.Observable init.objects.size j := by
      rcases hObs with hlt | hEsc
      · left
        rcases Nat.lt_or_ge j init.objects.size with hj' | hj'
        · exact hj'
        · have := hfLocal j hj'
          omega
      · right
        exact hObj12.2.2.1 (by simpa [hfj] using hEsc)
    obtain ⟨k, hk, hgk, hObj23⟩ := hgObj j hj hObs2
    exact ⟨k, hk, by simp [hgk, hfj], MemoryObject.isRefinedByUnder_trans hObj12 hObj23⟩

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

/-- A runtime value `tv` that refines an address runtime value `v` is equal to it. -/
theorem RuntimeValue.addr_of_isRefinedBy {v : Pointer} {tv : RuntimeValue}
    (h : RuntimeValue.addr v ⊒ tv) :
    tv = RuntimeValue.addr v := by
  cases tv <;> grind [RuntimeValue.isRefinedBy]

/-- A runtime value `tv` that refines a register runtime value `v` is equal to it. -/
theorem RuntimeValue.reg_of_isRefinedBy {v : Data.RISCV.Reg} {tv : RuntimeValue}
    (h : RuntimeValue.reg v ⊒ tv) :
    tv = RuntimeValue.reg v := by
  cases tv <;> grind [RuntimeValue.isRefinedBy]

/-! ## Interp refinements -/

/-- `fail` is refined by any value. -/
@[simp, grind .]
theorem Interp.isRefinedBy_fail_target :
    Interp.isRefinedBy R .fail target := by
  simp [Interp.isRefinedBy]

/-- `ub` is refined by any value. -/
@[simp, grind .]
theorem Interp.isRefinedBy_ub_target :
    Interp.isRefinedBy R (.ub) target := by
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
