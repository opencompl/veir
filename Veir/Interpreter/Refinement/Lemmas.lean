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

/-! ## Least upper bound under refinement -/

section LeastUpperBound
open Veir.Data.LLVM

/-- The least value both refine to, if there is one. -/
@[expose] def RuntimeValue.lub? : RuntimeValue → RuntimeValue → Option RuntimeValue
  | .int w x, .int w' y =>
    if h : w = w' then
      match x.cast h, y with
      | .poison, y => some (.int w' y)
      | x, .poison => some (.int w' x)
      | .val a, .val b => if a = b then some (.int w' (.val a)) else none
    else none
  | .byte w x, .byte w' y =>
    if h : w = w' then ((x.cast h).lub? y).map (.byte w') else none
  | .addr p, .addr q =>
    match p, q with
    | .poison, q => some (.addr q)
    | p, .poison => some (.addr p)
    | .val a, .val b => if a = b then some (.addr (.val a)) else none
  | c, d => if c = d then some c else none

/-- `RuntimeValue.lub?` is an upper bound: what it returns refines both values. -/
theorem RuntimeValue.lub?_isRefinedBy {c d m : RuntimeValue} (h : c.lub? d = some m) :
    c ⊒ m ∧ d ⊒ m := by
  cases c <;> cases d <;> simp only [RuntimeValue.lub?] at h
  case int.int w x w' y =>
    split at h
    · next hw =>
      subst hw
      simp only [Data.LLVM.Int.cast_self] at h
      split at h <;> (try split at h) <;> cases h <;>
        simp_all [RuntimeValue.isRefinedBy, _root_.isRefinedBy_eq, Data.LLVM.Int.cast_self]
    · cases h
  case byte.byte w x w' y =>
    split at h
    · next hw =>
      subst hw
      simp only [Byte.cast_self, Option.map_eq_some_iff] at h
      obtain ⟨m, hm, rfl⟩ := h
      obtain ⟨hx, hy⟩ := Byte.lub?_isRefinedBy hm
      exact ⟨⟨rfl, by simpa using hx⟩, ⟨rfl, by simpa using hy⟩⟩
    · cases h
  case addr.addr p q =>
    split at h <;> (try split at h) <;> cases h <;>
      simp_all [RuntimeValue.isRefinedBy] <;> split <;> simp_all
  all_goals
    split at h
    · next he =>
      cases h; cases he <;>
        exact ⟨RuntimeValue.isRefinedBy_refl _, RuntimeValue.isRefinedBy_refl _⟩
    · cases h

/--
`RuntimeValue.lub?` is the least upper bound: if some value refines both, `lub?` returns a
value below it.
-/
theorem RuntimeValue.lub?_least {c d e : RuntimeValue} (hc : c ⊒ e) (hd : d ⊒ e) :
    ∃ m, c.lub? d = some m ∧ m ⊒ e := by
  cases c <;> cases d <;> cases e <;> simp only [RuntimeValue.isRefinedBy] at hc hd <;>
    (try exact hc.elim) <;> (try exact hd.elim)
  case int.int.int w x w' y we z =>
    obtain ⟨rfl, hx⟩ := hc; obtain ⟨rfl, hy⟩ := hd
    simp only [Data.LLVM.Int.cast_self] at hx hy
    cases x <;> cases y <;> cases z <;>
      simp_all [RuntimeValue.lub?, RuntimeValue.isRefinedBy, _root_.isRefinedBy_eq,
        Data.LLVM.Int.cast_self]
  case byte.byte.byte w x w' y we z =>
    obtain ⟨rfl, hx⟩ := hc; obtain ⟨rfl, hy⟩ := hd
    simp only [Byte.cast_self] at hx hy
    obtain ⟨m, hm, hme⟩ := Byte.lub?_least hx hy
    exact ⟨.byte _ m, by simp [RuntimeValue.lub?, hm], rfl, by simpa using hme⟩
  case addr.addr.addr p q r =>
    cases p <;> cases q <;> cases r <;> simp_all [RuntimeValue.lub?, RuntimeValue.isRefinedBy]
  case reg.reg.reg =>
    subst hc; subst hd; exact ⟨_, by simp [RuntimeValue.lub?], RuntimeValue.isRefinedBy_refl _⟩
  case felt.felt.felt =>
    obtain ⟨rfl, rfl⟩ := hc; obtain ⟨rfl, rfl⟩ := hd
    exact ⟨_, by simp [RuntimeValue.lub?], RuntimeValue.isRefinedBy_refl _⟩
  case float.float.float =>
    split at hc <;> split at hd <;> (try exact hc.elim) <;> (try exact hd.elim)
    subst_vars
    exact ⟨_, by simp [RuntimeValue.lub?], RuntimeValue.isRefinedBy_refl _⟩

/-- Two runtime values that refine each other are equal. -/
theorem RuntimeValue.isRefinedBy_antisymm {c d : RuntimeValue} (h₁ : c ⊒ d) (h₂ : d ⊒ c) :
    c = d := by
  cases c <;> cases d <;> simp only [RuntimeValue.isRefinedBy] at h₁ h₂ <;>
    (try exact h₁.elim) <;> (try exact h₂.elim)
  case int.int w x w' y =>
    obtain ⟨rfl, h₁⟩ := h₁; obtain ⟨_, h₂⟩ := h₂
    simp only [Data.LLVM.Int.cast_self] at h₁ h₂
    cases x <;> cases y <;> simp_all [_root_.isRefinedBy_eq]
  case byte.byte w x w' y =>
    obtain ⟨rfl, h₁⟩ := h₁; obtain ⟨_, h₂⟩ := h₂
    simp only [Byte.cast_self] at h₁ h₂
    rw [Byte.isRefinedBy_antisymm h₁ h₂]
  case addr.addr p q => cases p <;> cases q <;> simp_all
  case reg.reg => rw [h₁]
  case felt.felt => obtain ⟨rfl, rfl⟩ := h₁; rfl
  case float.float =>
    split at h₁ <;> (try exact h₁.elim)
    subst_vars; rfl

end LeastUpperBound
