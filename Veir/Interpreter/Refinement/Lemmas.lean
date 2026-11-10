module

public import Veir.Interpreter.Refinement.Basic

import all Veir.Interpreter.Refinement.Basic
import all Veir.Data.LLVM.Byte.Basic
import Veir.Data.LLVM.Ptr.Lemmas

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
theorem MemoryByte.isRefinedBy_refl (b : MemoryByte) : b ⊒ b := by
  simp only [MemoryByte.isRefinedBy]
  bv_normalize
  grind

@[simp, grind .]
theorem MemoryState.isRefinedBy_refl (m : MemoryState) :
    m ⊒ m :=
  ⟨⟨rfl, fun _ => MemoryByte.isRefinedBy_refl _⟩, rfl⟩

theorem OperationResult.isRefinedBy_def
    {source target : Array RuntimeValue × MemoryState × Option ControlFlowAction} :
    OperationResult.isRefinedBy source target ↔
      source.1 ⊒ target.1 ∧ source.2.1 ⊒ target.2.1 ∧
        ControlFlowAction.optionIsRefinedBy source.2.2 target.2.2 := Iff.rfl

theorem MemoryState.isRefinedBy_def {source target : MemoryState} :
    source ⊒ target ↔ (source.objects = target.objects ∧
      ∀ addr, source.byte addr ⊒ target.byte addr) ∧ source.globals = target.globals := Iff.rfl

/-- Refinement preserves memory-object identities and layout. -/
theorem MemoryState.isRefinedBy.objects_eq {source target : MemoryState}
    (refines : source ⊒ target) : source.objects = target.objects := refines.1.1

/-- Refinement preserves the symbol-to-object table. -/
theorem MemoryState.isRefinedBy.globals_eq {source target : MemoryState}
    (refines : source ⊒ target) : source.globals = target.globals := refines.2

/-- Each stored byte becomes at least as defined. -/
theorem MemoryState.isRefinedBy.byte_refines {source target : MemoryState}
    (refines : source ⊒ target) (address : UInt64) : source.byte address ⊒ target.byte address :=
  refines.1.2 address

/-- Exact memory agreement is a special case of memory refinement. -/
theorem MemoryState.isRefinedBy_of_eq {source target : MemoryState} (same : source = target) : source ⊒ target := by
  subst target
  exact MemoryState.isRefinedBy_refl source

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
theorem VariableState.isRefinedByAt_refl
    {ctx : WfIRContext OpInfo} (state : VariableState ctx) (point : RefinementPoint)
    (pointIn : point.InBounds ctx.raw) :
    state.isRefinedByAt state id point point pointIn pointIn := by
  grind [VariableState.isRefinedByAt]

@[simp, grind .]
theorem InterpreterState.isRefinedByAt_refl
    {ctx : WfIRContext OpInfo} (state : InterpreterState ctx) (point : RefinementPoint)
    (pointIn : point.InBounds ctx.raw) :
    state.isRefinedByAt state id point point pointIn pointIn :=
  ⟨MemoryState.isRefinedBy_refl _, VariableState.isRefinedByAt_refl _ _ pointIn⟩

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
  bv_normalize
  grind

theorem MemoryState.isRefinedBy_trans {m1 m2 m3 : MemoryState}
    (h12 : m1 ⊒ m2) (h23 : m2 ⊒ m3) : m1 ⊒ m3 :=
  ⟨⟨h12.1.1.trans h23.1.1, fun addr => MemoryByte.isRefinedBy_trans (h12.1.2 addr) (h23.1.2 addr)⟩,
    h12.2.trans h23.2⟩

theorem RuntimeValue.arrayIsRefinedBy_trans {a b c : Array RuntimeValue}
    (h12 : a ⊒ b) (h23 : b ⊒ c) : a ⊒ c := by
  grind [RuntimeValue.arrayIsRefinedBy, RuntimeValue.isRefinedBy_trans]

theorem FunctionResult.isRefinedBy_trans {r₁ r₂ r₃ : MemoryState × Array RuntimeValue}
    (h12 : r₁ ⊒ r₂) (h23 : r₂ ⊒ r₃) : r₁ ⊒ r₃ := by
  exact ⟨MemoryState.isRefinedBy_trans h12.1 h23.1, RuntimeValue.arrayIsRefinedBy_trans h12.2 h23.2⟩

theorem ControlFlowAction.isRefinedBy_trans {a b c : ControlFlowAction}
    (ab : a ⊒ b) (bc : b ⊒ c) : a ⊒ c := by
  cases a <;> cases b <;> cases c <;>
    simp only [ControlFlowAction.isRefinedBy] at ab bc ⊢ <;>
    grind [RuntimeValue.arrayIsRefinedBy_trans]

theorem ControlFlowAction.optionIsRefinedBy_trans {a b c : Option ControlFlowAction}
    (ab : ControlFlowAction.optionIsRefinedBy a b)
    (bc : ControlFlowAction.optionIsRefinedBy b c) :
    ControlFlowAction.optionIsRefinedBy a c := by
  cases a <;> cases b <;> cases c <;>
    simp_all only [ControlFlowAction.optionIsRefinedBy] <;>
    grind [ControlFlowAction.isRefinedBy_trans]

/-- Operation-result refinement composes through values, memory, and control flow. -/
theorem OperationResult.isRefinedBy_trans
    {a b c : Array RuntimeValue × MemoryState × Option ControlFlowAction}
    (ab : OperationResult.isRefinedBy a b) (bc : OperationResult.isRefinedBy b c) :
    OperationResult.isRefinedBy a c :=
  ⟨RuntimeValue.arrayIsRefinedBy_trans ab.1 bc.1,
    MemoryState.isRefinedBy_trans ab.2.1 bc.2.1,
    ControlFlowAction.optionIsRefinedBy_trans ab.2.2 bc.2.2⟩

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

/-- Two bytes of a width refine as runtime values as they refine as bytes. -/
theorem RuntimeValue.byte_isRefinedBy_byte {bw : Nat} {b b' : Data.LLVM.Byte bw} :
    RuntimeValue.byte bw b ⊒ RuntimeValue.byte bw b' ↔ b ⊒ b' := by
  simp [RuntimeValue.isRefinedBy, Data.LLVM.Byte.cast]

/-- A runtime value `tv` that refines a float runtime value `v` is equal to it. -/
theorem RuntimeValue.float_of_isRefinedBy {ty : FloatType} {v : Data.Float.FloatValue ty.format}
    {tv : RuntimeValue}
    (h : RuntimeValue.float ty v ⊒ tv) :
    tv = RuntimeValue.float ty v := by
  cases tv <;> grind [RuntimeValue.isRefinedBy]

/-- A non-poison pointer value is refined only by itself. -/
theorem RuntimeValue.addr_val_isRefinedBy_iff {p : Data.Pointer} {tv : RuntimeValue} :
    RuntimeValue.addr (.val p) ⊒ tv ↔ tv = RuntimeValue.addr (.val p) := by
  cases tv <;> simp only [RuntimeValue.isRefinedBy, reduceCtorEq, RuntimeValue.addr.injEq]
  exact Data.LLVM.Ptr.val_isRefinedBy_iff

/-- A non-poison integer value is refined only by itself. -/
@[simp]
theorem RuntimeValue.int_val_isRefinedBy_iff {bw : Nat} {v : BitVec bw} {tv : RuntimeValue} :
    RuntimeValue.int bw (.val v) ⊒ tv ↔ tv = RuntimeValue.int bw (.val v) := by
  cases tv <;> grind [RuntimeValue.isRefinedBy, _root_.isRefinedBy_eq, cases Data.LLVM.Int]

/-- A runtime value `tv` that refines a register runtime value `v` is equal to it. -/
theorem RuntimeValue.reg_of_isRefinedBy {v : Data.RISCV.Reg} {tv : RuntimeValue}
    (h : RuntimeValue.reg v ⊒ tv) :
    tv = RuntimeValue.reg v := by
  cases tv <;> grind [RuntimeValue.isRefinedBy]

/-- An array of one value is refined by the arrays of one value that refines it. -/
@[simp]
theorem RuntimeValue.singleton_isRefinedBy_iff {v : RuntimeValue} {b : Array RuntimeValue} :
    #[v] ⊒ b ↔ ∃ w, b = #[w] ∧ v ⊒ w := by
  cases b; grind [arrayIsRefinedBy, List.length_eq_one_iff]

theorem RuntimeValue.cons_isRefinedBy_iff {x : RuntimeValue} {xs b : List RuntimeValue} :
    (x :: xs).toArray ⊒ b.toArray ↔ ∃ y ys, b = y :: ys ∧ x ⊒ y ∧ xs.toArray ⊒ ys.toArray := by
  cases b with
  | nil => simp [arrayIsRefinedBy]
  | cons y ys =>
    rw [arrayIsRefinedBy_cons]
    exact ⟨fun h => ⟨y, ys, rfl, h⟩, by rintro ⟨_, _, he, h⟩; cases he; exact h⟩

theorem RuntimeValue.nil_isRefinedBy_iff {b : List RuntimeValue} :
    ([] : List RuntimeValue).toArray ⊒ b.toArray ↔ b = [] := by
  cases b <;> simp [arrayIsRefinedBy]

/-- An integer is refined by an integer of its width that is the same, unless it is poison. -/
theorem RuntimeValue.int_isRefinedBy_iff {w : Nat} {x : Data.LLVM.Int w} {t : RuntimeValue} :
    .int w x ⊒ t ↔
      ∃ x', t = .int w x' ∧ (x = .poison ∨ ∃ c, x = .val c ∧ x' = .val c) := by
  constructor
  · intro h
    obtain ⟨x', rfl, hx⟩ := int_of_isRefinedBy h
    refine ⟨x', rfl, ?_⟩
    rw [_root_.isRefinedBy_eq] at hx
    cases x <;> cases x' <;> simp_all
  · rintro ⟨x', rfl, rfl | ⟨_, rfl, rfl⟩⟩
    · simp [RuntimeValue.isRefinedBy]
    · exact isRefinedBy_refl _

/-- A pointer is refined only by itself, unless it is poison. -/
theorem RuntimeValue.addr_isRefinedBy_iff {x : Ptr} {t : RuntimeValue} :
    .addr x ⊒ t ↔ ∃ x', t = .addr x' ∧
      (x = .poison ∨ ∃ c, x = .val c ∧ x' = .val c) := by
  cases t <;> simp [RuntimeValue.isRefinedBy] <;> rename_i y <;>
    cases x <;> cases y <;> simp [eq_comm]

theorem RuntimeValue.toList_triple_of_isRefinedBy {a b : Array RuntimeValue} (h : a ⊒ b)
    {x y z : RuntimeValue} (ha : a.toList = [x, y, z]) :
    ∃ x' y' z', b.toList = [x', y', z'] ∧ x ⊒ x' ∧ y ⊒ y' ∧ z ⊒ z' := by
  rw [← Array.toArray_toList (xs := a), ← Array.toArray_toList (xs := b), ha] at h
  simp only [cons_isRefinedBy_iff, nil_isRefinedBy_iff] at h
  grind

/--
A register runtime value can only be refined by itself, so operand arrays that consist purely of
registers are refined only by themselves.
-/
theorem RuntimeValue.eq_of_arrayIsRefinedBy_of_regs {a b : Array RuntimeValue}
    (h : a ⊒ b) (hregs : ∀ v ∈ a, ∃ r, v = .reg r) : b = a := by
  grind [arrayIsRefinedBy, reg_of_isRefinedBy, Array.getElem_mem]

/-- `target`, a refinement of `source`, conforms to every type `source` conforms to. -/
theorem RuntimeValue.Conforms.of_isRefinedBy {source target : RuntimeValue}
    {type : TypeAttr} (hConforms : source.Conforms type) (hRefined : source ⊒ target) :
    target.Conforms type := by
  obtain ⟨attr, hattr⟩ := type
  cases source <;> cases target <;> simp only [RuntimeValue.isRefinedBy] at hRefined <;>
    cases attr <;>
    simp_all only [RuntimeValue.Conforms, Ptr.isRefinedBy, dite_false_right, true_and] <;> grind

/-- A refinement of an array of values conforms to the types the array conforms to. -/
theorem RuntimeValue.ArrayConforms.of_isRefinedBy
    {source target : Array RuntimeValue} {types : Array TypeAttr}
    (hConforms : RuntimeValue.ArrayConforms source types)
    (hRefined : source ⊒ target) : RuntimeValue.ArrayConforms target types := by
  refine ⟨by grind [RuntimeValue.arrayIsRefinedBy, RuntimeValue.ArrayConforms], fun i hi => ?_⟩
  have hi' : i < source.size := by grind [RuntimeValue.arrayIsRefinedBy]
  exact (hConforms.2 i hi').of_isRefinedBy (hRefined.2 i hi')

/-! ## Operand lists

A refinement of an array of integers or pointers keeps its shape, and replaces only poison: every
other value it refines to itself. The lemmas below say so for the operand lists an interpreter
matches on, so that a proof of monotonicity can substitute the operands of the target.
-/

/-- The operands that refine one operand are one operand. -/
theorem RuntimeValue.toList_single_of_isRefinedBy {a b : Array RuntimeValue} (h : a ⊒ b)
    {x : RuntimeValue} (ha : a.toList = [x]) : ∃ y, b.toList = [y] ∧ x ⊒ y := by
  rw [← Array.toArray_toList (xs := a), ← Array.toArray_toList (xs := b), ha] at h
  simp only [cons_isRefinedBy_iff, nil_isRefinedBy_iff] at h
  grind

/-- The operands that refine two operands are two operands. -/
theorem RuntimeValue.toList_pair_of_isRefinedBy {a b : Array RuntimeValue} (h : a ⊒ b)
    {x y : RuntimeValue} (ha : a.toList = [x, y]) :
    ∃ x' y', b.toList = [x', y'] ∧ x ⊒ x' ∧ y ⊒ y' := by
  rw [← Array.toArray_toList (xs := a), ← Array.toArray_toList (xs := b), ha] at h
  simp only [cons_isRefinedBy_iff, nil_isRefinedBy_iff] at h
  grind

theorem RuntimeValue.toList_int1_of_isRefinedBy {a b : Array RuntimeValue} (h : a ⊒ b)
    {x : Data.LLVM.Int w} (ha : a.toList = [.int w x]) :
    ∃ x', b.toList = [.int w x'] ∧ (x = .poison ∨ ∃ c, x = .val c ∧ x' = .val c) := by
  rw [← Array.toArray_toList (xs := a), ← Array.toArray_toList (xs := b), ha] at h
  simp only [cons_isRefinedBy_iff, nil_isRefinedBy_iff, int_isRefinedBy_iff] at h
  grind [cases Data.LLVM.Int]

theorem RuntimeValue.toList_int2_of_isRefinedBy {a b : Array RuntimeValue} (h : a ⊒ b)
    {x : Data.LLVM.Int w} {y : Data.LLVM.Int v} (ha : a.toList = [.int w x, .int v y]) :
    ∃ x' y', b.toList = [.int w x', .int v y'] ∧
      (x = .poison ∨ ∃ c, x = .val c ∧ x' = .val c) ∧
      (y = .poison ∨ ∃ c, y = .val c ∧ y' = .val c) := by
  rw [← Array.toArray_toList (xs := a), ← Array.toArray_toList (xs := b), ha] at h
  simp only [cons_isRefinedBy_iff, nil_isRefinedBy_iff, int_isRefinedBy_iff] at h
  grind [cases Data.LLVM.Int]

theorem RuntimeValue.toList_int3_of_isRefinedBy {a b : Array RuntimeValue} (h : a ⊒ b)
    {x : Data.LLVM.Int w} {y : Data.LLVM.Int v} {z : Data.LLVM.Int u}
    (ha : a.toList = [.int w x, .int v y, .int u z]) :
    ∃ x' y' z', b.toList = [.int w x', .int v y', .int u z'] ∧
      (x = .poison ∨ ∃ c, x = .val c ∧ x' = .val c) ∧
      (y = .poison ∨ ∃ c, y = .val c ∧ y' = .val c) ∧
      (z = .poison ∨ ∃ c, z = .val c ∧ z' = .val c) := by
  rw [← Array.toArray_toList (xs := a), ← Array.toArray_toList (xs := b), ha] at h
  simp only [cons_isRefinedBy_iff, nil_isRefinedBy_iff, int_isRefinedBy_iff] at h
  grind [cases Data.LLVM.Int]

theorem RuntimeValue.toList_addr1_of_isRefinedBy {a b : Array RuntimeValue} (h : a ⊒ b)
    {x : Ptr} (ha : a.toList = [.addr x]) :
    ∃ x', b.toList = [.addr x'] ∧
      (x = .poison ∨ ∃ c, x = .val c ∧ x' = .val c) := by
  rw [← Array.toArray_toList (xs := a), ← Array.toArray_toList (xs := b), ha] at h
  simp only [cons_isRefinedBy_iff, nil_isRefinedBy_iff, addr_isRefinedBy_iff] at h
  grind [cases Ptr]

/-- A refinement of an array refines each of its slices. -/
theorem RuntimeValue.arrayIsRefinedBy_extract {a b : Array RuntimeValue} (h : a ⊒ b)
    (i j : Nat) : a.extract i j ⊒ b.extract i j := by
  obtain ⟨hs, hi⟩ := h
  refine ⟨by simp [hs], fun k hk => ?_⟩
  simp only [Array.size_extract] at hk
  have := hi (i + k) (by omega)
  rw [getElem!_pos a (i + k) (by omega), getElem!_pos b (i + k) (by omega)] at this
  rw [getElem!_pos _ k (by simp; omega), getElem!_pos _ k (by simp; omega)]
  simpa [Array.getElem_extract] using this

/-- A refinement of an array refines each of its suffixes. -/
theorem RuntimeValue.arrayIsRefinedBy_extract_size {a b : Array RuntimeValue} (h : a ⊒ b)
    (i : Nat) : a.extract i a.size ⊒ b.extract i b.size := by
  rw [← h.1]; exact arrayIsRefinedBy_extract h i a.size

theorem RuntimeValue.getElem?_of_arrayIsRefinedBy {a b : Array RuntimeValue} (h : a ⊒ b)
    {i : Nat} {v : RuntimeValue} (ha : a[i]? = some v) :
    ∃ v', b[i]? = some v' ∧ v ⊒ v' := by
  obtain ⟨hs, hi⟩ := h
  have hlt : i < a.size := by grind
  refine ⟨b[i]'(hs ▸ hlt), by simp, ?_⟩
  have := hi i hlt
  simp only [getElem!_pos, hlt, show i < b.size from hs ▸ hlt] at this
  grind

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

/-! ## Binds and loops -/

/-- Binding refined computations to continuations that preserve refinement. -/
theorem Interp.isRefinedBy_bind {α α' β β' : Type} {R : α → α' → Prop}
    {S : β → β' → Prop}
    {x : Interp α} {y : Interp α'} {f : α → Interp β} {g : α' → Interp β'}
    (hxy : Interp.isRefinedBy R x y) (hfg : ∀ a b, R a b → Interp.isRefinedBy S (f a) (g b)) :
    Interp.isRefinedBy S (x >>= f) (y >>= g) := by
  cases x <;> cases y <;> simp_all [Interp.isRefinedBy]

/-- Binding the same computation to continuations that refine. -/
theorem Interp.isRefinedBy_bind_same {α β β' : Type} {R : β → β' → Prop} {x : Interp α}
    {f : α → Interp β} {g : α → Interp β'} (h : ∀ a, Interp.isRefinedBy R (f a) (g a)) :
    Interp.isRefinedBy R (x >>= f) (x >>= g) := by
  cases x <;> simp [h]

/-- Steps of two loops that do the same and whose states are related by `R`. -/
def ForInStep.Rel {β β' : Type} (R : β → β' → Prop) :
    ForInStep β → ForInStep β' → Prop
  | .yield b, .yield b' => R b b'
  | .done b, .done b' => R b b'
  | _, _ => False

@[simp]
theorem ForInStep.rel_yield {β β' : Type} {R : β → β' → Prop} {b : β} {b' : β'} :
    ForInStep.Rel R (.yield b) (.yield b') ↔ R b b' := Iff.rfl

@[simp]
theorem ForInStep.rel_done {β β' : Type} {R : β → β' → Prop} {b : β} {b' : β'} :
    ForInStep.Rel R (.done b) (.done b') ↔ R b b' := Iff.rfl

@[simp]
theorem ForInStep.not_rel_yield_done {β β' : Type} {R : β → β' → Prop} {b : β} {b' : β'} :
    ¬ ForInStep.Rel R (.yield b) (.done b') := id

@[simp]
theorem ForInStep.not_rel_done_yield {β β' : Type} {R : β → β' → Prop} {b : β} {b' : β'} :
    ¬ ForInStep.Rel R (.done b) (.yield b') := id

/-- Two loops over the same list whose steps keep their states related. -/
theorem Interp.forIn_list_isRefinedBy {α β β' : Type} (l : List α) (R : β → β' → Prop)
    (f : α → β → Interp (ForInStep β)) (g : α → β' → Interp (ForInStep β'))
    (hfg : ∀ a b b', R b b' → Interp.isRefinedBy (ForInStep.Rel R) (f a b) (g a b'))
    (init : β) (init' : β') (h : R init init') :
    Interp.isRefinedBy R (forIn l init f) (forIn l init' g) := by
  induction l generalizing init init' with
  | nil => simpa using h
  | cons a l ih =>
    simp only [List.forIn_cons]
    refine Interp.isRefinedBy_bind (hfg a init init' h) ?_
    rintro (b | b) (b' | b') hb <;> simp only [ForInStep.Rel] at hb
    · simpa using hb
    · exact ih _ _ hb

/-- Two loops over the same range whose steps keep their states related. -/
theorem Interp.forIn_range_isRefinedBy {β β' : Type} (r : Std.Legacy.Range)
    (R : β → β' → Prop)
    (f : Nat → β → Interp (ForInStep β)) (g : Nat → β' → Interp (ForInStep β'))
    (hfg : ∀ a b b', R b b' → Interp.isRefinedBy (ForInStep.Rel R) (f a b) (g a b'))
    (init : β) (init' : β') (h : R init init') :
    Interp.isRefinedBy R (forIn r init f) (forIn r init' g) := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  exact Interp.forIn_list_isRefinedBy _ R _ _ (fun a b b' hb => hfg a b b' hb) init init' h

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

/-! ## Greatest lower bound under refinement -/

section GreatestLowerBound
open Veir.Data.LLVM

/-- The least value both refine to, if there is one. -/
@[expose] def RuntimeValue.glb? : RuntimeValue → RuntimeValue → Option RuntimeValue
  | .int w x, .int w' y =>
    if h : w = w' then
      match x.cast h, y with
      | .poison, y => some (.int w' y)
      | x, .poison => some (.int w' x)
      | .val a, .val b => if a = b then some (.int w' (.val a)) else none
    else none
  | .byte w x, .byte w' y =>
    if h : w = w' then ((x.cast h).glb? y).map (.byte w') else none
  | .addr p, .addr q =>
    match p, q with
    | .poison, q => some (.addr q)
    | p, .poison => some (.addr p)
    | .val a, .val b => if a = b then some (.addr (.val a)) else none
  | c, d => if c = d then some c else none

/-- `RuntimeValue.glb?` is a lower bound: what it returns refines both values. -/
theorem RuntimeValue.glb?_isRefinedBy {c d m : RuntimeValue} (h : c.glb? d = some m) :
    c ⊒ m ∧ d ⊒ m := by
  cases c <;> cases d <;> simp only [RuntimeValue.glb?] at h
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
      obtain ⟨hx, hy⟩ := Byte.glb?_isRefinedBy hm
      exact ⟨⟨rfl, by simpa using hx⟩, ⟨rfl, by simpa using hy⟩⟩
    · cases h
  case addr.addr p q =>
    split at h <;> (try split at h) <;> (try split at h) <;> cases h <;>
      simp_all [RuntimeValue.isRefinedBy] <;> (try split) <;> simp_all
  all_goals
    split at h
    · next he =>
      cases h; cases he <;>
        exact ⟨RuntimeValue.isRefinedBy_refl _, RuntimeValue.isRefinedBy_refl _⟩
    · cases h

/--
`RuntimeValue.glb?` is the greatest lower bound: every value that refines both refines what
`glb?` returns.
-/
theorem RuntimeValue.glb?_greatest {c d e : RuntimeValue} (hc : c ⊒ e) (hd : d ⊒ e) :
    ∃ m, c.glb? d = some m ∧ m ⊒ e := by
  cases c <;> cases d <;> cases e <;> simp only [RuntimeValue.isRefinedBy] at hc hd <;>
    (try exact hc.elim) <;> (try exact hd.elim)
  case int.int.int w x w' y we z =>
    obtain ⟨rfl, hx⟩ := hc; obtain ⟨rfl, hy⟩ := hd
    simp only [Data.LLVM.Int.cast_self] at hx hy
    cases x <;> cases y <;> cases z <;>
      simp_all [RuntimeValue.glb?, RuntimeValue.isRefinedBy, _root_.isRefinedBy_eq,
        Data.LLVM.Int.cast_self]
  case byte.byte.byte w x w' y we z =>
    obtain ⟨rfl, hx⟩ := hc; obtain ⟨rfl, hy⟩ := hd
    simp only [Byte.cast_self] at hx hy
    obtain ⟨m, hm, hme⟩ := Byte.glb?_greatest hx hy
    exact ⟨.byte _ m, by simp [RuntimeValue.glb?, hm], rfl, by simpa using hme⟩
  case addr.addr.addr p q r =>
    cases p <;> cases q <;> cases r <;> simp_all [RuntimeValue.glb?, RuntimeValue.isRefinedBy]
  case reg.reg.reg =>
    subst hc; subst hd; exact ⟨_, by simp [RuntimeValue.glb?], RuntimeValue.isRefinedBy_refl _⟩
  case felt.felt.felt =>
    obtain ⟨rfl, rfl⟩ := hc; obtain ⟨rfl, rfl⟩ := hd
    exact ⟨_, by simp [RuntimeValue.glb?], RuntimeValue.isRefinedBy_refl _⟩
  case float.float.float =>
    split at hc <;> split at hd <;> (try exact hc.elim) <;> (try exact hd.elim)
    subst_vars
    exact ⟨_, by simp [RuntimeValue.glb?], RuntimeValue.isRefinedBy_refl _⟩

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
  case addr.addr p q => rw [Data.LLVM.Ptr.isRefinedBy_antisymm h₁ h₂]
  case reg.reg => rw [h₁]
  case felt.felt => obtain ⟨rfl, rfl⟩ := h₁; rfl
  case float.float =>
    split at h₁ <;> (try exact h₁.elim)
    subst_vars; rfl

end GreatestLowerBound
