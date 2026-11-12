module

public import Veir.Interpreter.Lemmas
import Veir.Interpreter.Refinement.Memory

import all Veir.Interpreter.Memory
import all Veir.Dialects.LLVM.OpInfo

public section

/-!
# Monotonicity of the LLVM memory opcodes

The LLVM opcodes that read or write memory are monotone with refined memory
(`InterpretOp'ContextuallyMonotone`): refined operands and refined memory give refined results
and refined memory. Loops over memory, as in `memset`, `memcpy` and `memmove`, keep the two
memories refined step by step.
-/

open Veir.Data

namespace Veir

/-- A result of one value and refined memory. -/
private theorem result_single {v v' : RuntimeValue} {m m' : MemoryState} (hv : v ⊒ v')
    (hm : m ⊒ m') :
    OperationResult.isRefinedBy (#[v], m, none) (#[v'], m', none) :=
  OperationResult.isRefinedBy_def.mpr
    ⟨RuntimeValue.singleton_isRefinedBy_iff.mpr ⟨_, rfl, hv⟩, hm, trivial⟩

/-- A result of no values and refined memory. -/
private theorem result_empty {m m' : MemoryState} (hm : m ⊒ m') :
    OperationResult.isRefinedBy (#[], m, none) (#[], m', none) :=
  OperationResult.isRefinedBy_def.mpr
    ⟨RuntimeValue.arrayIsRefinedBy_refl _, hm, trivial⟩

/-- A computation of memories gives the results without values of its memories. -/
private theorem isRefinedBy_memory_result {s t : Interp MemoryState}
    (h : Interp.isRefinedBy MemoryState.isRefinedBy s t) :
    Interp.isRefinedBy OperationResult.isRefinedBy
      (do let m ← s; pure ((#[] : Array RuntimeValue), m, (none : Option ControlFlowAction)))
      (do let m ← t; pure ((#[] : Array RuntimeValue), m, (none : Option ControlFlowAction))) :=
  Interp.isRefinedBy_bind h fun _ _ hm => by simpa using result_empty hm

/--
`llvm.load` is monotone: a poison pointer is undefined behavior, and a load through a pointer
from refined memory gives a refined value.
-/
instance llvm_contextuallyMonotone_load : InterpretOp'ContextuallyMonotone (.llvm .load) where
  monotone properties resultTypes operands operands' blockOperands mem mem' h hMem := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · next x heq =>
      obtain ⟨x', hT, rfl | ⟨c, rfl, hc⟩⟩ := RuntimeValue.toList_addr1_of_isRefinedBy h heq
      · simp
      obtain ⟨c', rfl, hc'⟩ : ∃ c', x' = .val c' ∧ (c ⊒ c') := by
        rcases hc with rfl | rfl <;> simp
      simp only [hT, Pointer.checkAlignment_of_isRefinedBy hc']
      rcases resultTypes.toList with _ | ⟨type, _ | _⟩
      · simp [liftM]
      · refine Interp.isRefinedBy_bind_same fun _ => ?_
        exact Interp.isRefinedBy_bind (MemoryState.llvmLoad_isRefinedBy_of_refines hMem hc' type)
          fun v v' hv => by simpa using result_single hv hMem
      · simp [liftM]
    · simp [Interp.isRefinedBy]

/-- A step that yields the results of related computations. -/
private theorem yield_isRefinedBy {α α' β β' : Type} {S : α → α' → Prop}
    {R : β → β' → Prop}
    {x : Interp α} {y : Interp α'} {f : α → β} {g : α' → β'}
    (hxy : Interp.isRefinedBy S x y) (hfg : ∀ a b, S a b → R (f a) (g b)) :
    Interp.isRefinedBy (ForInStep.Rel R)
      (do let a ← x; pure (ForInStep.yield (f a)))
      (do let b ← y; pure (ForInStep.yield (g b))) :=
  Interp.isRefinedBy_bind hxy fun a b h => by
    simpa [ForInStep.rel_yield, ForInStep.rel_done] using hfg a b h

/-- `memset` of a refined value into refined memory gives refined memory. -/
theorem MemoryState.memset_isRefinedBy {mem mem' : MemoryState}
    (h : mem ⊒ mem') {p p' : Pointer} (hp : p ⊒ p')
    {v v' : RuntimeValue} (hv : v ⊒ v') (n : Nat) :
    Interp.isRefinedBy MemoryState.isRefinedBy
      (mem.memset p v n) (mem'.memset p' v' n) := by
  unfold MemoryState.memset
  refine Interp.isRefinedBy_bind
    (Interp.forIn_range_isRefinedBy _ _ _ _ (fun i m m' hm => ?_) _ _ h)
    fun m m' hm => by simpa using hm
  exact yield_isRefinedBy (f := id) (g := id)
    (MemoryState.llvmStore_isRefinedBy_of_refines hm (hp.addBytes i) hv)
    fun _ _ h => h

/-- Pushing refined values onto refined arrays gives refined arrays. -/
theorem RuntimeValue.arrayIsRefinedBy_push {a b : Array RuntimeValue} {x y : RuntimeValue}
    (h : a ⊒ b) (hxy : x ⊒ y) : a.push x ⊒ b.push y := by
  obtain ⟨hs, hi⟩ := h
  refine ⟨by simp [hs], fun i hi' => ?_⟩
  simp only [Array.size_push] at hi'
  have hlt' : i < b.size + 1 := by omega
  rw [getElem!_pos (a.push x) i (by simpa using hi'),
    getElem!_pos (b.push y) i (by simpa using hlt'), Array.getElem_push, Array.getElem_push]
  by_cases hlt : i < a.size
  · have := hi i hlt
    rw [getElem!_pos a i hlt, getElem!_pos b i (hs ▸ hlt)] at this
    simpa [hlt, hs ▸ hlt] using this
  · have hlt'' : ¬ i < b.size := hs ▸ hlt
    simpa [hlt, hlt''] using hxy

/-- The elements of refined arrays refine, the default beyond their end included. -/
theorem RuntimeValue.getElem!_of_arrayIsRefinedBy {a b : Array RuntimeValue} (h : a ⊒ b)
    (i : Nat) : a[i]! ⊒ b[i]! := by
  by_cases hlt : i < a.size
  · exact h.2 i hlt
  · rw [getElem!_neg a i hlt, getElem!_neg b i (h.1 ▸ hlt)]
    exact RuntimeValue.isRefinedBy_refl _

/-- `memcpy` in refined memory gives refined memory. -/
theorem MemoryState.memcpy_isRefinedBy {mem mem' : MemoryState}
    (h : mem ⊒ mem') {dst dst' src src' : Pointer}
    (hd : dst ⊒ dst') (hs : src ⊒ src') (n : Nat) :
    Interp.isRefinedBy MemoryState.isRefinedBy
      (mem.memcpy dst src n) (mem'.memcpy dst' src' n) := by
  unfold MemoryState.memcpy
  simp only [hd.address_eq, hs.address_eq]
  split
  · simp
  refine Interp.isRefinedBy_bind
    (Interp.forIn_range_isRefinedBy _ _ _ _ (fun i m m' hm => ?_) _ _ h)
    fun m m' hm => by simpa using hm
  exact Interp.isRefinedBy_bind
    (MemoryState.llvmLoad_isRefinedBy_of_refines hm (hs.addBytes i) _)
    fun v v' hv => yield_isRefinedBy (f := id) (g := id)
      (MemoryState.llvmStore_isRefinedBy_of_refines hm (hd.addBytes i) hv)
      fun _ _ h => h

/-- `memmove` in refined memory gives refined memory. -/
theorem MemoryState.memmove_isRefinedBy {mem mem' : MemoryState}
    (h : mem ⊒ mem') {dst dst' src src' : Pointer}
    (hd : dst ⊒ dst') (hs : src ⊒ src') (n : Nat) :
    Interp.isRefinedBy MemoryState.isRefinedBy
      (mem.memmove dst src n) (mem'.memmove dst' src' n) := by
  unfold MemoryState.memmove
  dsimp only
  refine Interp.isRefinedBy_bind (R := RuntimeValue.arrayIsRefinedBy)
    (Interp.forIn_range_isRefinedBy _ _ _ _ (fun i m m' hm => ?_) _ _ ?_) fun bs bs' hbs => ?_
  · exact yield_isRefinedBy (f := m.push) (g := m'.push)
      (MemoryState.llvmLoad_isRefinedBy_of_refines h (hs.addBytes i) _)
      fun v v' hv => RuntimeValue.arrayIsRefinedBy_push hm hv
  · exact RuntimeValue.arrayIsRefinedBy_refl _
  · refine Interp.isRefinedBy_bind
      (Interp.forIn_range_isRefinedBy _ _ _ _ (fun i m m' hm => ?_) _ _ h)
      fun m m' hm => by simpa using hm
    exact yield_isRefinedBy (f := id) (g := id)
      (MemoryState.llvmStore_isRefinedBy_of_refines hm (hd.addBytes i)
        (RuntimeValue.getElem!_of_arrayIsRefinedBy hbs i))
      fun _ _ h => h

/-- A refinement of a value has its type. -/
theorem RuntimeValue.storedType_eq_of_isRefinedBy {v v' : RuntimeValue} (h : v ⊒ v') :
    v.storedType = v'.storedType := by
  cases v <;> cases v' <;> simp only [RuntimeValue.isRefinedBy] at h
  all_goals first | (obtain ⟨rfl, -⟩ := h; rfl) | rfl

/--
`llvm.store` is monotone: a poison pointer is undefined behavior, a refined value has the same
type and so the same alignment, and storing it into refined memory gives refined memory.
-/
instance llvm_contextuallyMonotone_store : InterpretOp'ContextuallyMonotone (.llvm .store) where
  monotone properties resultTypes operands operands' blockOperands mem mem' h hMem := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · next v x heq =>
      obtain ⟨v', a', hT, hv, ha⟩ := RuntimeValue.toList_pair_of_isRefinedBy h heq
      obtain ⟨x', rfl, rfl | ⟨c, rfl, hc⟩⟩ := RuntimeValue.addr_isRefinedBy_iff.mp ha
      · simp only [hT]; simp
      obtain ⟨c', rfl, hc'⟩ : ∃ c', x' = .val c' ∧ (c ⊒ c') := by
        rcases hc with rfl | rfl <;> simp
      simp only [hT, Pointer.checkAlignment_of_isRefinedBy hc',
        ← RuntimeValue.storedType_eq_of_isRefinedBy hv]
      have hs := MemoryState.llvmStore_isRefinedBy_of_refines hMem hc' hv
      rcases v.storedType with _ | type
      · exact isRefinedBy_memory_result hs
      · exact Interp.isRefinedBy_bind_same fun _ => isRefinedBy_memory_result hs
    · simp [Interp.isRefinedBy]

/-- An allocation in refined memory gives the same pointer and refined memory. -/
theorem MemoryState.alloc_isRefinedBy {mem mem' : MemoryState}
    (h : mem ⊒ mem') (size : UInt64) :
    Interp.isRefinedBy (fun (r r' : MemoryState × Pointer) => r.1 ⊒ r'.1 ∧ r.2 = r'.2)
      (mem.alloc size) (mem'.alloc size) := by
  obtain ⟨⟨hobj, hbytes⟩, hglobals⟩ := MemoryState.isRefinedBy_def.mp h
  have hb : mem.nextBase = mem'.nextBase := by simp [MemoryState.nextBase, hobj]
  unfold MemoryState.alloc
  simp only [hb, hobj]
  split
  · simp
  · simp only [Interp.pure_eq, Interp.isRefinedBy_ok_target_iff, Interp.ok.injEq,
      exists_eq_left', and_true]
    exact MemoryState.isRefinedBy_def.mpr ⟨⟨rfl, hbytes⟩, hglobals⟩

/-- `llvm.mlir.addressof` is monotone: refined memories have the same globals. -/
instance llvm_contextuallyMonotone_mlir__addressof :
    InterpretOp'ContextuallyMonotone (.llvm .mlir__addressof) where
  monotone properties resultTypes operands operands' blockOperands mem mem' h hMem := by
    simp only [interpretOp', Llvm.interpretOp',
      MemoryState.pointerToGlobal_eq_of_isRefinedBy hMem]
    rcases mem'.pointerToGlobal properties.global_name.value with _ | p
    · simp [liftM]
    · simpa using result_single (RuntimeValue.isRefinedBy_refl _) hMem

/--
`llvm.alloca` is monotone: a poison count fails, and an allocation in refined memory gives the
same pointer and refined memory.
-/
instance llvm_contextuallyMonotone_alloca : InterpretOp'ContextuallyMonotone (.llvm .alloca) where
  monotone properties resultTypes operands operands' blockOperands mem mem' h hMem := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · next w c heq =>
      obtain ⟨x', hT, hx⟩ := RuntimeValue.toList_int1_of_isRefinedBy h heq
      obtain rfl : x' = .val c := by
        rcases hx with hx | ⟨_, hx, rfl⟩ <;> cases hx; rfl
      simp only [hT]
      refine Interp.isRefinedBy_bind_same fun _ => Interp.isRefinedBy_bind_same fun _ => ?_
      refine Interp.isRefinedBy_bind (MemoryState.alloc_isRefinedBy hMem _) ?_
      rintro ⟨m, q⟩ ⟨m', q'⟩ ⟨hm, rfl⟩
      simpa using result_single (RuntimeValue.isRefinedBy_refl _) hm
    · simp [Interp.isRefinedBy]

/--
`llvm.intr.memset` is monotone: a poison length or pointer is undefined behavior, and the same
length and pointer set refined memory to a refined value.
-/
instance llvm_contextuallyMonotone_intr__memset :
    InterpretOp'ContextuallyMonotone (.llvm .intr__memset) where
  monotone properties resultTypes operands operands' blockOperands mem mem' h hMem := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · next dst v w len heq =>
      obtain ⟨a', v', l', hT, ha, hv, hl⟩ := RuntimeValue.toList_triple_of_isRefinedBy h heq
      obtain ⟨d', rfl, hd⟩ := RuntimeValue.addr_isRefinedBy_iff.mp ha
      obtain ⟨l', rfl, hlen⟩ := RuntimeValue.int_isRefinedBy_iff.mp hl
      simp only [hT]
      rcases hlen with rfl | ⟨c, rfl, rfl⟩
      · simp
      dsimp only
      split
      · exact Interp.isRefinedBy_ok_target_iff.mpr ⟨_, rfl, result_empty hMem⟩
      rcases hd with rfl | ⟨q, rfl, hq⟩
      · simp
      obtain ⟨q', rfl, hq'⟩ : ∃ q', d' = .val q' ∧ (q ⊒ q') := by
        rcases hq with rfl | rfl <;> simp
      exact isRefinedBy_memory_result (MemoryState.memset_isRefinedBy hMem hq' hv _)
    · simp [Interp.isRefinedBy]

/--
`llvm.intr.memcpy` is monotone: a poison length or pointer is undefined behavior, and copying
in refined memory gives refined memory.
-/
instance llvm_contextuallyMonotone_intr__memcpy :
    InterpretOp'ContextuallyMonotone (.llvm .intr__memcpy) where
  monotone properties resultTypes operands operands' blockOperands mem mem' h hMem := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · next dst src w len heq =>
      obtain ⟨a', b', l', hT, ha, hb, hl⟩ := RuntimeValue.toList_triple_of_isRefinedBy h heq
      obtain ⟨d', rfl, hd⟩ := RuntimeValue.addr_isRefinedBy_iff.mp ha
      obtain ⟨s', rfl, hs⟩ := RuntimeValue.addr_isRefinedBy_iff.mp hb
      obtain ⟨l', rfl, hlen⟩ := RuntimeValue.int_isRefinedBy_iff.mp hl
      simp only [hT]
      rcases hlen with rfl | ⟨c, rfl, rfl⟩
      · simp
      dsimp only
      split
      · exact Interp.isRefinedBy_ok_target_iff.mpr ⟨_, rfl, result_empty hMem⟩
      rcases hd with rfl | ⟨p, rfl, hp⟩
      · simp
      rcases hs with rfl | ⟨q, rfl, hq⟩
      · simp
      obtain ⟨p', rfl, hp'⟩ : ∃ p', d' = .val p' ∧ (p ⊒ p') := by
        rcases hp with rfl | rfl <;> simp
      obtain ⟨q', rfl, hq'⟩ : ∃ q', s' = .val q' ∧ (q ⊒ q') := by
        rcases hq with rfl | rfl <;> simp
      simp only [ite_true]
      exact isRefinedBy_memory_result (MemoryState.memcpy_isRefinedBy hMem hp' hq' _)
    · simp [Interp.isRefinedBy]

/--
`llvm.intr.memmove` is monotone: a poison length or pointer is undefined behavior, and moving
in refined memory gives refined memory.
-/
instance llvm_contextuallyMonotone_intr__memmove :
    InterpretOp'ContextuallyMonotone (.llvm .intr__memmove) where
  monotone properties resultTypes operands operands' blockOperands mem mem' h hMem := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · next dst src w len heq =>
      obtain ⟨a', b', l', hT, ha, hb, hl⟩ := RuntimeValue.toList_triple_of_isRefinedBy h heq
      obtain ⟨d', rfl, hd⟩ := RuntimeValue.addr_isRefinedBy_iff.mp ha
      obtain ⟨s', rfl, hs⟩ := RuntimeValue.addr_isRefinedBy_iff.mp hb
      obtain ⟨l', rfl, hlen⟩ := RuntimeValue.int_isRefinedBy_iff.mp hl
      simp only [hT]
      rcases hlen with rfl | ⟨c, rfl, rfl⟩
      · simp
      dsimp only
      split
      · exact Interp.isRefinedBy_ok_target_iff.mpr ⟨_, rfl, result_empty hMem⟩
      rcases hd with rfl | ⟨p, rfl, hp⟩
      · simp
      rcases hs with rfl | ⟨q, rfl, hq⟩
      · simp
      obtain ⟨p', rfl, hp'⟩ : ∃ p', d' = .val p' ∧ (p ⊒ p') := by
        rcases hp with rfl | rfl <;> simp
      obtain ⟨q', rfl, hq'⟩ : ∃ q', s' = .val q' ∧ (q ⊒ q') := by
        rcases hq with rfl | rfl <;> simp
      simp only [reduceCtorEq, ite_false]
      exact isRefinedBy_memory_result (MemoryState.memmove_isRefinedBy hMem hp' hq' _)
    · simp [Interp.isRefinedBy]

end Veir

end
