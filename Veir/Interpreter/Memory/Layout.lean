module

public import Veir.Interpreter.Memory

import all Veir.Interpreter.Memory
import all Veir.Data.Pointer.Basic

public section

/-!
# The layout of memory

`alloc` places every object past the end of every object before it, with a
guard byte between them, and nothing in `MemoryState` records that. `LayoutWf`
does: objects lie in address order, each ends before the next begins, and the
guard byte after the last one is still an address. Under it an address inside
an object decodes to that object, which is what lets a wild pointer find its
way back to the object it was made from.
-/

namespace Veir

open Veir.Data

/-- The layout `alloc` maintains. -/
structure MemoryState.LayoutWf (mem : MemoryState) : Prop where
  /-- The null object is there. -/
  nonempty : 0 < mem.objects.size
  /-- The null object is at address 0. -/
  base_zero : (mem.objects[0]'nonempty).base = 0
  /-- An object ends, guard byte included, before the next one begins. -/
  disjoint : ∀ (i : Nat) (h : i + 1 < mem.objects.size),
    mem.objects[i].base.toNat + mem.objects[i].size < mem.objects[i + 1].base.toNat
  /-- The guard byte after an object is an address. -/
  noWrap : ∀ (i : Nat) (h : i < mem.objects.size),
    mem.objects[i].base.toNat + mem.objects[i].size + 1 < 2 ^ 64

namespace MemoryState

/-- The base of an object, read the way `objectOfAddress` and `decode` read it. -/
theorem base_getD_eq {mem : MemoryState} {i : Nat} (hi : i < mem.objects.size) :
    (mem.objects[i]?.map (·.base)).getD 0 = mem.objects[i].base := by
  simp [Array.getElem?_eq_getElem hi]

/-- Objects lie in address order. -/
theorem LayoutWf.base_lt {mem : MemoryState} (h : mem.LayoutWf) {i j : Nat}
    (hij : i < j) (hj : j < mem.objects.size) :
    mem.objects[i].base.toNat < mem.objects[j].base.toNat := by
  induction j with
  | zero => omega
  | succ j ih =>
    have := h.disjoint j hj
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hij) with hlt | rfl
    · have := ih hlt (by omega); omega
    · omega

/--
The fold behind `objectOfAddress`, over the first `m` indices. When the keys
increase and `i` is the last index whose key is at most `addr`, the fold settles
on `i` once it has seen it, and on the last index before that until then.
-/
theorem foldl_best_eq {b : Nat → Nat} {addr i n : Nat} (hi : i < n)
    (hmono : ∀ j k, j < k → k < n → b j < b k) (hlo : b i ≤ addr)
    (hhi : ∀ j, i < j → j < n → addr < b j) (m : Nat) (hm : m ≤ n) :
    (List.range m).foldl (fun best j => if b j ≤ addr ∧ b best ≤ b j then j else best) 0
      = min (m - 1) i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, ih (by omega)]
    simp only [List.foldl_cons, List.foldl_nil]
    by_cases hmi : m ≤ i
    · have hbm : b m ≤ addr := by
        rcases Nat.lt_or_eq_of_le hmi with hlt | rfl
        · exact Nat.le_of_lt (Nat.lt_of_lt_of_le (hmono m i hlt hi) hlo)
        · exact hlo
      have hbest : b (min (m - 1) i) ≤ b m := by
        rcases Nat.eq_zero_or_pos m with rfl | hpos
        · simp
        · rw [show min (m - 1) i = m - 1 by omega]
          exact Nat.le_of_lt (hmono (m - 1) m (by omega) (by omega))
      simp only [hbm, hbest, and_self, ↓reduceIte]
      omega
    · have hnot : ¬ (b m ≤ addr ∧ b i ≤ b m) := fun ⟨hle, _⟩ =>
        Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hhi m (by omega) (by omega)) hle)
      rw [show min (m - 1) i = i by omega]
      simp only [hnot, ↓reduceIte]
      omega

/-- An address inside an object, its one-past-the-end included, belongs to it. -/
theorem LayoutWf.objectOfAddress_eq {mem : MemoryState} (h : mem.LayoutWf) {i : Nat}
    (hi : i < mem.objects.size) {addr : UInt64} (hlo : mem.objects[i].base.toNat ≤ addr.toNat)
    (hhi : addr.toNat ≤ mem.objects[i].base.toNat + mem.objects[i].size) :
    mem.objectOfAddress addr = i := by
  have hmono : ∀ j k, j < k → k < mem.objects.size →
      ((mem.objects[j]?.map (fun o : MemoryObject => o.base)).getD 0).toNat <
        ((mem.objects[k]?.map (fun o : MemoryObject => o.base)).getD 0).toNat := by
    intro j k hjk hk
    rw [base_getD_eq (Nat.lt_trans hjk hk), base_getD_eq hk]
    exact h.base_lt hjk hk
  have hhi' : ∀ j, i < j → j < mem.objects.size →
      addr.toNat < ((mem.objects[j]?.map (fun o : MemoryObject => o.base)).getD 0).toNat := by
    intro j hij hj
    have := h.disjoint i (by omega)
    rw [base_getD_eq hj]
    obtain hlt | rfl : i + 1 < j ∨ i + 1 = j := by omega
    · have := h.base_lt hlt hj; omega
    · omega
  simp only [MemoryState.objectOfAddress, UInt64.le_iff_toNat_le]
  rw [foldl_best_eq hi hmono (by simpa [base_getD_eq hi] using hlo) hhi' _ (Nat.le_refl _)]
  omega

/-- An address inside an object decodes to the pointer into that object. -/
theorem LayoutWf.decode_address {mem : MemoryState} (h : mem.LayoutWf) {p : Pointer}
    (hp : p.object < mem.objects.size) (hlo : mem.objects[p.object].base.toNat ≤ p.address.toNat)
    (hhi : p.address.toNat ≤ mem.objects[p.object].base.toNat + mem.objects[p.object].size)
    (hwild : p.wild = false) : mem.decode p.address = p := by
  obtain ⟨o, a, w⟩ := p
  subst hwild
  simp [MemoryState.decode, h.objectOfAddress_eq hp hlo hhi]

/-- A pointer that is not wild resolves to itself. -/
theorem resolve_of_not_wild {mem : MemoryState} {p : Pointer} (hwild : p.wild = false) :
    mem.resolve p = p := by
  simp [MemoryState.resolve, hwild]

/-- The wild pointer at the address of a pointer into an object resolves to that pointer. -/
theorem LayoutWf.resolve_ofAddress {mem : MemoryState} (h : mem.LayoutWf) {p : Pointer}
    (hp : p.object < mem.objects.size) (hlo : mem.objects[p.object].base.toNat ≤ p.address.toNat)
    (hhi : p.address.toNat ≤ mem.objects[p.object].base.toNat + mem.objects[p.object].size)
    (hwild : p.wild = false) : mem.resolve (Pointer.ofAddress p.address) = p := by
  simpa [MemoryState.resolve, Pointer.ofAddress] using h.decode_address hp hlo hhi hwild

/-! ## The invariant holds -/

theorem LayoutWf.empty : MemoryState.empty.LayoutWf := by
  constructor <;> simp [MemoryState.empty, MemoryObject.ofSize, MemoryObject.size]

/-- What a successful `alloc` is: the object fits, guard byte included, and goes at the end. -/
theorem alloc_ok {mem mem' : MemoryState} {size : UInt64} {p : Pointer}
    (halloc : mem.alloc size = .ok (mem', p)) :
    mem.nextBase + size.toNat + 1 < 2 ^ 64 ∧
      mem' = { mem with
        objects := mem.objects.push (MemoryObject.ofSize mem.nextBase.toUInt64 size.toNat) } ∧
      p = ⟨mem.objects.size, mem.nextBase.toUInt64, false⟩ := by
  simp only [MemoryState.alloc] at halloc
  split at halloc
  · simp at halloc
  · simp only [pure, Interp.ok.injEq, Prod.mk.injEq] at halloc
    obtain ⟨rfl, rfl⟩ := halloc
    exact ⟨by omega, rfl, rfl⟩

/-- A fold of `max` is at least its start and at least every element. -/
theorem le_foldl_max {α : Type} (f : α → Nat) (l : List α) (init : Nat) :
    init ≤ l.foldl (fun past x => max past (f x)) init ∧
      ∀ x ∈ l, f x ≤ l.foldl (fun past x => max past (f x)) init := by
  induction l generalizing init with
  | nil => simp
  | cons y l ih =>
    simp only [List.foldl_cons]
    obtain ⟨h₁, h₂⟩ := ih (max init (f y))
    refine ⟨by omega, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · exact h₂ x hx

/-- Every object ends, guard byte included, at or before `nextBase`. -/
theorem le_nextBase {mem : MemoryState} {i : Nat} (hi : i < mem.objects.size) :
    mem.objects[i].base.toNat + mem.objects[i].size + 1 ≤ mem.nextBase := by
  have := (le_foldl_max (fun obj => obj.base.toNat + obj.size + 1) mem.objects.toList
    MemoryState.arenaSize.toNat).2 _ (Array.getElem_mem_toList hi)
  have hal : MemoryState.objectAlignment.toNat = 16 := rfl
  simp only [MemoryState.nextBase, hal, Array.foldl_toList] at this ⊢
  omega

/-- `alloc` keeps the layout. -/
theorem LayoutWf.alloc {mem mem' : MemoryState} {size : UInt64} {p : Pointer}
    (h : mem.LayoutWf) (halloc : mem.alloc size = .ok (mem', p)) : mem'.LayoutWf := by
  obtain ⟨hfits, rfl, -⟩ := alloc_ok halloc
  have hbase : mem.nextBase.toUInt64.toNat = mem.nextBase := by
    simp [show mem.nextBase < 2 ^ 64 by omega]
  refine ⟨by simp, by simpa [Array.getElem_push, h.nonempty] using h.base_zero,
    fun i hi => ?_, fun i hi => ?_⟩
  · simp only [Array.size_push] at hi
    have hi' : i < mem.objects.size := by omega
    have := le_nextBase hi'
    simp only [Array.getElem_push, hi', ↓reduceDIte]
    split
    · exact h.disjoint i ‹_›
    · simp only [MemoryObject.ofSize, hbase]; omega
  · simp only [Array.size_push] at hi
    simp only [Array.getElem_push]
    split
    · exact h.noWrap i ‹_›
    · have hsize : (MemoryObject.ofSize mem.nextBase.toUInt64 size.toNat).size = size.toNat := by
        simp [MemoryObject.ofSize, MemoryObject.size]
      rw [hsize]; simp only [MemoryObject.ofSize, hbase]; omega

end MemoryState

end Veir

end
