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
  /-- The null object is at address 0, so a wild pointer's address is its offset. -/
  base_zero : (mem.objects[0]'nonempty).base = 0
  /-- An object ends, guard byte included, before the next one begins. -/
  disjoint : ∀ (i : Nat) (h : i + 1 < mem.objects.size),
    mem.objects[i].base.toNat + mem.objects[i].size < mem.objects[i + 1].base.toNat
  /-- The guard byte after an object is an address. -/
  noWrap : ∀ (i : Nat) (h : i < mem.objects.size),
    mem.objects[i].base.toNat + mem.objects[i].size + 1 < 2 ^ 64

namespace MemoryState

/-- Objects lie in address order. -/
theorem LayoutWf.base_lt {mem : MemoryState} (h : mem.LayoutWf) {i j : Nat}
    (hij : i < j) (hj : j < mem.objects.size) : mem.objects[i].base < mem.objects[j].base := by
  induction j with
  | zero => omega
  | succ j ih =>
    rw [UInt64.lt_iff_toNat_lt]
    have hd := h.disjoint j hj
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hij) with hlt | rfl
    · have := ih hlt (by omega)
      rw [UInt64.lt_iff_toNat_lt] at this
      omega
    · omega

/--
The fold behind `objectOfAddress`, over the first `m` objects. When the bases
increase and `i` is the last object whose base is at most `addr`, the fold
settles on `i` as soon as it has seen it, and on the last object before that.
-/
theorem foldl_best_eq (b : Nat → UInt64) (addr : UInt64) {i n : Nat} (hi : i < n)
    (hmono : ∀ j k, j < k → k < n → b j < b k) (hlo : b i ≤ addr)
    (hhi : ∀ j, i < j → j < n → addr < b j) :
    ∀ m, m ≤ n →
      (List.range m).foldl (fun best j => if b j ≤ addr ∧ b best ≤ b j then j else best) 0
        = min (m - 1) i := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    rw [List.range_succ, List.foldl_append, ih (by omega)]
    simp only [List.foldl_cons, List.foldl_nil]
    by_cases hmi : m ≤ i
    · have hbm : b m ≤ addr := by
        rcases Nat.lt_or_eq_of_le hmi with hlt | rfl
        · have h1 := hmono m i hlt hi
          rw [UInt64.lt_iff_toNat_lt] at h1
          rw [UInt64.le_iff_toNat_le] at hlo ⊢
          omega
        · exact hlo
      have hbest : b (min (m - 1) i) ≤ b m := by
        rcases Nat.eq_zero_or_pos m with rfl | hpos
        · simp
        · rw [show min (m - 1) i = m - 1 by omega]
          exact UInt64.le_of_lt (hmono (m - 1) m (by omega) (by omega))
      simp only [hbm, hbest, and_self, ↓reduceIte]
      omega
    · rw [show min (m - 1) i = i by omega]
      have hnot : ¬ (b m ≤ addr ∧ b i ≤ b m) := fun ⟨hle, _⟩ => by
        have h1 := hhi m (by omega) (by omega)
        rw [UInt64.lt_iff_toNat_lt] at h1
        rw [UInt64.le_iff_toNat_le] at hle
        omega
      simp only [hnot, ↓reduceIte]
      omega

/-- The base of an object, read through the lookup `objectOfAddress` uses. -/
theorem base_getD_eq {mem : MemoryState} {i : Nat} (hi : i < mem.objects.size) :
    (mem.objects[i]?.map (·.base)).getD 0 = mem.objects[i].base := by
  simp [Array.getElem?_eq_getElem hi]

/-- An address inside an object, its one-past-the-end included, belongs to it. -/
theorem LayoutWf.objectOfAddress_eq {mem : MemoryState} (h : mem.LayoutWf) {i : Nat}
    (hi : i < mem.objects.size) {addr : UInt64} (hlo : mem.objects[i].base ≤ addr)
    (hhi : addr.toNat ≤ mem.objects[i].base.toNat + mem.objects[i].size) :
    mem.objectOfAddress addr = i := by
  have hfold := foldl_best_eq (fun j => (mem.objects[j]?.map (·.base)).getD 0) addr hi
    (fun j k hjk hk => by
      rw [base_getD_eq (by omega), base_getD_eq hk]; exact h.base_lt hjk hk)
    (by rw [base_getD_eq hi]; exact hlo)
    (fun j hij hj => by
      rw [base_getD_eq hj, UInt64.lt_iff_toNat_lt]
      have hd := h.disjoint i (by omega)
      have h1 : mem.objects[i + 1].base.toNat ≤ mem.objects[j].base.toNat := by
        rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hij) with hlt | heq
        · exact UInt64.le_iff_toNat_le.mp (UInt64.le_of_lt (h.base_lt hlt hj))
        · subst heq; exact Nat.le_refl _
      omega)
    mem.objects.size (Nat.le_refl _)
  simp only [MemoryState.objectOfAddress]
  exact hfold.trans (by omega)

/-- The address of a pointer, in the naturals, when it does not wrap. -/
theorem LayoutWf.toNat_address {mem : MemoryState} (h : mem.LayoutWf) {p : Pointer}
    (hp : p.object < mem.objects.size) (hoff : p.offset.toNat ≤ mem.objects[p.object].size) :
    (mem.address p).toNat = mem.objects[p.object].base.toNat + p.offset.toNat := by
  have hnw := h.noWrap p.object hp
  simp only [MemoryState.address, base_getD_eq hp, UInt64.toNat_add]
  exact Nat.mod_eq_of_lt (by omega)

/-- The address of an in-bounds pointer decodes to that pointer. -/
theorem LayoutWf.decode_address {mem : MemoryState} (h : mem.LayoutWf) {p : Pointer}
    (hp : p.object < mem.objects.size) (hoff : p.offset.toNat ≤ mem.objects[p.object].size)
    (hwild : p.wild = false) : mem.decode (mem.address p) = p := by
  have haddr := h.toNat_address hp hoff
  have hobj : mem.objectOfAddress (mem.address p) = p.object :=
    h.objectOfAddress_eq hp (by rw [UInt64.le_iff_toNat_le, haddr]; omega) (by rw [haddr]; omega)
  obtain ⟨o, off, w⟩ := p
  simp only at hwild hp hoff hobj
  subst hwild
  simp only [MemoryState.decode]
  rw [hobj, base_getD_eq hp]
  simp only [Pointer.mk.injEq, true_and, and_true, MemoryState.address, base_getD_eq hp]
  rw [UInt64.add_comm]
  exact UInt64.add_sub_cancel _ _

/-- A pointer that is not wild resolves to itself. -/
theorem resolve_of_not_wild {mem : MemoryState} {p : Pointer} (hwild : p.wild = false) :
    mem.resolve p = p := by
  simp [MemoryState.resolve, hwild]

/-- The wild pointer at the address of an in-bounds pointer resolves to that pointer. -/
theorem LayoutWf.resolve_ofAddress {mem : MemoryState} (h : mem.LayoutWf) {p : Pointer}
    (hp : p.object < mem.objects.size) (hoff : p.offset.toNat ≤ mem.objects[p.object].size)
    (hwild : p.wild = false) : mem.resolve (Pointer.ofAddress (mem.address p)) = p := by
  simp only [MemoryState.resolve, Pointer.ofAddress, ↓reduceIte]
  exact h.decode_address hp hoff hwild

/-- A wild pointer's address is its offset. -/
theorem LayoutWf.address_ofAddress {mem : MemoryState} (h : mem.LayoutWf) (addr : UInt64) :
    mem.address (Pointer.ofAddress addr) = addr := by
  simp [MemoryState.address, Pointer.ofAddress, Array.getElem?_eq_getElem h.nonempty, h.base_zero]

/-- The fold behind `objectOfAddress` only ever picks an index it was offered. -/
theorem foldl_best_lt (b : Nat → UInt64) (addr : UInt64) {n : Nat} :
    ∀ (l : List Nat) (best : Nat), best < n → (∀ i ∈ l, i < n) →
      l.foldl (fun best j => if b j ≤ addr ∧ b best ≤ b j then j else best) best < n := by
  intro l
  induction l with
  | nil => intro _ hbest _; simpa using hbest
  | cons j l ih =>
    intro best hbest hl
    simp only [List.foldl_cons]
    apply ih
    · split
      · exact hl j (by simp)
      · exact hbest
    · exact fun i hi => hl i (by simp [hi])

/-- An address decodes to an object of the memory. -/
theorem LayoutWf.objectOfAddress_lt {mem : MemoryState} (h : mem.LayoutWf) (addr : UInt64) :
    mem.objectOfAddress addr < mem.objects.size := by
  simp only [MemoryState.objectOfAddress]
  exact foldl_best_lt _ addr _ 0 h.nonempty (fun i hi => List.mem_range.mp hi)

theorem LayoutWf.decode_object_lt {mem : MemoryState} (h : mem.LayoutWf) (addr : UInt64) :
    (mem.decode addr).object < mem.objects.size :=
  h.objectOfAddress_lt addr

/-- A pointer into an object of the memory resolves to one. -/
theorem LayoutWf.resolve_object_lt {mem : MemoryState} (h : mem.LayoutWf) {p : Pointer}
    (hp : p.object < mem.objects.size) : (mem.resolve p).object < mem.objects.size := by
  simp only [MemoryState.resolve]
  split
  · exact h.decode_object_lt _
  · exact hp

/-! ## Growing the memory -/

/--
`mem'` extends `mem`: every object of `mem` is an object of `mem'` at the same address. Every
operation leaves the memory extending the one it found, since objects are only ever added, and
that is what keeps a pointer's address meaningful across a step in assembly mode.
-/
structure Extends (mem mem' : MemoryState) : Prop where
  /-- Objects are only ever added. -/
  size_le : mem.objects.size ≤ mem'.objects.size
  /-- An object keeps its address. -/
  base_eq : ∀ (i : Nat) (h : i < mem.objects.size),
    (mem'.objects[i]'(Nat.lt_of_lt_of_le h size_le)).base = mem.objects[i].base

theorem Extends.refl (mem : MemoryState) : mem.Extends mem :=
  ⟨Nat.le_refl _, fun _ _ => rfl⟩

/-- A pointer into an object of `mem` has the same address in a memory that extends `mem`. -/
theorem Extends.address_eq {mem mem' : MemoryState} (h : mem.Extends mem')
    {p : Pointer} (hp : p.object < mem.objects.size) : mem'.address p = mem.address p := by
  simp only [MemoryState.address, Array.getElem?_eq_getElem hp,
    Array.getElem?_eq_getElem (Nat.lt_of_lt_of_le hp h.size_le), Option.map_some, Option.getD_some,
    h.base_eq p.object hp]

/-- `alloc` extends the memory. -/
theorem alloc_extends {mem mem' : MemoryState} {size : UInt64} {p : Pointer}
    (halloc : mem.alloc size = .ok (mem', p)) : mem.Extends mem' := by
  simp only [MemoryState.alloc] at halloc
  split at halloc
  · simp at halloc
  · simp only [pure, Interp.ok.injEq, Prod.mk.injEq] at halloc
    obtain ⟨rfl, -⟩ := halloc
    refine ⟨by simp, fun i hi => ?_⟩
    simp [Array.getElem_push, hi]

/-- `alloc` returns a pointer to the object it adds. -/
theorem alloc_object_lt {mem mem' : MemoryState} {size : UInt64} {p : Pointer}
    (halloc : mem.alloc size = .ok (mem', p)) : p.object < mem'.objects.size := by
  simp only [MemoryState.alloc] at halloc
  split at halloc
  · simp at halloc
  · simp only [pure, Interp.ok.injEq, Prod.mk.injEq] at halloc
    obtain ⟨rfl, rfl⟩ := halloc
    simp

/-- `alloc` returns a pointer that is not wild. -/
theorem alloc_not_wild {mem mem' : MemoryState} {size : UInt64} {p : Pointer}
    (halloc : mem.alloc size = .ok (mem', p)) : p.wild = false := by
  simp only [MemoryState.alloc] at halloc
  split at halloc
  · simp at halloc
  · simp only [pure, Interp.ok.injEq, Prod.mk.injEq] at halloc
    obtain ⟨-, rfl⟩ := halloc
    rfl

/-! ## The invariant holds -/

theorem LayoutWf.empty : MemoryState.empty.LayoutWf where
  nonempty := by simp [MemoryState.empty]
  base_zero := by simp [MemoryState.empty, MemoryObject.ofSize]
  disjoint i h := by simp [MemoryState.empty] at h
  noWrap i h := by
    simp [MemoryState.empty] at h
    subst h
    simp [MemoryState.empty, MemoryObject.ofSize, MemoryObject.size]

/-- Every object ends, guard byte included, at or before `nextBase`. -/
theorem le_nextBase {mem : MemoryState} {i : Nat} (hi : i < mem.objects.size) :
    mem.objects[i].base.toNat + mem.objects[i].size + 1 ≤ mem.nextBase := by
  have hinit : ∀ (l : List MemoryObject) (init : Nat),
      init ≤ l.foldl (fun past obj => max past (obj.base.toNat + obj.size + 1)) init := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons x l ih => intro init; simp only [List.foldl_cons]; exact Nat.le_trans (Nat.le_max_left _ _) (ih _)
  have hfold : ∀ (l : List MemoryObject) (init : Nat) (obj : MemoryObject), obj ∈ l →
      obj.base.toNat + obj.size + 1 ≤
        l.foldl (fun past obj => max past (obj.base.toNat + obj.size + 1)) init := by
    intro l
    induction l with
    | nil => intro _ _ h; simp at h
    | cons x l ih =>
      intro init obj hmem
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact Nat.le_trans (Nat.le_max_right _ _) (hinit _ _)
      · exact ih _ obj hmem
  have hpast := hfold mem.objects.toList MemoryState.arenaSize.toNat mem.objects[i]
    (Array.getElem_mem_toList hi)
  rw [Array.foldl_toList] at hpast
  have hal : MemoryState.objectAlignment.toNat = 16 := rfl
  simp only [MemoryState.nextBase, hal]
  omega

/-- `alloc` keeps the layout. -/
theorem LayoutWf.alloc {mem mem' : MemoryState} {size : UInt64} {p : Pointer}
    (h : mem.LayoutWf) (halloc : mem.alloc size = .ok (mem', p)) : mem'.LayoutWf := by
  simp only [MemoryState.alloc] at halloc
  split at halloc
  · simp at halloc
  next hfits =>
    simp only [pure, Interp.ok.injEq, Prod.mk.injEq] at halloc
    obtain ⟨rfl, -⟩ := halloc
    have hbase : (mem.nextBase.toUInt64).toNat = mem.nextBase := by
      simp [show mem.nextBase < 2 ^ 64 by omega]
    refine ⟨by simp, ?_, fun i hi => ?_, fun i hi => ?_⟩
    · simp only [Array.getElem_push, h.nonempty, ↓reduceDIte]
      exact h.base_zero
    · simp only [Array.size_push] at hi
      have hi' : i < mem.objects.size := by omega
      by_cases hnext : i + 1 < mem.objects.size
      · simp only [Array.getElem_push, hi', hnext, ↓reduceDIte]
        exact h.disjoint i hnext
      · simp only [Array.getElem_push, hi', hnext, ↓reduceDIte, MemoryObject.ofSize, hbase]
        have := le_nextBase (mem := mem) hi'
        omega
    · simp only [Array.size_push] at hi
      by_cases hlt : i < mem.objects.size
      · simp only [Array.getElem_push, hlt, ↓reduceDIte]
        exact h.noWrap i hlt
      · simp only [Array.getElem_push, hlt, ↓reduceDIte]
        have hsize : (MemoryObject.ofSize mem.nextBase.toUInt64 size.toNat).size = size.toNat := by
          simp [MemoryObject.ofSize, MemoryObject.size]
        rw [hsize]
        simp only [MemoryObject.ofSize, hbase]
        omega

end MemoryState

end Veir

end
