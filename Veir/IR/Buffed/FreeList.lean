module

public import Std.Data.HashMap.Lemmas

/-!
# Exact-size free lists

Free ranges are indexed by their byte length. A bucket is a stack, so allocation
and deallocation take expected constant time and never move a live allocation.
We deliberately neither split nor coalesce ranges: a different size falls back
to arena growth. The caller owns the bounds and non-overlap invariant.
-/

@[expose] public section

namespace Veir.Buffed

abbrev FreeList := Std.HashMap UInt64 (List UInt64)

namespace FreeList

/-- Addresses available for a request of exactly `size` bytes. -/
def bucket (free : FreeList) (size : UInt64) : List UInt64 :=
  free[size]?.getD []

/-- Return a range to its size class. Only an exclusively owned, dead allocation
may be returned; returning it twice would permit overlapping allocations. -/
def release (free : FreeList) (address size : UInt64) : FreeList :=
  free.insert size (address :: free.bucket size)

/-- Remove one exact-size range. Empty buckets are erased, so the index does not
retain every size class ever encountered. -/
def take (free : FreeList) (size : UInt64) : Option (UInt64 × FreeList) :=
  match free.bucket size with
  | [] => none
  | address :: rest =>
    some (address, if rest.isEmpty then free.erase size else free.insert size rest)

@[simp]
theorem bucket_release (free : FreeList) (address size query : UInt64) :
    (free.release address size).bucket query =
      if size = query then address :: free.bucket size else free.bucket query := by
  simp [release, bucket, Std.HashMap.getElem?_insert]
  split <;> simp_all

@[simp]
theorem take_empty (size : UInt64) : take ∅ size = none := by
  simp [take, bucket]

/-- A returned address really was available in the requested size class. -/
theorem take_mem {free free' : FreeList} {size address : UInt64}
    (h : free.take size = some (address, free')) : address ∈ free.bucket size := by
  unfold take at h
  split at h
  · contradiction
  · simp_all

/-- Popping one bucket does not introduce any new free addresses. -/
theorem bucket_take_subset {free free' : FreeList} {size address : UInt64}
    (h : free.take size = some (address, free')) (query candidate : UInt64) :
    candidate ∈ free'.bucket query → candidate ∈ free.bucket query := by
  unfold take at h
  split at h
  · contradiction
  · rename_i head rest hb
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    split
    · simp_all [bucket, Std.HashMap.getElem?_erase]
      split <;> simp_all
    · simp only [bucket, Std.HashMap.getElem?_insert]
      split <;> simp_all [bucket]

/-- The range discipline needed by a reusable arena. In particular, the index
cannot contain two copies of a slot, even in different size classes. -/
structure Valid (free : FreeList) (limit : Nat) : Prop where
  nodup (size : UInt64) : (free.bucket size).Nodup
  bounds (size address : UInt64) (h : address ∈ free.bucket size) :
    0 < size.toNat ∧ address.toNat + size.toNat ≤ limit
  disjoint (size₁ address₁ size₂ address₂ : UInt64)
      (h₁ : address₁ ∈ free.bucket size₁) (h₂ : address₂ ∈ free.bucket size₂)
      (hne : size₁ ≠ size₂ ∨ address₁ ≠ address₂) :
    address₁.toNat + size₁.toNat ≤ address₂.toNat ∨
      address₂.toNat + size₂.toNat ≤ address₁.toNat

theorem valid_empty (limit : Nat) : Valid ∅ limit := by
  constructor <;> simp [bucket]

theorem Valid.mono {free : FreeList} {limit limit' : Nat}
    (h : free.Valid limit) (hle : limit ≤ limit') : free.Valid limit' := by
  refine ⟨h.nodup, ?_, h.disjoint⟩
  intro size address hm
  have := h.bounds size address hm
  omega

theorem bucket_take {free free' : FreeList} {size address : UInt64}
    (h : free.take size = some (address, free')) (query : UInt64) :
    free'.bucket query =
      if size = query then (free.bucket size).tail else free.bucket query := by
  unfold take at h
  split at h
  · contradiction
  · rename_i head rest hb
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    split
    · simp only [List.isEmpty_iff] at *
      subst rest
      simp only [bucket, Std.HashMap.getElem?_erase]
      split <;> simp_all [bucket]
    · simp only [bucket, Std.HashMap.getElem?_insert]
      split <;> simp_all [bucket]

theorem Valid.take {free free' : FreeList} {limit : Nat} {size address : UInt64}
    (hv : free.Valid limit) (h : free.take size = some (address, free')) :
    free'.Valid limit := by
  refine ⟨?_, ?_, ?_⟩
  · intro query
    rw [bucket_take h]
    split
    · exact (hv.nodup size).tail
    · exact hv.nodup query
  · intro query candidate hm
    exact hv.bounds query candidate (bucket_take_subset h _ _ hm)
  · intro s a t b ha hb hne
    exact hv.disjoint s a t b (bucket_take_subset h _ _ ha)
      (bucket_take_subset h _ _ hb) hne

theorem Valid.taken_not_mem {free free' : FreeList} {limit : Nat} {size address : UInt64}
    (hv : free.Valid limit) (h : free.take size = some (address, free')) :
    address ∉ free'.bucket size := by
  rw [bucket_take h, if_pos rfl]
  have hn := hv.nodup size
  unfold FreeList.take at h
  split at h
  · contradiction
  · simp_all

theorem Valid.release {free : FreeList} {limit : Nat} {size address : UInt64}
    (hv : free.Valid limit) (hs : 0 < size.toNat)
    (hb : address.toNat + size.toNat ≤ limit)
    (hd : ∀ s a, a ∈ free.bucket s →
      address.toNat + size.toNat ≤ a.toNat ∨ a.toNat + s.toNat ≤ address.toNat) :
    (free.release address size).Valid limit := by
  have hn : address ∉ free.bucket size := by
    intro hm
    have := hd size address hm
    omega
  constructor
  · intro query
    rw [bucket_release]
    split
    · exact List.nodup_cons.mpr ⟨hn, hv.nodup size⟩
    · exact hv.nodup query
  · intro s a hm
    rw [bucket_release] at hm
    split at hm
    · rename_i heq
      subst s
      rcases List.mem_cons.mp hm with rfl | hm
      · exact ⟨hs, hb⟩
      · exact hv.bounds _ _ hm
    · exact hv.bounds _ _ hm
  · intro s a t b ha hb hne
    have hold := hv.disjoint s a t b
    have hleft := hd t b
    have hright := hd s a
    simp only [bucket_release] at ha hb
    split at ha <;> split at hb
    all_goals grind

end FreeList
end Veir.Buffed
