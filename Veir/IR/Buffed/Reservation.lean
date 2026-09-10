module

public import Veir.IR.Buffed.RawAccessors

@[expose] public section
namespace Veir.Buffed.IRBufContext

theorem reserve_attributes {b b' : IRBufContext} {size address : UInt64}
    (h : b.reserve size = some (b', address)) : b'.attributes = b.attributes := by
  unfold reserve at h
  split at h
  · split at h
    · cases h; rfl
    · contradiction
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨buf, ha, heq⟩ := h
    cases heq
    unfold alloc at ha
    split at ha
    · cases ha; rfl
    · contradiction

theorem reserve_origin {b b' : IRBufContext} {size address : UInt64}
    (h : b.reserve size = some (b', address)) :
    (∃ free, b.freeList.take size = some (address, free) ∧ b'.freeList = free) ∨
      (address.toNat = b.mem.size ∧ b'.freeList = b.freeList) := by
  unfold reserve at h
  split at h
  · rename_i a free ht
    split at h
    · cases h; exact .inl ⟨free, ht, rfl⟩
    · contradiction
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨buf, ha, heq⟩ := h
    cases heq
    exact .inr ⟨b.usize_toNat, alloc_freeList ha⟩

theorem reserve_read_disjoint {b b' : IRBufContext} {size address : UInt64}
    (h : b.reserve size = some (b', address)) (w : Nat) (n len : UInt64)
    (hb : n.toNat + len.toNat ≤ b.mem.size)
    (hd : n.toNat + len.toNat ≤ address.toNat ∨ address.toNat + size.toNat ≤ n.toNat) :
    b'.mem.read! (w := w) n len = b.mem.read! n len := by
  unfold reserve at h
  split at h
  · split at h
    · cases h
      exact ExArray.read!_zero_disjoint _ _ _ _ _ _ (by simpa [IsDisjoint] using hd)
    · contradiction
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨buf, ha, heq⟩ := h
    cases heq
    unfold alloc at ha
    split at ha
    · cases ha
      exact ExArray.read!_extend _ _ _ _ _ (by simp [IsIncluded, ExArray.range_def]; omega)
    · contradiction

theorem reserve_free_disjoint {b b' : IRBufContext} {size address : UInt64}
    (hv : b.freeList.Valid b.mem.size) (h : b.reserve size = some (b', address))
    (s a : UInt64) (hm : a ∈ b'.freeList.bucket s) :
    a.toNat + s.toNat ≤ address.toNat ∨ address.toNat + size.toNat ≤ a.toNat := by
  rcases reserve_origin h with ⟨free, ht, hf⟩ | ⟨ha, hf⟩
  · rw [hf] at hm
    have hold := FreeList.bucket_take_subset ht s a hm
    have hne := hv.taken_not_mem ht
    exact hv.disjoint s a size address hold (FreeList.take_mem ht) (by grind)
  · rw [hf] at hm
    exact .inl (by have := hv.bounds s a hm; omega)

theorem reserve_free_subset {b b' : IRBufContext} {size address : UInt64}
    (h : b.reserve size = some (b', address)) (s a : UInt64)
    (hm : a ∈ b'.freeList.bucket s) : a ∈ b.freeList.bucket s := by
  rcases reserve_origin h with ⟨free, ht, hf⟩ | ⟨_, hf⟩
  · rw [hf] at hm; exact FreeList.bucket_take_subset ht s a hm
  · simpa [hf] using hm

end Veir.Buffed.IRBufContext
