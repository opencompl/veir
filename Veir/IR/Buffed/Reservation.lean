module

public import Veir.IR.Buffed.RawAccessors

@[expose] public section
namespace Veir.Buffed.IRBufContext

theorem reserve_attributes {b b' : IRBufContext} {size address : UInt64}
    (h : b.reserve size = some (b', address)) : b'.attributes = b.attributes := by
  simp only [reserve, Option.map_eq_some_iff] at h
  obtain ⟨buf, ha, heq⟩ := h
  cases heq
  unfold alloc at ha
  split at ha
  · cases ha; rfl
  · contradiction

/-- Every reservation starts at the old end of the arena. -/
theorem reserve_origin {b b' : IRBufContext} {size address : UInt64}
    (h : b.reserve size = some (b', address)) : address.toNat = b.mem.size := by
  simp only [reserve, Option.map_eq_some_iff] at h
  obtain ⟨buf, _, heq⟩ := h
  cases heq
  simpa only [IRBufContext.size, IRBufContext.usize, Nat.toUInt64_eq,
    ExArray.ofNat_size_eq_usize] using b.usize_toNat

/-- Appending storage preserves every read from the old arena. -/
theorem reserve_read {b b' : IRBufContext} {size address : UInt64}
    (h : b.reserve size = some (b', address)) (w : Nat) (n len : UInt64)
    (hb : n.toNat + len.toNat ≤ b.mem.size) :
    b'.mem.read! (w := w) n len = b.mem.read! n len := by
  simp only [reserve, Option.map_eq_some_iff] at h
  obtain ⟨buf, ha, heq⟩ := h
  cases heq
  unfold alloc at ha
  split at ha
  · cases ha
    exact ExArray.read!_extend _ _ _ _ _ (by simp [IsIncluded, ExArray.range_def]; omega)
  · contradiction

end Veir.Buffed.IRBufContext
