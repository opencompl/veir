module

public import Veir.IR.Buffed.RawAccessors

@[expose] public section
namespace Veir.Buffed.IRBufContext

theorem reserve_attributes {b b' : IRBufContext} {size address : UInt64}
    (h : b.reserve size = some (b', address)) : b'.attributes = b.attributes := by
  grind [reserve, alloc]

/-- Every reservation starts at the old end of the arena. -/
theorem reserve_origin {b b' : IRBufContext} {size address : UInt64}
    (h : b.reserve size = some (b', address)) : address.toNat = b.mem.size := by
  grind [reserve, Option.map_eq_some_iff]

/-- Appending storage preserves every read from the old arena. -/
theorem reserve_read {b b' : IRBufContext} {size address : UInt64}
    (h : b.reserve size = some (b', address)) (w : Nat) (n len : UInt64)
    (hb : n.toNat + len.toNat ≤ b.mem.size) :
    b'.mem.read! (w := w) n len = b.mem.read! n len := by
  grind [reserve, alloc, IsIncluded, ExArray.range_def]

end Veir.Buffed.IRBufContext
