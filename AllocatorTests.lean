import Veir.IR.Buffed.Reservation

open Veir.Buffed

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

-- Kernel-checked guarantees of the append-only allocator.
example {b b' : IRBufContext} {size address : UInt64}
    (h : b.reserve size = some (b', address)) : address.toNat = b.mem.size :=
  IRBufContext.reserve_origin h

example {b b' : IRBufContext} {size address : UInt64}
    (h : b.reserve size = some (b', address)) (n len : UInt64)
    (hb : n.toNat + len.toNat ≤ b.mem.size) :
    b'.mem.read! (w := 64) n len = b.mem.read! n len :=
  IRBufContext.reserve_read h 64 n len hb

def main : IO Unit := do
  let some initial := (default : IRBufContext).alloc 256
    | throw (IO.userError "initial allocation failed")
  let mut initial := initial
  for offset in ([0, 56, 64, 72, 80, 88, 96, 248] : List UInt64) do
    if h : 0 ≤ offset.toNat ∧ offset.toNat + 8 ≤ initial.mem.size then
      initial := { initial with mem := initial.mem.blit64 offset 123 h }
    else throw (IO.userError "initial allocation was too small")
  let some (grown, address) := initial.reserve 32
    | throw (IO.userError "append failed")
  check (address == 256 && grown.mem.size == 288) "allocation did not append"
  for offset in [256, 264, 272, 280] do
    check (grown.mem.read64! offset == 0) "appended bytes were not zeroed"
  for offset in [0, 56, 64, 72, 80, 88, 96, 248] do
    check (grown.mem.read64! offset == 123) "append overwrote old bytes"
    check (initial.mem.read64! offset == 123) "append mutated a shared snapshot"
  check (initial.mem.size == 256) "append grew the shared snapshot"
  check (grown.attributes == initial.attributes) "append changed the attribute table"
  check ((grown.reserve (-1 : UInt64)).isNone) "overflowing reservation succeeded"
  check ((grown.reserve Int64.maxNatValue.toUInt64).isNone) "oversized reservation succeeded"
  let mut ctx := grown
  for _ in [:10000] do
    let oldSize := ctx.mem.size
    let some (allocated, slot) := ctx.reserve 32
      | throw (IO.userError "repeated append failed")
    check (slot.toNat == oldSize && allocated.mem.size == oldSize + 32)
      "reservation reused an old address or grew by the wrong amount"
    check (allocated.mem.read64! slot == 0) "new storage was not zeroed"
    ctx := allocated
  check (ctx.mem.size == 320288) "incorrect final arena size"
  IO.println "Allocator tests passed (including 10,000 append-only allocations)."
