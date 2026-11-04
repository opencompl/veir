import Veir.IR.Buffed.RawAccessors

open Veir.Buffed

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def main : IO Unit := do
  let some initial := (default : IRBufContext).alloc 256
    | throw (IO.userError "initial allocation failed")
  let mut initial := initial
  -- Dirty the whole slot and place live sentinels on both sides.
  for offset in ([56, 64, 72, 80, 88, 96] : List UInt64) do
    if h : 0 ≤ offset.toNat ∧ offset.toNat + 8 ≤ initial.mem.size then
      initial := { initial with mem := initial.mem.blit64 offset 123 h }
    else throw (IO.userError "initial allocation was too small")
  let some (reused, address) := (initial.release 64 32).reserve 32
    | throw (IO.userError "reuse failed")
  check (address == 64 && reused.mem.size == 256) "reuse grew the arena or moved the slot"
  for offset in [64, 72, 80, 88] do
    check (reused.mem.read64! offset == 0) "reused bytes were not cleared"
  check (reused.mem.read64! 56 == 123 && reused.mem.read64! 96 == 123)
    "reuse overwrote a neighboring live allocation"
  check (initial.mem.read64! 64 == 123) "reuse mutated a shared snapshot"
  check (reused.attributes == initial.attributes) "reuse changed the attribute table"
  let some (grown, next) := reused.reserve 32
    | throw (IO.userError "growth failed")
  check (next == 256 && grown.mem.size == 288) "a taken slot was allocated twice"
  let free := FreeList.release (FreeList.release ∅ 24 24) 64 32
  check ((free.take 16).isNone) "a different size class was reused"
  check ((free.take 24).map Prod.fst == some 24) "size-class lookup failed"
  let both := free.release 96 32
  let some (lastFreed, rest) := both.take 32
    | throw (IO.userError "multiple-free lookup failed")
  let some (firstFreed, rest) := rest.take 32
    | throw (IO.userError "multiple-free lookup lost a slot")
  check (lastFreed == 96 && firstFreed == 64) "free slots were not returned in stack order"
  check ((rest.take 32).isNone) "a free slot was returned twice"
  check ((rest.take 24).map Prod.fst == some 24) "taking a slot corrupted another size class"
  let mut ctx := reused.release 64 32
  for _ in [:10000] do
    let some (allocated, slot) := ctx.reserve 32
      | throw (IO.userError "repeated reuse failed")
    check (slot == 64) "repeated reuse lost its slot"
    ctx := allocated.release slot 32
  check (ctx.mem.size == 256) "repeated reuse grew the buffer"
  IO.println "Allocator tests passed (including 10,000 reuse cycles)."
