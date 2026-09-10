import ExArray.CompilerExtras
import Veir.IR.Buffed.RecycledOperation
import Veir.IR.Buffed.RecycledBlock
import Veir.IR.Buffed.RecycledRegion
import Veir.Rewriter.EraseContainers
import Veir.GlobalOpInfo
import Veir.IR.InBounds

open Veir
set_option maxHeartbeats 1000000

private def NoObjects (ctx : Veir.IRContext OpCode) : Prop :=
  ∀ p : TopLevelPtr, ¬ p.InBounds ctx

private structure EmptyArena where
  ctx : Sim.IRContext OpCode
  empty : NoObjects ctx.spec

private def initial : EmptyArena := ⟨default, by
  change NoObjects (default : Veir.IRContext OpCode)
  intro p
  cases p <;> simp [TopLevelPtr.InBounds, OperationPtr.inBounds_def,
    BlockPtr.inBounds_def, RegionPtr.inBounds_def, IRContext.default_def]⟩

private theorem fieldsOfEmpty {ctx : Veir.IRContext OpCode} (h : NoObjects ctx) : ctx.FieldsInBounds := by
  constructor
  · intro p hp; exact False.elim (h (.operation p) hp)
  · intro p hp; exact False.elim (h (.block p) hp)
  · intro p hp; exact False.elim (h (.region p) hp)

/-- Exercise the verified allocator and deallocator with spare capacities and
back-allocated results. No proof assumptions are used by this regression test. -/
private def cycleOperation (a : EmptyArena) : Option EmptyArena := do
  rlet h : (p, c) ← Sim.OperationPtr.allocRecycled a.ctx (.builtin .unrealized_conversion_cast) ()
    3 2 1 2 (by decide) (by decide) (by decide) (by decide)
  have hs := Sim.OperationPtr.allocRecycled_spec' h
  have ib : p.InBounds c := by grind
  have he : NoObjects (p.spec.dealloc c.spec ib.ib) := by
    intro q hq
    have old := a.empty
    unfold NoObjects at old
    cases q <;> grind [TopLevelPtr.InBounds, OperationPtr.dealloc, OperationPtr.inBounds_def]
  pure ⟨Sim.OperationPtr.dealloc c p ib (fieldsOfEmpty he), he⟩

private def cycleBlock (a : EmptyArena) : Option EmptyArena := do
  rlet h : (p, c) ← Sim.BlockPtr.allocRecycled a.ctx 5
  have hs := Sim.BlockPtr.allocRecycled_spec' 5 h
  have ib : p.InBounds c := by grind
  have he : NoObjects (p.spec.dealloc c.spec) := by
    intro q hq
    have old := a.empty
    unfold NoObjects at old
    cases q <;> grind [TopLevelPtr.InBounds, BlockPtr.dealloc, BlockPtr.inBounds_def]
  have hp : (p.spec.get! c.spec).parent = none := by grind [Block.empty]
  pure ⟨Rewriter.eraseBlock c p ib hp (fieldsOfEmpty he), he⟩

private def cycleRegion (a : EmptyArena) : Option EmptyArena := do
  rlet h : (p, c) ← Sim.RegionPtr.allocRecycled a.ctx
  have hs := Sim.RegionPtr.allocRecycled_spec' h
  have ib : p.InBounds c := by grind
  have he : NoObjects (p.spec.dealloc c.spec) := by
    intro q hq
    have old := a.empty
    unfold NoObjects at old
    cases q <;> grind [TopLevelPtr.InBounds, RegionPtr.dealloc, RegionPtr.inBounds_def]
  have hp : (p.spec.get! c.spec).parent = none := by grind [Region.empty]
  pure ⟨Rewriter.eraseRegion c p ib hp (fieldsOfEmpty he), he⟩

def main : IO Unit := do
  let some first := cycleOperation initial >>= cycleBlock >>= cycleRegion
    | throw (IO.userError "initial IR allocation/erasure failed")
  let highWater := first.ctx.buf.mem.size
  let mut arena := first
  for _ in [:10000] do
    let some next := cycleOperation arena >>= cycleBlock >>= cycleRegion
      | throw (IO.userError "IR allocation/erasure cycle failed")
    arena := next
  unless arena.ctx.buf.mem.size == highWater do
    throw (IO.userError s!"IR arena grew from {highWater} to {arena.ctx.buf.mem.size}")
  IO.println s!"Verified IR reuse tests passed: 30,000 allocations/erasures, {highWater} bytes."
