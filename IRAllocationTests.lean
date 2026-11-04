import ExArray.CompilerExtras
import Veir.IR.Buffed.AllocateOperation
import Veir.IR.Buffed.AllocateBlock
import Veir.IR.Buffed.AllocateRegion
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
  change NoObjects (Erased.mk (default : Veir.IRContext OpCode)).out
  rw [Erased.out_mk]
  intro p
  cases p <;> simp [TopLevelPtr.InBounds, OperationPtr.inBounds_def,
    BlockPtr.inBounds_def, RegionPtr.inBounds_def, IRContext.default_def]⟩

private theorem fieldsOfEmpty {ctx : Veir.IRContext OpCode} (h : NoObjects ctx) : ctx.FieldsInBounds := by
  constructor
  · intro p hp; exact False.elim (h (.operation p) hp)
  · intro p hp; exact False.elim (h (.block p) hp)
  · intro p hp; exact False.elim (h (.region p) hp)

/-- Exercise verified append-only allocation and logical deletion with spare
capacities and back-allocated results. No proof assumptions are used. -/
private def cycleOperation (a : EmptyArena) : Option EmptyArena := do
  rlet h : (p, c) ← Sim.OperationPtr.allocFresh a.ctx (.builtin .unrealized_conversion_cast) ()
    3 2 1 2 (by decide) (by decide) (by decide) (by decide)
  have hs := Sim.OperationPtr.allocFresh_spec' h
  have ib : p.InBounds c := by grind
  have he : NoObjects (p.spec.dealloc c.spec ib.ib) := by
    intro q hq
    have old := a.empty
    unfold NoObjects at old
    cases q <;> grind [TopLevelPtr.InBounds, OperationPtr.dealloc, OperationPtr.inBounds_def]
  pure ⟨Sim.OperationPtr.dealloc c p ib (fieldsOfEmpty he), by
    simpa only [Sim.OperationPtr.dealloc.unfold, Sim.OperationPtr.forget.unfold,
      Sim.IRContext.spec, Erased.out_mk] using he⟩

private def cycleBlock (a : EmptyArena) : Option EmptyArena := do
  rlet h : (p, c) ← Sim.BlockPtr.allocFresh a.ctx 5
  have hs := Sim.BlockPtr.allocFresh_spec' 5 h
  have ib : p.InBounds c := by grind
  have he : NoObjects (p.spec.dealloc c.spec) := by
    intro q hq
    have old := a.empty
    unfold NoObjects at old
    cases q <;> grind [TopLevelPtr.InBounds, BlockPtr.dealloc, BlockPtr.inBounds_def]
  have hp : (p.spec.get! c.spec).parent = none := by grind [Block.empty]
  pure ⟨Rewriter.eraseBlock c p ib hp (fieldsOfEmpty he), by simpa using he⟩

private def cycleRegion (a : EmptyArena) : Option EmptyArena := do
  rlet h : (p, c) ← Sim.RegionPtr.allocFresh a.ctx
  have hs := Sim.RegionPtr.allocFresh_spec' h
  have ib : p.InBounds c := by grind
  have he : NoObjects (p.spec.dealloc c.spec) := by
    intro q hq
    have old := a.empty
    unfold NoObjects at old
    cases q <;> grind [TopLevelPtr.InBounds, RegionPtr.dealloc, RegionPtr.inBounds_def]
  have hp : (p.spec.get! c.spec).parent = none := by grind [Region.empty]
  pure ⟨Rewriter.eraseRegion c p ib hp (fieldsOfEmpty he), by simpa using he⟩

-- Deletion changes only the erased specification, not the runtime arena.
example (ctx : Sim.IRContext OpCode) (p : Sim.OperationPtr) (ib : p.InBounds ctx)
    (fib : (p.spec.dealloc ctx.spec ib.ib).FieldsInBounds) :
    (Sim.OperationPtr.dealloc ctx p ib fib).buf = ctx.buf := by
  simp only [Sim.OperationPtr.dealloc.unfold, Sim.OperationPtr.forget.unfold]

example (ctx : Sim.IRContext OpCode) (p : Sim.BlockPtr) (ib : p.InBounds ctx)
    (fib : (p.spec.dealloc ctx.spec).FieldsInBounds) :
    (Sim.BlockPtr.dealloc ctx p ib fib).buf = ctx.buf := by
  simp only [Sim.BlockPtr.dealloc.unfold, Sim.BlockPtr.forget.unfold]

example (ctx : Sim.IRContext OpCode) (p : Sim.RegionPtr) (ib : p.InBounds ctx)
    (fib : (p.spec.dealloc ctx.spec).FieldsInBounds) :
    (Sim.RegionPtr.dealloc ctx p ib fib).buf = ctx.buf := by
  simp only [Sim.RegionPtr.dealloc.unfold, Sim.RegionPtr.forget.unfold]

def main : IO Unit := do
  let some first := cycleOperation initial >>= cycleBlock >>= cycleRegion
    | throw (IO.userError "initial IR allocation/erasure failed")
  let bytesPerCycle := first.ctx.buf.mem.size
  unless bytesPerCycle > 0 do
    throw (IO.userError "allocations did not grow the arena")
  let mut arena := first
  for i in [:10000] do
    let some next := cycleOperation arena >>= cycleBlock >>= cycleRegion
      | throw (IO.userError "IR allocation/erasure cycle failed")
    unless next.ctx.buf.mem.size == (i + 2) * bytesPerCycle do
      throw (IO.userError "deleted storage was reused or arena growth was incorrect")
    arena := next
  IO.println s!"Verified append-only IR tests passed: 30,000 further allocations/erasures, {arena.ctx.buf.mem.size} bytes."
