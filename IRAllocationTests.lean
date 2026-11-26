import Veir.IR.Buffed.AllocateOperation
import Veir.IR.Buffed.AllocateBlock
import Veir.IR.Buffed.AllocateRegion
import Veir.Rewriter.Basic
import Veir.GlobalOpInfo
import Veir.IR.InBounds

open Veir
set_option maxHeartbeats 1000000

/- The paired header fields occupy separate words and fit before the payload. -/
open Buffed.Operation in
example : Offsets.numResults + Sizes.numResults = Offsets.countResults ∧
    Offsets.countResults + Sizes.countResults = Offsets.prev ∧
    Offsets.numBlockOperands + Sizes.numBlockOperands = Offsets.countBlockOperands ∧
    Offsets.countBlockOperands + Sizes.countBlockOperands = Offsets.numRegions ∧
    Offsets.numRegions + Sizes.numRegions = Offsets.countRegions ∧
    Offsets.countRegions + Sizes.countRegions = Offsets.numOperands ∧
    Offsets.numOperands + Sizes.numOperands = Offsets.countOperands ∧
    Offsets.countOperands + Sizes.countOperands = Offsets.attrs ∧
    Offsets.properties.toInt = sizeBaseNat := by decide

open Buffed.Block in
example : Offsets.numArguments + Sizes.numArguments = Offsets.countArguments ∧
    Offsets.countArguments + Sizes.countArguments = Offsets.arguments ∧
    Offsets.arguments.toInt = sizeBaseNat := by decide

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

/-- Reuse the returned verified context for a second push. In particular the first
append must not change the reserved size or cause the second to overwrite slot zero. -/
private def chainedArguments : Option Bool := do
  rlet h : (bl, c) ← Sim.BlockPtr.allocFresh initial.ctx 3
  have hs := Sim.BlockPtr.allocFresh_spec' 3 h
  have ib : bl.InBounds c := by grind
  let ty : TypeAttr := IntegerType.mk 32
  rlet h₁ : c₁ ← Rewriter.pushBlockArgumentAt bl c 0 ty ib (by grind [Block.empty]) (by grind [Block.empty])
  have spec₁ := Rewriter.pushBlockArgumentAt_spec h₁
  have ib₁ : bl.InBounds c₁ := ⟨ib.sim, by grind [Rewriter.pushBlockArgument]⟩
  rlet _h₂ : c₂ ← Rewriter.pushBlockArgumentAt bl c₁ 1 ty ib₁ (by grind [Rewriter.pushBlockArgument, Block.empty])
    (by grind [Rewriter.pushBlockArgument, Block.empty])
  pure (bl.getNumArguments c ib == 0 && bl.getNumArguments c₁ ib₁ == 1 &&
    bl.getNumArguments! c₂ == 2 && bl.impl.readNumArguments! c₂.buf == 3 &&
    (bl.impl.getArgumentPtr 0).readIndex! c₂.buf == 0 && (bl.impl.getArgumentPtr 1).readIndex! c₂.buf == 1)

/-- A reserved operation exposes no elements until the first push, even if all
four arrays have nonzero capacities. -/
private def reservedOperation : Option Bool := do
  rlet h : (op, c) ← Sim.OperationPtr.allocFresh initial.ctx (.builtin .unrealized_conversion_cast) ()
    3 2 1 4 (by decide) (by decide) (by decide) (by decide)
  have hs := Sim.OperationPtr.allocFresh_spec' h
  have ib : op.InBounds c := by grind
  if ha : c.buf.attributes.size < UInt64.size then
    let c₁ := Rewriter.pushResultAt op c 0 (IntegerType.mk 32) ib (by grind [Operation.empty])
      (by grind [Operation.empty]) ha
    pure (op.getNumResults c ib == 0 && op.getNumResults! c₁ == 1 &&
      op.getNumOperands! c₁ == 0 && op.getNumSuccessors! c₁ == 0 && op.getNumRegions! c₁ == 0 &&
      op.impl.readNumResults! c₁.buf == 3 && op.impl.readNumOperands! c₁.buf == 2 &&
      op.impl.readNumBlockOperands! c₁.buf == 1 && op.impl.readNumRegions! c₁.buf == 4)
  else none

def main : IO Unit := do
  unless reservedOperation == some true do
    throw (IO.userError "operation lengths do not match initialized elements")
  unless chainedArguments == some true do
    throw (IO.userError "chained block argument pushes did not preserve counts, capacity, or slots")
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
