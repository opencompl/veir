module

public import Veir.IR.Buffed.Push
import Veir.IR.Buffed.Frames
import Veir.IR.Buffed.InBounds
import Veir.IR.Buffed.RawAccessorsLemmas
import Veir.IR.GetSet

public section
namespace Veir
variable [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo]

private inductive HeaderOwner where
  | op (p : OperationPtr)
  | bl (p : BlockPtr)
  deriving DecidableEq

private def HeaderOwner.base : HeaderOwner → UInt64
  | .op p => p.toM
  | .bl p => p.toM
private def HeaderOwner.bytes : HeaderOwner → Nat
  | .op _ => Buffed.Operation.sizeBaseNat
  | .bl _ => Buffed.Block.sizeBaseNat
private def HeaderOwner.range (p : HeaderOwner) (s : IRContext OpInfo) := match p with
  | .op p => p.rangeInt s
  | .bl p => p.rangeInt s
private def HeaderOwner.Valid (p : HeaderOwner) (s : IRContext OpInfo) := match p with
  | .op p => p.InBounds s
  | .bl p => p.InBounds s

private theorem HeaderOwner.in_range {ctx : Sim.IRContext OpInfo} (p : HeaderOwner) (h : p.Valid ctx.spec) :
    (p.range ctx.spec).lower ≤ p.base.toNat ∧
    (p.base.toNat : Int) + p.bytes ≤ (p.range ctx.spec).upper ∧
    p.base.toNat + p.bytes ≤ ctx.buf.mem.size := by
  cases p with
  | op p =>
    have hb : p.InBounds ctx.spec := h
    have hr := Sim.OperationPtr.range_linear p hb
    have hp := OperationPtr.toM_toNat ctx.sim.repr p hb
    simp only [range, base, bytes, OperationPtr.rangeInt, Buffed.Operation.rangeInt, add_nat_range_def]
    grind [OperationPtr.toFlat]
  | bl p =>
    have hb : p.InBounds ctx.spec := h
    have hr := Sim.BlockPtr.range_linear p hb
    have hp := BlockPtr.toM_toNat ctx.sim.repr p hb
    simp only [range, base, bytes, BlockPtr.rangeInt, Buffed.Block.rangeInt, add_nat_range_def]
    grind [BlockPtr.toFlat]

private theorem HeaderOwner.disjoint {ctx : Sim.IRContext OpInfo} {p q : HeaderOwner}
    (hp : p.Valid ctx.spec) (hq : q.Valid ctx.spec) (hne : p ≠ q) :
    IsDisjointI (p.range ctx.spec) (q.range ctx.spec) := by
  cases p with
  | op p => cases q with
    | op q => exact Sim.disjoint_operation_operation p q hp hq (by grind)
    | bl q => exact Sim.disjoint_operation_block p q hp hq
  | bl p => cases q with
    | op q => exact Sim.disjoint_block_operation p q hp hq
    | bl q => exact Sim.disjoint_block_block p q hp hq (by grind)

/-- The two writes made by a push are inside the same allocation. One is outside
its header; the other updates a single header word. -/
private structure PushFrame (ctx : Sim.IRContext OpInfo) (buf : Buffed.IRBufContext)
    (p : HeaderOwner) (off : Int64) (slot : UInt64) (sz : Nat) : Prop where
  slot_lo : (p.range ctx.spec).lower ≤ slot.toNat
  slot_hi : (slot.toNat : Int) + sz ≤ (p.range ctx.spec).upper
  outside : slot.toNat + sz ≤ p.base.toNat ∨ p.base.toNat + p.bytes ≤ slot.toNat
  read (a : UInt64)
    (_ : a.toNat + 8 ≤ slot.toNat ∨ slot.toNat + sz ≤ a.toNat)
    (_ : a.toNat + 8 ≤ (p.base + off).toNat ∨ (p.base + off).toNat + 8 ≤ a.toNat) :
    buf.mem.read64! a = ctx.buf.mem.read64! a

private theorem PushFrame.header {ctx : Sim.IRContext OpInfo} {p q : HeaderOwner}
    {buf off slot sz} (f : PushFrame ctx buf p off slot sz) (hp : p.Valid ctx.spec) (hq : q.Valid ctx.spec)
    (o : Int64) (ha : 0 ≤ off.toInt ∧ off.toInt + 8 ≤ p.bytes)
    (hb : 0 ≤ o.toInt ∧ o.toInt + 8 ≤ q.bytes)
    (hd : p ≠ q ∨ off.toInt + 8 ≤ o.toInt ∨ o.toInt + 8 ≤ off.toInt) :
    buf.mem.read64! (q.base + o) = ctx.buf.mem.read64! (q.base + o) := by
  have hpr := p.in_range (ctx := ctx) hp
  have hqr := q.in_range (ctx := ctx) hq
  have hmem := Sim.IRContext.mem_size_lt ctx
  have hpo : ((p.base + off).toNat : Int) = p.base.toNat + off.toInt := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;> grind
  have hqo : ((q.base + o).toNat : Int) = q.base.toNat + o.toInt := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;> grind
  have hs := f.outside
  have h1 := f.slot_lo
  have h2 := f.slot_hi
  by_cases heq : p = q
  · subst q
    rcases hd with h | h
    · exact False.elim (h rfl)
    · apply f.read <;> omega
  · have hdis := HeaderOwner.disjoint (ctx := ctx) hp hq heq
    simp only [isDisjointI_def] at hdis
    apply f.read <;> omega

private theorem disjointSlotWord {a slot : UInt64} {sz : Nat} {b : Buffed.IRBufContext} (off : Int64)
    (h : slot.toNat + sz ≤ b.size) (d : a.toNat + 8 ≤ slot.toNat ∨ slot.toNat + sz ≤ a.toNat)
    (ho : 0 ≤ off.toInt ∧ off.toInt + 8 ≤ sz) :
    IsDisjoint (a.toNat...(a.toNat + 8)) ((slot + off).toNat...((slot + off).toNat + 8)) := by
  have hf := b.mem.fits_in_memory
  have haddr : ((slot + off).toNat : Int) = slot.toNat + off.toInt := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [Buffed.IRBufContext.size_def]
  simp only [IsDisjoint]; omega

set_option hygiene false in
local macro "disjoint_push_reads" sz:term:max : tactic => `(tactic|
  (have h8 : 8 ≤ $sz := by decide
   have ds0 : IsDisjoint (a.toNat...(a.toNat + 8)) (slot.toNat...(slot.toNat + 8)) := by
     simp only [IsDisjoint]; omega
   repeat' rw [ExArray.read64!_blit64_disjoint _ _ _ _ _ (by
     first
     | exact dc
     | exact ds0
     | exact disjointSlotWord (slot := slot) _ hslot ds (by decide))]))

private theorem resultFrame (ptr : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo) {ib room hattrs fields} :
    let idx := ptr.impl.readCountResults! ctx.buf
    let slot := ptr.impl.getResultPtr! ctx.buf idx
    PushFrame ctx (ptr.pushResult ctx type firstUse ib room hattrs fields).buf (.op ptr.spec)
      Buffed.Operation.Offsets.countResults slot Buffed.OpResult.sizeNat := by
  dsimp only
  let idx := ptr.impl.readCountResults! ctx.buf
  let slot := ptr.impl.getResultPtr! ctx.buf idx
  have hi : idx.toNat = ptr.spec.getNumResults! ctx.spec := by
    simpa only [idx, ← ib.sim.out, Sim.IRContext.inner_def, Sim.IRContext.spec, Sim.RawIRContext.spec]
      using (ctx.countsMatch.results ptr.spec ib.ib).live
  have hslot : slot.toNat + Buffed.OpResult.sizeNat ≤ ctx.buf.size := by prove_setLinkBoundsResultSlot ctx ptr idx
  constructor
  · change (ptr.spec.rangeInt ctx.spec).lower ≤ slot.toNat
    prove_setLinkBoundsResultSlot ctx ptr idx
  · change (slot.toNat : Int) + Buffed.OpResult.sizeNat ≤ (ptr.spec.rangeInt ctx.spec).upper
    prove_setLinkBoundsResultSlot ctx ptr idx
  · left; change slot.toNat + Buffed.OpResult.sizeNat ≤ ptr.spec.toM.toNat
    prove_setLinkBoundsResultSlot ctx ptr idx
  · intro a ds dc
    change a.toNat + 8 ≤ slot.toNat ∨ slot.toNat + Buffed.OpResult.sizeNat ≤ a.toNat at ds
    simp only [HeaderOwner.base, ib.sim.out] at dc
    simp only [Sim.OperationPtr.pushResult, Buffed.OperationMPtr.pushResult,
      Buffed.OperationMPtr.writeCountResults, Buffed.OpResultMPtr.writeOwner,
      Buffed.OpResultMPtr.writeIndex, Buffed.OpResultMPtr.writeFirstUse,
      Buffed.OpResultMPtr.writeType, Buffed.OpResultMPtr.writeKind,
      Buffed.OperationMPtr.readCountResults_eq_readCountResults!,
      Buffed.OperationMPtr.getResultPtr_eq_getResultPtr!, Buffed.IRBufContext.insertAttrsBounded]
    disjoint_push_reads Buffed.OpResult.sizeNat

private theorem operandFrame (ptr : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo) {ib room fields} :
    let idx := ptr.impl.readCountOperands! ctx.buf
    let slot := ptr.impl + ptr.impl.computeOperandOffset! (OpInfo := OpInfo) ctx.buf idx
    PushFrame ctx (ptr.pushOperand ctx value nextUse back ib room fields).buf (.op ptr.spec)
      Buffed.Operation.Offsets.countOperands slot Buffed.OpOperand.sizeNat := by
  dsimp only
  let idx := ptr.impl.readCountOperands! ctx.buf
  let slot := ptr.impl + ptr.impl.computeOperandOffset! (OpInfo := OpInfo) ctx.buf idx
  have hi : idx.toNat = ptr.spec.getNumOperands! ctx.spec := by
    simpa only [idx, ← ib.sim.out, Sim.IRContext.inner_def, Sim.IRContext.spec, Sim.RawIRContext.spec]
      using (ctx.countsMatch.operands ptr.spec ib.ib).live
  have hslot : slot.toNat + Buffed.OpOperand.sizeNat ≤ ctx.buf.size := by prove_setLinkBoundsOperandSlot ctx ptr idx
  constructor
  · change (ptr.spec.rangeInt ctx.spec).lower ≤ slot.toNat
    prove_setLinkBoundsOperandSlot ctx ptr idx
  · change (slot.toNat : Int) + Buffed.OpOperand.sizeNat ≤ (ptr.spec.rangeInt ctx.spec).upper
    prove_setLinkBoundsOperandSlot ctx ptr idx
  · right; change ptr.spec.toM.toNat + Buffed.Operation.sizeBaseNat ≤ slot.toNat
    prove_setLinkBoundsOperandSlot ctx ptr idx
  · intro a ds dc
    change a.toNat + 8 ≤ slot.toNat ∨ slot.toNat + Buffed.OpOperand.sizeNat ≤ a.toNat at ds
    simp only [HeaderOwner.base, ib.sim.out] at dc
    simp only [Sim.OperationPtr.pushOperand,
      Buffed.OperationMPtr.pushOperand,
      Buffed.OperationMPtr.writeCountOperands,
      Buffed.OperationMPtr.readCountOperands_eq_readCountOperands!,
      Buffed.OperationMPtr.computeOperandOffset_eq_computeOperandOffset!,
      Buffed.OpOperandMPtr.writeNextUse,
      Buffed.OpOperandMPtr.writeBack,
      Buffed.OpOperandMPtr.writeOwner,
      Buffed.OpOperandMPtr.writeValue]
    disjoint_push_reads Buffed.OpOperand.sizeNat

private theorem blockOperandFrame (ptr : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo) {ib room fields} :
    let idx := ptr.impl.readCountBlockOperands! ctx.buf
    let slot := ptr.impl.readNthBlockOperand! (OpInfo := OpInfo) ctx.buf idx
    PushFrame ctx (ptr.pushBlockOperand ctx value nextUse back ib room fields).buf (.op ptr.spec)
      Buffed.Operation.Offsets.countBlockOperands slot Buffed.BlockOperand.sizeNat := by
  dsimp only
  let idx := ptr.impl.readCountBlockOperands! ctx.buf
  let slot := ptr.impl.readNthBlockOperand! (OpInfo := OpInfo) ctx.buf idx
  have hi : idx.toNat = ptr.spec.getNumSuccessors! ctx.spec := by
    simpa only [idx, ← ib.sim.out, Sim.IRContext.inner_def, Sim.IRContext.spec, Sim.RawIRContext.spec]
      using (ctx.countsMatch.blockOperands ptr.spec ib.ib).live
  have hslot : slot.toNat + Buffed.BlockOperand.sizeNat ≤ ctx.buf.size := by
    simp only [slot, Buffed.OperationMPtr.readNthBlockOperand!]
    prove_setLinkBoundsBlockOperandSlot ctx ptr idx
  constructor
  · change (ptr.spec.rangeInt ctx.spec).lower ≤ slot.toNat
    simp only [slot, Buffed.OperationMPtr.readNthBlockOperand!]
    prove_setLinkBoundsBlockOperandSlot ctx ptr idx
  · change (slot.toNat : Int) + Buffed.BlockOperand.sizeNat ≤ (ptr.spec.rangeInt ctx.spec).upper
    simp only [slot, Buffed.OperationMPtr.readNthBlockOperand!]
    prove_setLinkBoundsBlockOperandSlot ctx ptr idx
  · right; change ptr.spec.toM.toNat + Buffed.Operation.sizeBaseNat ≤ slot.toNat
    simp only [slot, Buffed.OperationMPtr.readNthBlockOperand!]
    prove_setLinkBoundsBlockOperandSlot ctx ptr idx
  · intro a ds dc
    change a.toNat + 8 ≤ slot.toNat ∨ slot.toNat + Buffed.BlockOperand.sizeNat ≤ a.toNat at ds
    simp only [HeaderOwner.base, ib.sim.out] at dc
    simp only [Sim.OperationPtr.pushBlockOperand,
      Buffed.OperationMPtr.pushBlockOperand,
      Buffed.OperationMPtr.writeCountBlockOperands,
      Buffed.OperationMPtr.readCountBlockOperands_eq_readCountBlockOperands!,
      Buffed.OperationMPtr.readNthBlockOperand_eq_readNthBlockOperand!,
      Buffed.BlockOperandMPtr.writeNextUse,
      Buffed.BlockOperandMPtr.writeBack,
      Buffed.BlockOperandMPtr.writeOwner,
      Buffed.BlockOperandMPtr.writeValue]
    disjoint_push_reads Buffed.BlockOperand.sizeNat

private theorem argumentFrame (ptr : Sim.BlockPtr) (ctx : Sim.IRContext OpInfo) {ib room hattrs fields} :
    let idx := ptr.impl.readCountArguments! ctx.buf
    let slot := ptr.impl.getArgumentPtr idx
    PushFrame ctx (ptr.pushArgument ctx type firstUse ib room hattrs fields).buf (.bl ptr.spec)
      Buffed.Block.Offsets.countArguments slot Buffed.BlockArgument.sizeNat := by
  dsimp only
  let idx := ptr.impl.readCountArguments! ctx.buf
  let slot := ptr.impl.getArgumentPtr idx
  have hi : idx.toNat = ptr.spec.getNumArguments! ctx.spec := by
    simpa only [idx, ← ib.sim.out, Sim.IRContext.inner_def, Sim.IRContext.spec, Sim.RawIRContext.spec]
      using (ctx.countsMatch.arguments ptr.spec ib.ib).live
  have hslot : slot.toNat + Buffed.BlockArgument.sizeNat ≤ ctx.buf.size := by prove_setLinkBoundsArgumentSlot ctx ptr idx
  constructor
  · change (ptr.spec.rangeInt ctx.spec).lower ≤ slot.toNat
    prove_setLinkBoundsArgumentSlot ctx ptr idx
  · change (slot.toNat : Int) + Buffed.BlockArgument.sizeNat ≤ (ptr.spec.rangeInt ctx.spec).upper
    prove_setLinkBoundsArgumentSlot ctx ptr idx
  · right; change ptr.spec.toM.toNat + Buffed.Block.sizeBaseNat ≤ slot.toNat
    prove_setLinkBoundsArgumentSlot ctx ptr idx
  · intro a ds dc
    change a.toNat + 8 ≤ slot.toNat ∨ slot.toNat + Buffed.BlockArgument.sizeNat ≤ a.toNat at ds
    simp only [HeaderOwner.base, ib.sim.out] at dc
    simp only [Sim.BlockPtr.pushArgument,
      Buffed.BlockMPtr.pushArgument,
      Buffed.BlockMPtr.writeCountArguments,
      Buffed.BlockMPtr.readCountArguments_eq_readCountArguments!,
      Buffed.IRBufContext.insertAttrsBounded,
      Buffed.BlockArgumentMPtr.writeKind,
      Buffed.BlockArgumentMPtr.writeType,
      Buffed.BlockArgumentMPtr.writeFirstUse,
      Buffed.BlockArgumentMPtr.writeIndex,
      Buffed.BlockArgumentMPtr.writeOwner]
    disjoint_push_reads Buffed.BlockArgument.sizeNat

private theorem regionFrame (ptr : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo) {ib room fields} :
    let idx := ptr.impl.readCountRegions! ctx.buf
    let slot := ptr.impl + ptr.impl.computeRegionOffset! (OpInfo := OpInfo) ctx.buf idx
    PushFrame ctx (ptr.pushRegion ctx region ib room fields).buf (.op ptr.spec)
      Buffed.Operation.Offsets.countRegions slot Buffed.ptrSizeNat := by
  dsimp only
  let idx := ptr.impl.readCountRegions! ctx.buf
  let slot := ptr.impl + ptr.impl.computeRegionOffset! (OpInfo := OpInfo) ctx.buf idx
  have hi : idx.toNat = ptr.spec.getNumRegions! ctx.spec := by
    simpa only [idx, ← ib.sim.out, Sim.IRContext.inner_def, Sim.IRContext.spec, Sim.RawIRContext.spec]
      using (ctx.countsMatch.regions ptr.spec ib.ib).live
  have hoff := OperationPtr.computeRegionsOffet!_plus_offset_eq_regionsInt ctx ptr.spec ib.ib (idx := idx)
    (by have := ctx.sim.repr.operations_indices ptr.spec ib.ib; grind)
  rw [ib.sim.out] at hoff
  change (ptr.impl.computeRegionOffset! (OpInfo := OpInfo) ctx.buf idx).toInt = _ at hoff
  have hslot : slot.toNat + Buffed.ptrSizeNat ≤ ctx.buf.size := by prove_setLinkBoundsRegionSlot ctx ptr idx
  constructor
  · change (ptr.spec.rangeInt ctx.spec).lower ≤ slot.toNat
    prove_setLinkBoundsRegionSlot ctx ptr idx
  · change (slot.toNat : Int) + Buffed.ptrSizeNat ≤ (ptr.spec.rangeInt ctx.spec).upper
    prove_setLinkBoundsRegionSlot ctx ptr idx
  · right; change ptr.spec.toM.toNat + Buffed.Operation.sizeBaseNat ≤ slot.toNat
    prove_setLinkBoundsRegionSlot ctx ptr idx
  · intro a ds dc
    change a.toNat + 8 ≤ slot.toNat ∨ slot.toNat + Buffed.ptrSizeNat ≤ a.toNat at ds
    simp only [HeaderOwner.base, ib.sim.out] at dc
    simp only [Sim.OperationPtr.pushRegion,
      Buffed.OperationMPtr.pushRegion,
      Buffed.OperationMPtr.writeCountRegions,
      Buffed.OperationMPtr.readCountRegions_eq_readCountRegions!,
      Buffed.OperationMPtr.writeNthRegion, Buffed.OperationMPtr.computeRegionOffset_eq_computeRegionOffset!]
    disjoint_push_reads Buffed.ptrSizeNat

set_option hygiene false in
local macro "header_row" key:term:max off:term:max maxOff:term:max old:term:max push:Lean.Parser.Tactic.simpLemma
    : tactic => `(tactic|
  (have hb : q.InBounds ctx.spec := by
     simp only [$push, Sim.RawIRContext.spec, Erased.out_mk] at hq
     grind
   have prior := $old q hb
   have maxRead := frame.header (q := $key) ib.ib hb $maxOff
     (by simp only [HeaderOwner.bytes]; decide) (by simp only [HeaderOwner.bytes]; decide)
     (by exact Or.inr (by decide))
   refine ⟨?_, ?_, ?_⟩
   · first
     | (by_cases he : q = ptr.spec; case pos => subst q; simpa only [ib.sim.out] using changed)
     | skip
     all_goals
       have hread := frame.header (q := $key) ib.ib hb $off
         (by simp only [HeaderOwner.bytes]; decide) (by simp only [HeaderOwner.bytes]; decide)
         (by first | exact Or.inr (by decide) | exact Or.inl (by grind))
       refine (congrArg UInt64.toNat hread).trans (prior.live.trans ?_)
       simp only [$push, Sim.RawIRContext.spec, Erased.out_mk]; grind
   · have := prior.bounded
     simp only [$push, Sim.RawIRContext.spec, Erased.out_mk]; grind
   · refine Eq.trans ?_ (prior.reserved.trans (congrArg UInt64.toNat maxRead.symm))
     simp only [$push, Sim.RawIRContext.spec, Erased.out_mk]; grind))

open Lean.Parser.Tactic in
set_option hygiene false in
local macro "all_header_rows" push:Lean.Parser.Tactic.simpLemma : tactic => `(tactic|
  (constructor <;> intro q hq
   · header_row (.op q) Buffed.Operation.Offsets.countResults Buffed.Operation.Offsets.numResults ctx.countsMatch.results $push:simpLemma
   · header_row (.op q) Buffed.Operation.Offsets.countOperands Buffed.Operation.Offsets.numOperands ctx.countsMatch.operands $push:simpLemma
   · header_row (.op q) Buffed.Operation.Offsets.countBlockOperands Buffed.Operation.Offsets.numBlockOperands ctx.countsMatch.blockOperands $push:simpLemma
   · header_row (.op q) Buffed.Operation.Offsets.countRegions Buffed.Operation.Offsets.numRegions ctx.countsMatch.regions $push:simpLemma
   · header_row (.bl q) Buffed.Block.Offsets.countArguments Buffed.Block.Offsets.numArguments ctx.countsMatch.arguments $push:simpLemma))

theorem Sim.OperationPtr.pushResult_countsMatch (ptr : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo)
    {ib room hattrs fields} : Sim.CountsMatch (Sim.OperationPtr.pushResult ptr ctx type firstUse ib room hattrs fields) := by
  have frame := resultFrame (ib := ib) (fields := fields) (room := room) (hattrs := hattrs) (type := type) (firstUse := firstUse) ptr ctx
  have changed := (Sim.OperationPtr.pushResult_length ptr ctx (ib := ib) (fields := fields) (room := room) (hattrs := hattrs) (type := type) (firstUse := firstUse)).1
  all_header_rows Sim.OperationPtr.pushResult

theorem Sim.OperationPtr.pushOperand_countsMatch (ptr : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo)
    {ib room fields} : Sim.CountsMatch (Sim.OperationPtr.pushOperand ptr ctx value nextUse back ib room fields) := by
  have frame := operandFrame (ib := ib) (fields := fields) (room := room) (value := value) (nextUse := nextUse) (back := back) ptr ctx
  have changed := (Sim.OperationPtr.pushOperand_length ptr ctx (ib := ib) (fields := fields) (room := room) (value := value) (nextUse := nextUse) (back := back)).1
  all_header_rows Sim.OperationPtr.pushOperand

theorem Sim.OperationPtr.pushBlockOperand_countsMatch (ptr : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo)
    {ib room fields} : Sim.CountsMatch (Sim.OperationPtr.pushBlockOperand ptr ctx value nextUse back ib room fields) := by
  have frame := blockOperandFrame (ib := ib) (fields := fields) (room := room) (value := value) (nextUse := nextUse) (back := back) ptr ctx
  have changed := (Sim.OperationPtr.pushBlockOperand_length ptr ctx (ib := ib) (fields := fields) (room := room) (value := value) (nextUse := nextUse) (back := back)).1
  all_header_rows Sim.OperationPtr.pushBlockOperand

theorem Sim.OperationPtr.pushRegion_countsMatch (ptr : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo)
    {ib room fields} : Sim.CountsMatch (Sim.OperationPtr.pushRegion ptr ctx region ib room fields) := by
  have frame := regionFrame (ib := ib) (fields := fields) (room := room) (region := region) ptr ctx
  have changed := (Sim.OperationPtr.pushRegion_length ptr ctx (ib := ib) (fields := fields) (room := room) (region := region)).1
  all_header_rows Sim.OperationPtr.pushRegion

theorem Sim.BlockPtr.pushArgument_countsMatch (ptr : Sim.BlockPtr) (ctx : Sim.IRContext OpInfo)
    {ib room hattrs fields} : Sim.CountsMatch (Sim.BlockPtr.pushArgument ptr ctx type firstUse ib room hattrs fields) := by
  have frame := argumentFrame (ib := ib) (fields := fields) (room := room) (hattrs := hattrs) (type := type) (firstUse := firstUse) ptr ctx
  have changed := (Sim.BlockPtr.pushArgument_length ptr ctx (ib := ib) (fields := fields) (room := room) (hattrs := hattrs) (type := type) (firstUse := firstUse)).1
  all_header_rows Sim.BlockPtr.pushArgument

end Veir
