module

public import Veir.IR.Buffed.RawAccessorFootprints
public import Veir.IR.Fields

/-!
# Frame lemmas for the `Matches` refinement predicates

A setter writes a single word of the buffer; every `Matches` structure whose footprint is
disjoint from that word survives unchanged. The lemmas here state this once per structure,
so a setter's `Sim` proof only has to discharge one interval-disjointness goal per section
instead of re-proving every field.
-/

set_option linter.unusedSectionVars false

public section

namespace Veir

open Veir.Buffed

variable [HasOpInfo OpInfo] [SerializableOpInfo OpInfo]

/-- `buf'` reads identically to `buf` everywhere inside `[lo, hi)`, and every attribute
lookup that succeeds in `buf` returns the same value in `buf'` (so the table may have
grown, e.g. by an `insertAttrs` push). -/
structure Buffed.AgreesOn (buf' buf : IRBufContext OpInfo) (lo hi : Nat) : Prop where
  read64 : ∀ (a : UInt64), lo ≤ a.toNat → a.toNat + 8 ≤ hi → buf'.mem.read64! a = buf.mem.read64! a
  read32 : ∀ (a : UInt64), lo ≤ a.toNat → a.toNat + 4 ≤ hi → buf'.mem.read32! a = buf.mem.read32! a
  attrs : ∀ (i : Nat) (a : Attribute), buf.attributes[i]? = some a → buf'.attributes[i]? = some a

/-- A single-`blit64` write agrees with the original buffer on any range disjoint from the
written word — the one brick every scalar setter needs to feed a `Matches` frame lemma. -/
theorem Buffed.agreesOn_blit64 (bctx : IRBufContext OpInfo) (p v : UInt64) (hb) (lo hi : Nat)
    (hd : hi ≤ p.toNat ∨ p.toNat + 8 ≤ lo) :
    AgreesOn { bctx with mem := bctx.mem.blit64 p v hb } bctx lo hi := by
  refine ⟨fun a h1 h2 => ?_, fun a h1 h2 => ?_, fun _ _ h => h⟩
  · exact ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega)
  · exact ExArray.read32!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega)

/-- Restrict an agreement to a subrange — the bridge from an allocation's
whole-old-buffer agreement to the per-record windows the frame lemmas expect. -/
theorem Buffed.AgreesOn.mono {buf' buf : IRBufContext OpInfo} {lo hi lo' hi' : Nat}
    (h : AgreesOn buf' buf lo hi) (hlo : lo ≤ lo') (hhi : hi' ≤ hi) :
    AgreesOn buf' buf lo' hi' :=
  ⟨fun a h1 h2 => h.read64 a (by omega) (by omega),
   fun a h1 h2 => h.read32 a (by omega) (by omega), h.attrs⟩

/-! ## Sum-pointer write footprints vs the framed section ranges

The three sum-typed writers (`ValuePtr`, `OpOperandPtrPtr`, `BlockOperandPtrPtr`) write one
word whose location depends on the constructor. These lemmas package the case analysis once,
so the setter macro's frame discharges stay linear. Coverage per writer: the existing
`disjoint_operation_header` lemmas handle `[op.id, op.id + operandsInt)`; the lemmas here
handle the array regions, block headers/tails and regions. -/

namespace Sim

variable {ctx : Sim.IRContext OpInfo}

theorem ValuePtr.disjoint_operation_arrays (v : Veir.ValuePtr) (ib : v.InBounds ctx.spec)
    (op : Veir.OperationPtr) (hop : op.InBounds ctx.spec) :
    IsDisjointI ((v.toFlatNat ctx.spec : Int)...((v.toFlatNat ctx.spec : Int) + Buffed.ValueImpl.sizeNat))
      (((op.id : Int) + Buffed.Operation.Offsets.operandsInt op ctx.spec)...((op.id : Int) + Buffed.Operation.Offsets.afterInt op ctx.spec)) := by
  have hrange_o := OperationPtr.range_linear op hop
  cases v with
  | opResult res =>
    have hib : res.InBounds ctx.spec := by grind [Veir.ValuePtr.InBounds]
    have hpib := OpResultPtr.op_inBounds hib
    have hsl := OpResultPtr.slot_included res hib
    have hrange_p := OperationPtr.range_linear res.op hpib
    have hdisj := fun hne : res.op ≠ op => disjoint_operation_operation res.op op hpib hop hne
    grind [Veir.ValuePtr.toFlatNat, Veir.OperationPtr.toFlat, IsIncludedI]
  | blockArgument arg =>
    have hib : arg.InBounds ctx.spec := by grind [Veir.ValuePtr.InBounds]
    have hpib := BlockArgumentPtr.block_inBounds hib
    have hsl := BlockArgumentPtr.slot_included arg hib
    have hrange_p := BlockPtr.range_linear arg.block hpib
    have hdisj := disjoint_block_operation arg.block op hpib hop
    grind [Veir.ValuePtr.toFlatNat, Veir.OperationPtr.toFlat, Veir.BlockPtr.toFlat,
      Veir.BlockPtr.rangeInt, IsIncludedI]

theorem ValuePtr.disjoint_block_header (v : Veir.ValuePtr) (ib : v.InBounds ctx.spec)
    (bl : Veir.BlockPtr) (hbl : bl.InBounds ctx.spec) :
    IsDisjointI ((v.toFlatNat ctx.spec : Int)...((v.toFlatNat ctx.spec : Int) + Buffed.ValueImpl.sizeNat))
      (((bl.id : Int))...((bl.id : Int) + Buffed.Block.Offsets.argumentsInt)) := by
  have hrange_b := BlockPtr.range_linear bl hbl
  cases v with
  | opResult res =>
    have hib : res.InBounds ctx.spec := by grind [Veir.ValuePtr.InBounds]
    have hpib := OpResultPtr.op_inBounds hib
    have hsl := OpResultPtr.slot_included res hib
    have hrange_p := OperationPtr.range_linear res.op hpib
    have hdisj := disjoint_operation_block res.op bl hpib hbl
    grind [Veir.ValuePtr.toFlatNat, Veir.OperationPtr.toFlat, Veir.BlockPtr.toFlat,
      Veir.BlockPtr.rangeInt, IsIncludedI]
  | blockArgument arg =>
    have hib : arg.InBounds ctx.spec := by grind [Veir.ValuePtr.InBounds]
    have hpib := BlockArgumentPtr.block_inBounds hib
    have hsl := BlockArgumentPtr.slot_included arg hib
    have hrange_p := BlockPtr.range_linear arg.block hpib
    have hdisj := fun hne : arg.block ≠ bl => disjoint_block_block arg.block bl hpib hbl hne
    grind [Veir.ValuePtr.toFlatNat, Veir.BlockPtr.toFlat, Veir.BlockPtr.rangeInt, IsIncludedI]

theorem ValuePtr.disjoint_region_range (v : Veir.ValuePtr) (ib : v.InBounds ctx.spec)
    (rg : Veir.RegionPtr) (hrg : rg.InBounds ctx.spec) :
    IsDisjointI ((v.toFlatNat ctx.spec : Int)...((v.toFlatNat ctx.spec : Int) + Buffed.ValueImpl.sizeNat))
      (((rg.id : Int))...((rg.id : Int) + Buffed.Region.Offsets.afterInt)) := by
  have hrange_r := RegionPtr.range_linear rg hrg
  cases v with
  | opResult res =>
    have hib : res.InBounds ctx.spec := by grind [Veir.ValuePtr.InBounds]
    have hpib := OpResultPtr.op_inBounds hib
    have hsl := OpResultPtr.slot_included res hib
    have hrange_p := OperationPtr.range_linear res.op hpib
    have hdisj := disjoint_operation_region res.op rg hpib hrg
    grind [Veir.ValuePtr.toFlatNat, Veir.OperationPtr.toFlat, Veir.RegionPtr.toFlat,
      Veir.RegionPtr.rangeInt, IsIncludedI]
  | blockArgument arg =>
    have hib : arg.InBounds ctx.spec := by grind [Veir.ValuePtr.InBounds]
    have hpib := BlockArgumentPtr.block_inBounds hib
    have hsl := BlockArgumentPtr.slot_included arg hib
    have hrange_p := BlockPtr.range_linear arg.block hpib
    have hdisj := disjoint_block_region arg.block rg hpib hrg
    grind [Veir.ValuePtr.toFlatNat, Veir.BlockPtr.toFlat, Veir.BlockPtr.rangeInt,
      Veir.RegionPtr.toFlat, Veir.RegionPtr.rangeInt, IsIncludedI]

theorem OpOperandPtrPtr.disjoint_operation_arrays_bo (p : Veir.OpOperandPtrPtr) (ib : p.InBounds ctx.spec)
    (op : Veir.OperationPtr) (hop : op.InBounds ctx.spec) :
    IsDisjointI ((p.toFlatNat ctx.spec : Int)...((p.toFlatNat ctx.spec : Int) + Buffed.ptrSizeNat))
      (((op.id : Int) + Buffed.Operation.Offsets.blockOperandsInt op ctx.spec)...((op.id : Int) + Buffed.Operation.Offsets.afterInt op ctx.spec)) := by
  have hrange_o := OperationPtr.range_linear op hop
  cases p with
  | operandNextUse opr =>
    have hib : opr.InBounds ctx.spec := by grind [Veir.OpOperandPtrPtr.InBounds]
    have hpib := OpOperandPtr.op_inBounds hib
    have hsl := OpOperandPtr.slot_included opr hib
    have hrange_p := OperationPtr.range_linear opr.op hpib
    have hdisj := fun hne : opr.op ≠ op => disjoint_operation_operation opr.op op hpib hop hne
    grind [Veir.OpOperandPtrPtr.toFlatNat, Veir.OperationPtr.toFlat, IsIncludedI]
  | valueFirstUse v =>
    have hib : v.InBounds ctx.spec := by grind [Veir.OpOperandPtrPtr.InBounds]
    have hdisj := ValuePtr.disjoint_operation_arrays v hib op hop
    grind [Veir.OpOperandPtrPtr.toFlatNat, IsIncludedI]

theorem OpOperandPtrPtr.disjoint_block_header (p : Veir.OpOperandPtrPtr) (ib : p.InBounds ctx.spec)
    (bl : Veir.BlockPtr) (hbl : bl.InBounds ctx.spec) :
    IsDisjointI ((p.toFlatNat ctx.spec : Int)...((p.toFlatNat ctx.spec : Int) + Buffed.ptrSizeNat))
      (((bl.id : Int))...((bl.id : Int) + Buffed.Block.Offsets.argumentsInt)) := by
  cases p with
  | operandNextUse opr =>
    have hib : opr.InBounds ctx.spec := by grind [Veir.OpOperandPtrPtr.InBounds]
    have hpib := OpOperandPtr.op_inBounds hib
    have hsl := OpOperandPtr.slot_included opr hib
    have hrange_p := OperationPtr.range_linear opr.op hpib
    have hdisj := disjoint_operation_block opr.op bl hpib hbl
    grind [Veir.OpOperandPtrPtr.toFlatNat, Veir.OperationPtr.toFlat, Veir.BlockPtr.toFlat,
      Veir.BlockPtr.rangeInt, IsIncludedI]
  | valueFirstUse v =>
    have hib : v.InBounds ctx.spec := by grind [Veir.OpOperandPtrPtr.InBounds]
    have hdisj := ValuePtr.disjoint_block_header v hib bl hbl
    grind [Veir.OpOperandPtrPtr.toFlatNat, IsIncludedI]

theorem OpOperandPtrPtr.disjoint_region_range (p : Veir.OpOperandPtrPtr) (ib : p.InBounds ctx.spec)
    (rg : Veir.RegionPtr) (hrg : rg.InBounds ctx.spec) :
    IsDisjointI ((p.toFlatNat ctx.spec : Int)...((p.toFlatNat ctx.spec : Int) + Buffed.ptrSizeNat))
      (((rg.id : Int))...((rg.id : Int) + Buffed.Region.Offsets.afterInt)) := by
  cases p with
  | operandNextUse opr =>
    have hib : opr.InBounds ctx.spec := by grind [Veir.OpOperandPtrPtr.InBounds]
    have hpib := OpOperandPtr.op_inBounds hib
    have hsl := OpOperandPtr.slot_included opr hib
    have hrange_p := OperationPtr.range_linear opr.op hpib
    have hdisj := disjoint_operation_region opr.op rg hpib hrg
    grind [Veir.OpOperandPtrPtr.toFlatNat, Veir.OperationPtr.toFlat, Veir.RegionPtr.toFlat,
      Veir.RegionPtr.rangeInt, IsIncludedI]
  | valueFirstUse v =>
    have hib : v.InBounds ctx.spec := by grind [Veir.OpOperandPtrPtr.InBounds]
    have hdisj := ValuePtr.disjoint_region_range v hib rg hrg
    grind [Veir.OpOperandPtrPtr.toFlatNat, IsIncludedI]

theorem BlockOperandPtrPtr.disjoint_operation_upTo_bo (p : Veir.BlockOperandPtrPtr) (ib : p.InBounds ctx.spec)
    (op : Veir.OperationPtr) (hop : op.InBounds ctx.spec) :
    IsDisjointI ((p.toFlatNat ctx.spec : Int)...((p.toFlatNat ctx.spec : Int) + Buffed.ptrSizeNat))
      (((op.id : Int) + Buffed.Operation.Offsets.resultsInt op ctx.spec)...((op.id : Int) + Buffed.Operation.Offsets.blockOperandsInt op ctx.spec)) := by
  have hrange_o := OperationPtr.range_linear op hop
  cases p with
  | blockOperandNextUse opr =>
    have hib : opr.InBounds ctx.spec := by grind [Veir.BlockOperandPtrPtr.InBounds]
    have hpib := BlockOperandPtr.op_inBounds hib
    have hsl := BlockOperandPtr.slot_included opr hib
    have hrange_p := OperationPtr.range_linear opr.op hpib
    have hdisj := fun hne : opr.op ≠ op => disjoint_operation_operation opr.op op hpib hop hne
    grind [Veir.BlockOperandPtrPtr.toFlatNat, Veir.OperationPtr.toFlat, IsIncludedI]
  | blockFirstUse bl =>
    have hib : bl.InBounds ctx.spec := by grind [Veir.BlockOperandPtrPtr.InBounds]
    have hrange_p := BlockPtr.range_linear bl hib
    have hdisj := disjoint_block_operation bl op hib hop
    grind [Veir.BlockOperandPtrPtr.toFlatNat, Veir.OperationPtr.toFlat, Veir.BlockPtr.toFlat,
      Veir.BlockPtr.rangeInt, IsIncludedI]

theorem BlockOperandPtrPtr.disjoint_operation_regions (p : Veir.BlockOperandPtrPtr) (ib : p.InBounds ctx.spec)
    (op : Veir.OperationPtr) (hop : op.InBounds ctx.spec) :
    IsDisjointI ((p.toFlatNat ctx.spec : Int)...((p.toFlatNat ctx.spec : Int) + Buffed.ptrSizeNat))
      (((op.id : Int) + Buffed.Operation.Offsets.regionsInt op ctx.spec)...((op.id : Int) + Buffed.Operation.Offsets.afterInt op ctx.spec)) := by
  have hrange_o := OperationPtr.range_linear op hop
  cases p with
  | blockOperandNextUse opr =>
    have hib : opr.InBounds ctx.spec := by grind [Veir.BlockOperandPtrPtr.InBounds]
    have hpib := BlockOperandPtr.op_inBounds hib
    have hsl := BlockOperandPtr.slot_included opr hib
    have hrange_p := OperationPtr.range_linear opr.op hpib
    have hdisj := fun hne : opr.op ≠ op => disjoint_operation_operation opr.op op hpib hop hne
    grind [Veir.BlockOperandPtrPtr.toFlatNat, Veir.OperationPtr.toFlat, IsIncludedI]
  | blockFirstUse bl =>
    have hib : bl.InBounds ctx.spec := by grind [Veir.BlockOperandPtrPtr.InBounds]
    have hrange_p := BlockPtr.range_linear bl hib
    have hdisj := disjoint_block_operation bl op hib hop
    grind [Veir.BlockOperandPtrPtr.toFlatNat, Veir.OperationPtr.toFlat, Veir.BlockPtr.toFlat,
      Veir.BlockPtr.rangeInt, IsIncludedI]

theorem BlockOperandPtrPtr.disjoint_block_tail (p : Veir.BlockOperandPtrPtr) (ib : p.InBounds ctx.spec)
    (bl : Veir.BlockPtr) (hbl : bl.InBounds ctx.spec) :
    IsDisjointI ((p.toFlatNat ctx.spec : Int)...((p.toFlatNat ctx.spec : Int) + Buffed.ptrSizeNat))
      (((bl.id : Int) + 8)...((bl.id : Int) + Buffed.Block.Offsets.afterInt bl ctx.spec)) := by
  have hrange_b := BlockPtr.range_linear bl hbl
  cases p with
  | blockOperandNextUse opr =>
    have hib : opr.InBounds ctx.spec := by grind [Veir.BlockOperandPtrPtr.InBounds]
    have hpib := BlockOperandPtr.op_inBounds hib
    have hsl := BlockOperandPtr.slot_included opr hib
    have hrange_p := OperationPtr.range_linear opr.op hpib
    have hdisj := disjoint_operation_block opr.op bl hpib hbl
    grind [Veir.BlockOperandPtrPtr.toFlatNat, Veir.OperationPtr.toFlat, Veir.BlockPtr.toFlat,
      Veir.BlockPtr.rangeInt, IsIncludedI]
  | blockFirstUse bl' =>
    have hib : bl'.InBounds ctx.spec := by grind [Veir.BlockOperandPtrPtr.InBounds]
    have hrange_p := BlockPtr.range_linear bl' hib
    have hdisj := fun hne : bl' ≠ bl => disjoint_block_block bl' bl hib hbl hne
    grind [Veir.BlockOperandPtrPtr.toFlatNat, Veir.BlockPtr.toFlat, Veir.BlockPtr.rangeInt, IsIncludedI]

theorem BlockOperandPtrPtr.disjoint_region_range (p : Veir.BlockOperandPtrPtr) (ib : p.InBounds ctx.spec)
    (rg : Veir.RegionPtr) (hrg : rg.InBounds ctx.spec) :
    IsDisjointI ((p.toFlatNat ctx.spec : Int)...((p.toFlatNat ctx.spec : Int) + Buffed.ptrSizeNat))
      (((rg.id : Int))...((rg.id : Int) + Buffed.Region.Offsets.afterInt)) := by
  cases p with
  | blockOperandNextUse opr =>
    have hib : opr.InBounds ctx.spec := by grind [Veir.BlockOperandPtrPtr.InBounds]
    have hpib := BlockOperandPtr.op_inBounds hib
    have hsl := BlockOperandPtr.slot_included opr hib
    have hrange_p := OperationPtr.range_linear opr.op hpib
    have hdisj := disjoint_operation_region opr.op rg hpib hrg
    grind [Veir.BlockOperandPtrPtr.toFlatNat, Veir.OperationPtr.toFlat, Veir.RegionPtr.toFlat,
      Veir.RegionPtr.rangeInt, IsIncludedI]
  | blockFirstUse bl =>
    have hib : bl.InBounds ctx.spec := by grind [Veir.BlockOperandPtrPtr.InBounds]
    have hrange_p := BlockPtr.range_linear bl hib
    have hdisj := disjoint_block_region bl rg hib hrg
    grind [Veir.BlockOperandPtrPtr.toFlatNat, Veir.BlockPtr.toFlat, Veir.BlockPtr.rangeInt,
      Veir.RegionPtr.toFlat, Veir.RegionPtr.rangeInt, IsIncludedI]

end Sim

/-! ## Slot structures (parented by an operation or a block) -/

/-- `OpOperandPtr.Matches` survives any buffer change that agrees on the slot's 32-byte
footprint and any layout-preserving spec change that fixes the slot value. -/
theorem OpOperandPtr.matches_frame (ctx : Sim.IRContext OpInfo)
    {buf' : Buffed.IRBufContext OpInfo} {spec' : IRContext OpInfo}
    (oper : OpOperandPtr) (ib : oper.InBounds ctx.spec)
    (hm : oper.Matches ⟨ctx.buf, ctx.spec⟩ ib)
    (hagree : Buffed.AgreesOn buf' ctx.buf (oper.toFlatNat ctx.spec) (oper.toFlatNat ctx.spec + 32))
    (hlay : ctx.spec.LayoutPreserved spec')
    (hget : oper.get! spec' = oper.get! ctx.spec)
    (ib' : oper.InBounds spec') :
    oper.Matches ⟨buf', spec'⟩ ib' := by
  have hFIB := Veir.Sim.IRContext.fieldsInBounds ctx
  have hfib := OpOperandPtr.get_fieldsInBounds ctx.spec oper hFIB ib
  have htoM := OpOperandPtr.layoutPreserved_same_toM hlay ib
  have htoO := OpOperandPtr.layoutPreserved_same_toO hlay ((Option.maybe_def _ _ _).mp hfib.nextUse_inBounds)
  have htoM_b := OpOperandPtrPtr.layoutPreserved_same_toM hlay hfib.back_inBounds
  have htoM_v := ValuePtr.layoutPreserved_same_toM hlay hfib.value_inBounds
  have haddr := Sim.OpOperandPtr.toM_toNat oper ib
  have hincl := Sim.OpOperandPtr.slot_included oper ib
  have hpib := Sim.OpOperandPtr.op_inBounds ib
  have hrange := Sim.OperationPtr.range_linear oper.op hpib
  have hsize := Sim.IRContext.mem_size_lt ctx
  have hnu := hagree.read64 (oper.toM ctx.spec + Buffed.OpOperand.Offsets.nextUse) (by grind) (by grind)
  have hba := hagree.read64 (oper.toM ctx.spec + Buffed.OpOperand.Offsets.back) (by grind) (by grind)
  have how := hagree.read64 (oper.toM ctx.spec + Buffed.OpOperand.Offsets.owner) (by grind) (by grind)
  have hva := hagree.read64 (oper.toM ctx.spec + Buffed.OpOperand.Offsets.value) (by grind) (by grind)
  constructor
  · have := hm.nextUse
    grind [Buffed.OpOperandMPtr.readNextUse!]
  · have := hm.back
    grind [Buffed.OpOperandMPtr.readBack!]
  · have := hm.owner
    grind [Buffed.OpOperandMPtr.readOwner!]
  · have := hm.value
    grind [Buffed.OpOperandMPtr.readValue!]

/-- `BlockOperandPtr.Matches` survives any buffer change agreeing on the slot's 32-byte
footprint and any layout-preserving spec change fixing the slot value. -/
theorem BlockOperandPtr.matches_frame (ctx : Sim.IRContext OpInfo)
    {buf' : Buffed.IRBufContext OpInfo} {spec' : IRContext OpInfo}
    (oper : BlockOperandPtr) (ib : oper.InBounds ctx.spec)
    (hm : oper.Matches ⟨ctx.buf, ctx.spec⟩ ib)
    (hagree : Buffed.AgreesOn buf' ctx.buf (oper.toFlatNat ctx.spec) (oper.toFlatNat ctx.spec + 32))
    (hlay : ctx.spec.LayoutPreserved spec')
    (hget : oper.get! spec' = oper.get! ctx.spec)
    (ib' : oper.InBounds spec') :
    oper.Matches ⟨buf', spec'⟩ ib' := by
  have hFIB := Veir.Sim.IRContext.fieldsInBounds ctx
  have hfib := BlockOperandPtr.get_fieldsInBounds ctx.spec oper hFIB ib
  have htoM := BlockOperandPtr.layoutPreserved_same_toM hlay ib
  have htoO := BlockOperandPtr.layoutPreserved_same_toO hlay ((Option.maybe_def _ _ _).mp hfib.nextUse_inBounds)
  have htoM_b := BlockOperandPtrPtr.layoutPreserved_same_toM hlay hfib.back_inBounds
  have haddr := Sim.BlockOperandPtr.toM_toNat oper ib
  have hincl := Sim.BlockOperandPtr.slot_included oper ib
  have hpib := Sim.BlockOperandPtr.op_inBounds ib
  have hrange := Sim.OperationPtr.range_linear oper.op hpib
  have hsize := Sim.IRContext.mem_size_lt ctx
  have hnu := hagree.read64 (oper.toM ctx.spec + Buffed.BlockOperand.Offsets.nextUse) (by grind) (by grind)
  have hba := hagree.read64 (oper.toM ctx.spec + Buffed.BlockOperand.Offsets.back) (by grind) (by grind)
  have how := hagree.read64 (oper.toM ctx.spec + Buffed.BlockOperand.Offsets.owner) (by grind) (by grind)
  have hva := hagree.read64 (oper.toM ctx.spec + Buffed.BlockOperand.Offsets.value) (by grind) (by grind)
  constructor
  · have := hm.nextUse
    grind [Buffed.BlockOperandMPtr.readNextUse!]
  · have := hm.back
    grind [Buffed.BlockOperandMPtr.readBack!]
  · have := hm.owner
    grind [Buffed.BlockOperandMPtr.readOwner!]
  · have := hm.value
    grind [Buffed.BlockOperandMPtr.readValue!]

/-- `OpResultPtr.Matches` survives any buffer change agreeing on the slot's 40-byte
footprint and any layout-preserving spec change fixing the slot value. -/
theorem OpResultPtr.matches_frame (ctx : Sim.IRContext OpInfo)
    {buf' : Buffed.IRBufContext OpInfo} {spec' : IRContext OpInfo}
    (res : OpResultPtr) (ib : res.InBounds ctx.spec)
    (hm : OpResultPtr.Matches ⟨ctx.buf, ctx.spec⟩ res ib)
    (hagree : Buffed.AgreesOn buf' ctx.buf (res.toFlatNat ctx.spec) (res.toFlatNat ctx.spec + 40))
    (hlay : ctx.spec.LayoutPreserved spec')
    (hget : res.get! spec' = res.get! ctx.spec)
    (ib' : res.InBounds spec') :
    OpResultPtr.Matches ⟨buf', spec'⟩ res ib' := by
  have hFIB := Veir.Sim.IRContext.fieldsInBounds ctx
  have hfib := OpResultPtr.get_fieldsInBounds ctx.spec res hFIB ib
  have htoM := OpResultPtr.layoutPreserved_same_toM hlay ib
  have htoO := OpOperandPtr.layoutPreserved_same_toO hlay ((Option.maybe_def _ _ _).mp hfib.firstUse_inBounds)
  have haddr := Sim.OpResultPtr.toM_toNat res ib
  have hincl := Sim.OpResultPtr.slot_included res ib
  have hpib := Sim.OpResultPtr.op_inBounds ib
  have hrange := Sim.OperationPtr.range_linear res.op hpib
  have hsize := Sim.IRContext.mem_size_lt ctx
  have hki := hagree.read64 (res.toM ctx.spec) (by grind) (by grind)
  have hty := hagree.read64 (res.toM ctx.spec + Buffed.ValueImpl.Offsets.type) (by grind) (by grind)
  have hfu := hagree.read64 (res.toM ctx.spec + Buffed.ValueImpl.Offsets.firstUse) (by grind) (by grind)
  have hix := hagree.read64 (res.toM ctx.spec + Buffed.OpResult.Offsets.index) (by grind) (by grind)
  have how := hagree.read64 (res.toM ctx.spec + Buffed.OpResult.Offsets.owner) (by grind) (by grind)
  have hat := hagree.attrs
  constructor
  · have := hm.kind
    grind [Buffed.OpResultMPtr.readKind!]
  · have := hm.typee
    grind [Buffed.OpResultMPtr.readType!]
  · have := hm.firstUse
    grind [Buffed.OpResultMPtr.readFirstUse!]
  · have := hm.index
    grind [Buffed.OpResultMPtr.readIndex!]
  · have := hm.owner
    grind [Buffed.OpResultMPtr.readOwner!]

/-- `BlockArgumentPtr.Matches` survives any buffer change agreeing on the slot's 40-byte
footprint (`loc` is 0-sized, so the slot is ValueImpl + index + owner) and any
layout-preserving spec change fixing the slot value. -/
theorem BlockArgumentPtr.matches_frame (ctx : Sim.IRContext OpInfo)
    {buf' : Buffed.IRBufContext OpInfo} {spec' : IRContext OpInfo}
    (arg : BlockArgumentPtr) (ib : arg.InBounds ctx.spec)
    (hm : BlockArgumentPtr.Matches ⟨ctx.buf, ctx.spec⟩ arg ib)
    (hagree : Buffed.AgreesOn buf' ctx.buf arg.toFlatNat (arg.toFlatNat + 40))
    (hlay : ctx.spec.LayoutPreserved spec')
    (hget : arg.get! spec' = arg.get! ctx.spec)
    (ib' : arg.InBounds spec') :
    BlockArgumentPtr.Matches ⟨buf', spec'⟩ arg ib' := by
  have hFIB := Veir.Sim.IRContext.fieldsInBounds ctx
  have hfib := BlockArgumentPtr.get_fieldsInBounds ctx.spec arg hFIB ib
  have htoO := OpOperandPtr.layoutPreserved_same_toO hlay ((Option.maybe_def _ _ _).mp hfib.firstUse_inBounds)
  have haddr := Sim.BlockArgumentPtr.toM_toNat arg ib
  have hincl := Sim.BlockArgumentPtr.slot_included arg ib
  have hpib := Sim.BlockArgumentPtr.block_inBounds ib
  have hrange := Sim.BlockPtr.range_linear arg.block hpib
  have hsize := Sim.IRContext.mem_size_lt ctx
  have hki := hagree.read64 arg.toM (by grind) (by grind)
  have hty := hagree.read64 (arg.toM + Buffed.ValueImpl.Offsets.type) (by grind) (by grind)
  have hfu := hagree.read64 (arg.toM + Buffed.ValueImpl.Offsets.firstUse) (by grind) (by grind)
  have hix := hagree.read64 (arg.toM + Buffed.BlockArgument.Offsets.index) (by grind) (by grind)
  have how := hagree.read64 (arg.toM + Buffed.BlockArgument.Offsets.owner) (by grind) (by grind)
  have hat := hagree.attrs
  constructor
  · have := hm.kind
    grind [Buffed.BlockArgumentMPtr.readKind!]
  · have := hm.type
    grind [Buffed.BlockArgumentMPtr.readType!]
  · have := hm.firstUse
    grind [Buffed.BlockArgumentMPtr.readFirstUse!]
  · have := hm.index
    grind [Buffed.BlockArgumentMPtr.readIndex!]
  · have := hm.owner
    grind [Buffed.BlockArgumentMPtr.readOwner!]

/-! ## Header structures (fixed offsets from the pointer's own address) -/

/-- `OperationPtr.MatchesBase` survives any buffer change agreeing on the 72-byte header
and any layout-preserving spec change fixing the op. -/
theorem OperationPtr.matchesBase_frame (ctx : Sim.IRContext OpInfo)
    {buf' : Buffed.IRBufContext OpInfo} {spec' : IRContext OpInfo}
    (op : OperationPtr) (ib : op.InBounds ctx.spec)
    (hm : OperationPtr.MatchesBase ⟨ctx.buf, ctx.spec⟩ op ib)
    (hagree : Buffed.AgreesOn buf' ctx.buf op.id (op.id + 72))
    (_hlay : ctx.spec.LayoutPreserved spec')
    (hgprev : (op.get! spec').prev = (op.get! ctx.spec).prev)
    (hgnext : (op.get! spec').next = (op.get! ctx.spec).next)
    (hgparent : (op.get! spec').parent = (op.get! ctx.spec).parent)
    (hgattrs : (op.get! spec').attrs = (op.get! ctx.spec).attrs)
    (hgetTy : op.getOpType! spec' = op.getOpType! ctx.spec)
    (ib' : op.InBounds spec') :
    OperationPtr.MatchesBase ⟨buf', spec'⟩ op ib' := by
  have hrepr := ctx.sim.repr.operations op ib
  have hrange := Sim.OperationPtr.range_linear op ib
  have hsize := Sim.IRContext.mem_size_lt ctx
  have hprev := hagree.read64 (op.toM + Buffed.Operation.Offsets.prev) (by grind [Veir.OperationPtr.toM]) (by grind [Veir.OperationPtr.toM])
  have hnext := hagree.read64 (op.toM + Buffed.Operation.Offsets.next) (by grind [Veir.OperationPtr.toM]) (by grind [Veir.OperationPtr.toM])
  have hparent := hagree.read64 (op.toM + Buffed.Operation.Offsets.parent) (by grind [Veir.OperationPtr.toM]) (by grind [Veir.OperationPtr.toM])
  have hoptype := hagree.read32 (op.toM + Buffed.Operation.Offsets.opType) (by grind [Veir.OperationPtr.toM]) (by grind [Veir.OperationPtr.toM])
  have hattrs := hagree.read64 (op.toM + Buffed.Operation.Offsets.attrs) (by grind [Veir.OperationPtr.toM]) (by grind [Veir.OperationPtr.toM])
  have hattrT := hagree.attrs
  constructor
  · have := hm.prev
    grind [Buffed.OperationMPtr.readPrev!]
  · have := hm.next
    grind [Buffed.OperationMPtr.readNext!]
  · have := hm.parent
    grind [Buffed.OperationMPtr.readParent!]
  · have := hm.opType
    grind [Buffed.OperationMPtr.readOpType!]
  · have := hm.attrs
    grind [Buffed.OperationMPtr.readAttrs!]

/-- `BlockPtr.MatchesBase` survives any buffer change agreeing on the 56-byte header and
any layout-preserving spec change fixing the block. -/
theorem BlockPtr.matchesBase_frame (ctx : Sim.IRContext OpInfo)
    {buf' : Buffed.IRBufContext OpInfo} {spec' : IRContext OpInfo}
    (bl : BlockPtr) (ib : bl.InBounds ctx.spec)
    (hm : BlockPtr.MatchesBase ⟨ctx.buf, ctx.spec⟩ bl ib)
    (hagree : Buffed.AgreesOn buf' ctx.buf bl.id (bl.id + 56))
    (hlay : ctx.spec.LayoutPreserved spec')
    (hgfirstUse : (bl.get! spec').firstUse = (bl.get! ctx.spec).firstUse)
    (hgprev : (bl.get! spec').prev = (bl.get! ctx.spec).prev)
    (hgnext : (bl.get! spec').next = (bl.get! ctx.spec).next)
    (hgparent : (bl.get! spec').parent = (bl.get! ctx.spec).parent)
    (hgfirstOp : (bl.get! spec').firstOp = (bl.get! ctx.spec).firstOp)
    (hglastOp : (bl.get! spec').lastOp = (bl.get! ctx.spec).lastOp)
    (ib' : bl.InBounds spec') :
    BlockPtr.MatchesBase ⟨buf', spec'⟩ bl ib' := by
  have hFIB := Veir.Sim.IRContext.fieldsInBounds ctx
  have hfib := BlockPtr.get_fieldsInBounds ctx.spec bl hFIB ib
  have htoO := BlockOperandPtr.layoutPreserved_same_toO hlay ((Option.maybe_def _ _ _).mp hfib.firstUse_inBounds)
  have hrepr := ctx.sim.repr.blocks bl ib
  have hrange := Sim.BlockPtr.range_linear bl ib
  have hsize := Sim.IRContext.mem_size_lt ctx
  have hfu := hagree.read64 (bl.toM + Buffed.Block.Offsets.firstUse) (by grind [Veir.BlockPtr.toM]) (by grind [Veir.BlockPtr.toM])
  have hprev := hagree.read64 (bl.toM + Buffed.Block.Offsets.prev) (by grind [Veir.BlockPtr.toM]) (by grind [Veir.BlockPtr.toM])
  have hnext := hagree.read64 (bl.toM + Buffed.Block.Offsets.next) (by grind [Veir.BlockPtr.toM]) (by grind [Veir.BlockPtr.toM])
  have hparent := hagree.read64 (bl.toM + Buffed.Block.Offsets.parent) (by grind [Veir.BlockPtr.toM]) (by grind [Veir.BlockPtr.toM])
  have hfop := hagree.read64 (bl.toM + Buffed.Block.Offsets.firstOp) (by grind [Veir.BlockPtr.toM]) (by grind [Veir.BlockPtr.toM])
  have hlop := hagree.read64 (bl.toM + Buffed.Block.Offsets.lastOp) (by grind [Veir.BlockPtr.toM]) (by grind [Veir.BlockPtr.toM])
  constructor
  · have := hm.firstUse
    grind [Buffed.BlockMPtr.readFirstUse!]
  · have := hm.prev
    grind [Buffed.BlockMPtr.readPrev!]
  · have := hm.next
    grind [Buffed.BlockMPtr.readNext!]
  · have := hm.parent
    grind [Buffed.BlockMPtr.readParent!]
  · have := hm.firstOp
    grind [Buffed.BlockMPtr.readFirstOp!]
  · have := hm.lastOp
    grind [Buffed.BlockMPtr.readLastOp!]

/-- `RegionPtr.Matches` survives any buffer change agreeing on the 24-byte region record
and any layout-preserving spec change fixing the region. -/
theorem RegionPtr.matches_frame (ctx : Sim.IRContext OpInfo)
    {buf' : Buffed.IRBufContext OpInfo} {spec' : IRContext OpInfo}
    (rg : RegionPtr) (ib : rg.InBounds ctx.spec)
    (hm : rg.Matches ⟨ctx.buf, ctx.spec⟩ ib)
    (hagree : Buffed.AgreesOn buf' ctx.buf rg.id (rg.id + 24))
    (_hlay : ctx.spec.LayoutPreserved spec')
    (hget : rg.get! spec' = rg.get! ctx.spec)
    (ib' : rg.InBounds spec') :
    rg.Matches ⟨buf', spec'⟩ ib' := by
  have hrepr := ctx.sim.repr.regions rg ib
  have hrange := Sim.RegionPtr.range_linear rg ib
  have hsize := Sim.IRContext.mem_size_lt ctx
  have hfb := hagree.read64 (rg.toM + Buffed.Region.Offsets.firstBlock) (by grind [Veir.RegionPtr.toM]) (by grind [Veir.RegionPtr.toM])
  have hlb := hagree.read64 (rg.toM + Buffed.Region.Offsets.lastBlock) (by grind [Veir.RegionPtr.toM]) (by grind [Veir.RegionPtr.toM])
  have hparent := hagree.read64 (rg.toM + Buffed.Region.Offsets.parent) (by grind [Veir.RegionPtr.toM]) (by grind [Veir.RegionPtr.toM])
  constructor
  · have := hm.firstBlock
    grind [Buffed.RegionMPtr.readFirstBlock!]
  · have := hm.lastBlock
    grind [Buffed.RegionMPtr.readLastBlock!]
  · have := hm.parent
    grind [Buffed.RegionMPtr.readParent!]

/-! ## Single count fields (word-level, so they survive writes to *other* header words of
the same parent — needed when the written field and the count share a header) -/

/-- The `capResults` count survives any buffer change agreeing on the count's word at
offset 0 of the header. -/
theorem OperationPtr.numResults_frame (ctx : Sim.IRContext OpInfo)
    {buf' : Buffed.IRBufContext OpInfo} {spec' : IRContext OpInfo}
    (op : OperationPtr) (ib : op.InBounds ctx.spec)
    (hm : (op.get! ctx.spec).capResults = (op.toM.readNumResults! ctx.buf).toNat)
    (hagree : Buffed.AgreesOn buf' ctx.buf op.id (op.id + 8))
    (hcap : (op.get! spec').capResults = (op.get! ctx.spec).capResults) :
    (op.get! spec').capResults = (op.toM.readNumResults! buf').toNat := by
  have hrepr := ctx.sim.repr.operations op ib
  have hrange := Sim.OperationPtr.range_linear op ib
  have hsize := Sim.IRContext.mem_size_lt ctx
  have h := hagree.read64 (op.toM + Buffed.Operation.Offsets.numResults) (by grind [Veir.OperationPtr.toM]) (by grind [Veir.OperationPtr.toM])
  grind [Buffed.OperationMPtr.readNumResults!]

/-- The `capBlockOperands` count survives any buffer change agreeing on the count's word
at offset 40 of the header. -/
theorem OperationPtr.numBlockOperands_frame (ctx : Sim.IRContext OpInfo)
    {buf' : Buffed.IRBufContext OpInfo} {spec' : IRContext OpInfo}
    (op : OperationPtr) (ib : op.InBounds ctx.spec)
    (hm : (op.get! ctx.spec).capBlockOperands = (op.toM.readNumBlockOperands! ctx.buf).toNat)
    (hagree : Buffed.AgreesOn buf' ctx.buf (op.id + 40) (op.id + 48))
    (hcap : (op.get! spec').capBlockOperands = (op.get! ctx.spec).capBlockOperands) :
    (op.get! spec').capBlockOperands = (op.toM.readNumBlockOperands! buf').toNat := by
  have hrepr := ctx.sim.repr.operations op ib
  have hrange := Sim.OperationPtr.range_linear op ib
  have hsize := Sim.IRContext.mem_size_lt ctx
  have h := hagree.read64 (op.toM + Buffed.Operation.Offsets.numBlockOperands) (by grind [Veir.OperationPtr.toM]) (by grind [Veir.OperationPtr.toM])
  grind [Buffed.OperationMPtr.readNumBlockOperands!]

/-- The `capRegions` count survives any buffer change agreeing on the count's word at
offset 48 of the header. -/
theorem OperationPtr.numRegions_frame (ctx : Sim.IRContext OpInfo)
    {buf' : Buffed.IRBufContext OpInfo} {spec' : IRContext OpInfo}
    (op : OperationPtr) (ib : op.InBounds ctx.spec)
    (hm : (op.get! ctx.spec).capRegions = (op.toM.readNumRegions! ctx.buf).toNat)
    (hagree : Buffed.AgreesOn buf' ctx.buf (op.id + 48) (op.id + 56))
    (hcap : (op.get! spec').capRegions = (op.get! ctx.spec).capRegions) :
    (op.get! spec').capRegions = (op.toM.readNumRegions! buf').toNat := by
  have hrepr := ctx.sim.repr.operations op ib
  have hrange := Sim.OperationPtr.range_linear op ib
  have hsize := Sim.IRContext.mem_size_lt ctx
  have h := hagree.read64 (op.toM + Buffed.Operation.Offsets.numRegions) (by grind [Veir.OperationPtr.toM]) (by grind [Veir.OperationPtr.toM])
  grind [Buffed.OperationMPtr.readNumRegions!]

/-- The `capOperands` count survives any buffer change agreeing on the count's word at
offset 56 of the header. -/
theorem OperationPtr.numOperands_frame (ctx : Sim.IRContext OpInfo)
    {buf' : Buffed.IRBufContext OpInfo} {spec' : IRContext OpInfo}
    (op : OperationPtr) (ib : op.InBounds ctx.spec)
    (hm : (op.get! ctx.spec).capOperands = (op.toM.readNumOperands! ctx.buf).toNat)
    (hagree : Buffed.AgreesOn buf' ctx.buf (op.id + 56) (op.id + 64))
    (hcap : (op.get! spec').capOperands = (op.get! ctx.spec).capOperands) :
    (op.get! spec').capOperands = (op.toM.readNumOperands! buf').toNat := by
  have hrepr := ctx.sim.repr.operations op ib
  have hrange := Sim.OperationPtr.range_linear op ib
  have hsize := Sim.IRContext.mem_size_lt ctx
  have h := hagree.read64 (op.toM + Buffed.Operation.Offsets.numOperands) (by grind [Veir.OperationPtr.toM]) (by grind [Veir.OperationPtr.toM])
  grind [Buffed.OperationMPtr.readNumOperands!]

/-- The `capArguments` count survives any buffer change agreeing on the count's word at
offset 48 of the block header. -/
theorem BlockPtr.numArguments_frame (ctx : Sim.IRContext OpInfo)
    {buf' : Buffed.IRBufContext OpInfo} {spec' : IRContext OpInfo}
    (bl : BlockPtr) (ib : bl.InBounds ctx.spec)
    (hm : (bl.get! ctx.spec).capArguments = (Buffed.BlockMPtr.readNumArguments! ctx.buf bl.toM).toNat)
    (hagree : Buffed.AgreesOn buf' ctx.buf (bl.id + 48) (bl.id + 56))
    (hcap : (bl.get! spec').capArguments = (bl.get! ctx.spec).capArguments) :
    (bl.get! spec').capArguments = (Buffed.BlockMPtr.readNumArguments! buf' bl.toM).toNat := by
  have hrepr := ctx.sim.repr.blocks bl ib
  have hrange := Sim.BlockPtr.range_linear bl ib
  have hsize := Sim.IRContext.mem_size_lt ctx
  have h := hagree.read64 (bl.toM + Buffed.Block.Offsets.numArguments) (by grind [Veir.BlockPtr.toM]) (by grind [Veir.BlockPtr.toM])
  grind [Buffed.BlockMPtr.readNumArguments!]

/-! ## The region-array slot (dynamic offset computed from header reads) -/

/-- The `idx`-th region link survives any buffer change that agrees on the three header
words feeding `computeRegionsOffset!` (`opType`, `numBlockOperands`, `numOperands`, all
inside `[op.id + 32, op.id + 64)`) and on the slot's word in the region array, plus any
spec change fixing the region value. -/
theorem OperationPtr.nthRegion_frame (ctx : Sim.IRContext OpInfo)
    {buf' : Buffed.IRBufContext OpInfo} {spec' : IRContext OpInfo}
    (op : OperationPtr) (ib : op.InBounds ctx.spec) (idx : Nat)
    (hnr : idx < op.getNumRegions! ctx.spec)
    (hm : Sim.RegionPtr.Sim ⟨Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM idx.toUInt64, op.getRegion! ctx.spec idx⟩)
    (hagreeHdr : Buffed.AgreesOn buf' ctx.buf (op.id + 32) (op.id + 64))
    (hagreeArr : Buffed.AgreesOn buf' ctx.buf
      (op.id + 72 + (Buffed.Operation.propertySize (op.getOpType! ctx.spec)).toNat
        + 32 * (op.get! ctx.spec).capOperands + 32 * (op.get! ctx.spec).capBlockOperands + 8 * idx)
      (op.id + 72 + (Buffed.Operation.propertySize (op.getOpType! ctx.spec)).toNat
        + 32 * (op.get! ctx.spec).capOperands + 32 * (op.get! ctx.spec).capBlockOperands + 8 * idx + 8))
    (hreg : op.getRegion! spec' idx = op.getRegion! ctx.spec idx) :
    Sim.RegionPtr.Sim ⟨Buffed.OperationMPtr.readNthRegion! buf' op.toM idx.toUInt64, op.getRegion! spec' idx⟩ := by
  have hrepr := ctx.sim.repr.operations op ib
  have hind := ctx.sim.repr.operations_indices op ib
  have hidx : idx < (op.get! ctx.spec).capRegions := by
    have := hind.capRegions
    grind
  have hsize := Sim.IRContext.mem_size_lt ctx
  have hrange := Sim.OperationPtr.range_linear op ib
  have hlt := Sim.OperationPtr.after_lt_ctx op ib
  have hty := hagreeHdr.read32 (op.toM + Buffed.Operation.Offsets.opType)
    (by grind [Veir.OperationPtr.toM]) (by grind [Veir.OperationPtr.toM])
  have hbo := hagreeHdr.read64 (op.toM + Buffed.Operation.Offsets.numBlockOperands)
    (by grind [Veir.OperationPtr.toM]) (by grind [Veir.OperationPtr.toM])
  have hoo := hagreeHdr.read64 (op.toM + Buffed.Operation.Offsets.numOperands)
    (by grind [Veir.OperationPtr.toM]) (by grind [Veir.OperationPtr.toM])
  have hoff : Buffed.OperationMPtr.computeRegionsOffset! buf' op.toM
      = Buffed.OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
    simp only [Buffed.OperationMPtr.computeRegionsOffset!,
      Buffed.OperationMPtr.computeBlockOperandsOffset!, Buffed.OperationMPtr.computeOperandsOffset!]
    grind [Buffed.OperationMPtr.readOpType!, Buffed.OperationMPtr.readNumOperands!,
      Buffed.OperationMPtr.readNumBlockOperands!]
  have hplus := OperationPtr.computeRegionsOffet!_plus_offset_eq_regionsInt ctx op ib
    (idx := idx.toUInt64) (by grind)
  have haddr : ((op.toM + (Buffed.OperationMPtr.computeRegionsOffset! ctx.buf op.toM + Buffed.ptrSize * idx.toUInt64)).toNat : Int)
      = op.id + (Buffed.Operation.Offsets.regionsInt op ctx.spec + Buffed.ptrSizeNat * idx) := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;>
      grind [Veir.OperationPtr.toM, Veir.OperationPtr.toFlat]
  have harr := hagreeArr.read64
    (op.toM + (Buffed.OperationMPtr.computeRegionsOffset! ctx.buf op.toM + Buffed.ptrSize * idx.toUInt64))
    (by grind) (by grind)
  simp only [Buffed.OperationMPtr.readNthRegion!, Buffed.OperationMPtr.computeRegionOffset!] at hm ⊢
  rw [Sim.RegionPtr.Sim_def] at hm ⊢
  rw [hoff, harr, hreg]
  exact hm

end Veir
