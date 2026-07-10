module

public import ExArray.CompilerExtras
public import Veir.IR
public import Veir.Rewriter.LinkedList.Basic
public import Veir.Rewriter.LinkedList.GetSet

meta import Veir.IR.Buffed.Basic
import Veir.IR.Buffed.RawAccessorsLemmas
import Veir.IR.Buffed.Meta
import Veir.IR.Buffed.InBounds
import Veir.Rewriter.LinkedList.LayoutUnchanged
import all Veir.IR.Basic
import all Veir.Rewriter.LinkedList.Basic
import all Veir.IR.Buffed.Basic
import all Veir.IR.Buffed.RawAccessors
import all Veir.IR.Buffed.SimDefs

set_option linter.unusedSectionVars false

/-! # Region push simulation proofs

The raw region-slot setter, its spec-level counterpart, and the (large) proof that the `Sim`
relation survives them. Split out of `Veir.Rewriter.Basic` to keep that file readable,
mirroring `Veir.Rewriter.RewriterPushOperand`.

Unlike the other slot setters, `Rewriter.setRegion` writes into *two* allocations: the region's
`parent` link and the operation's region slot. Every read-preservation bridge therefore carries
two disjointness obligations. -/

public section
namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo] [SerializableOpInfo OpInfo]
variable {ctx : Sim.IRContext OpInfo}

@[grind]
def Rewriter.pushRegion (ctx : IRContext OpInfo) (op : OperationPtr) (region : RegionPtr)
    (hop : op.InBounds ctx := by grind) (hregion : region.InBounds ctx := by grind)
    (_hRegionParent : (region.get! ctx).parent = none := by grind) :
    IRContext OpInfo :=
  let ctx := region.setParent ctx op
  op.pushRegion ctx region

@[inline]
protected def Rewriter.setRegion (opPtr : Buffed.OperationMPtr) (ctx₀ : Buffed.IRBufContext OpInfo) (idx : UInt64)
    (region : Buffed.RegionMPtr)
    (hregion : (region + Buffed.Region.Offsets.parent).toInt + Buffed.Region.Sizes.parent.toInt ≤ ctx₀.size)
    (hnum : opPtr.toNat + Buffed.Operation.sizeBaseNat ≤ ctx₀.size)
    (hslot : (opPtr + opPtr.computeRegionOffset ctx₀ idx hnum).toNat + Buffed.ptrSize.toNat ≤ ctx₀.size) :
    Buffed.IRBufContext OpInfo :=
  -- Compute the region slot from `ctx₀` (the region-`writeParent` below touches the region, not
  -- the operation's count fields, so the offset is the same), then write the parent link and
  -- blit the region pointer into the slot. `hregion` bounds the (independent) region pointer.
  let slot := opPtr + opPtr.computeRegionOffset ctx₀ idx hnum
  let ctx := region.writeParent ctx₀ opPtr hregion
  let mem := ctx.mem.blit64 slot region (by
    have hb := ctx₀.mem.fits_in_memory
    simp only [Buffed.IRBufContext.size_def] at *
    grind [UInt64.uint64_add_int64_toInt_lt, Buffed.RegionMPtr.writeParent_range,
      Buffed.RegionMPtr.writeParent_size])
  { ctx with mem := mem }

set_option maxHeartbeats 1000000000 in
/-- The `Sim` relation survives writing `region` into slot `idx` of `opPtr`'s (pre-allocated)
region array and back-linking the region's `parent` to `opPtr`, while the spec performs the
matching `Rewriter.pushRegion`. Discharges the `admitted_sim` in `Rewriter.pushRegionAtSim`. -/
theorem Rewriter.setRegion_pushRegion_sim (opPtr : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo)
    (idx : UInt64) (region : Sim.RegionPtr)
    (opPtrInBounds : opPtr.InBounds ctx) (regionInBounds : region.InBounds ctx)
    (hRegionParent : (region.spec.get! ctx.spec).parent = none)
    (hidx : idx.toNat = opPtr.spec.getNumRegions! ctx.spec)
    (hcap : idx.toNat < (opPtr.spec.get! ctx.spec).capRegions)
    (hregion : (region.impl + Buffed.Region.Offsets.parent).toInt + Buffed.Region.Sizes.parent.toInt ≤ ctx.buf.size)
    (hnum : opPtr.impl.toNat + Buffed.Operation.sizeBaseNat ≤ ctx.buf.size)
    (hslot : (opPtr.impl + Buffed.OperationMPtr.computeRegionOffset ctx.buf opPtr.impl idx hnum).toNat
      + Buffed.ptrSize.toNat ≤ ctx.buf.size) :
    Veir.Sim ⟨Rewriter.setRegion opPtr.impl ctx.buf idx region.impl hregion hnum hslot,
              Rewriter.pushRegion ctx.spec opPtr.spec region.spec (by grind) (by grind) (by grind)⟩ := by
  have hin := ctx.sim.in_bounds (.operation opPtr.spec) (by grind)
  have hrin := ctx.sim.in_bounds (.region region.spec) (by grind)
  have hsz : ctx.buf.mem.size < 2^63 := by grind
  have hincl := OperationPtr.nthRegion_range_included_op_range ctx opPtr.spec idx hcap (by grind)
  have hidxlt : idx.toNat < 4294967296 := by
    have := ctx.isRepr.operations_indices opPtr.spec (by grind) |>.regions
    grind
  have hmul : (Buffed.ptrSize * idx).toNat = Buffed.ptrSizeNat * idx.toNat := by
    rw [UInt64.toNat_mul]
    grind
  have hoff := OperationPtr.computeRegionsOffset!_ideal ctx opPtr (by grind) (by grind) hnum
  have hopM : (UInt64.toNat opPtr.impl : Int) = opPtr.spec.toFlat := by
    have := opPtrInBounds.sim
    simp only [Sim.OperationPtr.Sim, OperationPtr.toM] at this
    grind [OperationPtr.toFlat, OperationPtr.range]
  have hrgM : (UInt64.toNat region.impl : Int) = region.spec.toFlat := by
    have := regionInBounds.sim
    simp only [Sim.RegionPtr.Sim, RegionPtr.toM] at this
    grind [RegionPtr.toFlat, RegionPtr.range]
  have hslotaddr : ((opPtr.impl + Buffed.OperationMPtr.computeRegionOffset ctx.buf opPtr.impl idx hnum).toNat : Int)
      = opPtr.spec.toFlat + (Buffed.Operation.Offsets.regionsInt opPtr.spec ctx.spec + Buffed.ptrSizeNat * idx.toNat) := by
    simp only [Buffed.OperationMPtr.computeRegionOffset,
      Buffed.OperationMPtr.computeRegionsOffset_eq_computeRegionsOffset!]
    grind [Buffed.OperationMPtr.computeRegionOffset, IsIncludedI, IsIncludedIN]
  have hparentaddr : ((region.impl + Buffed.Region.Offsets.parent).toNat : Int) = region.spec.toFlat + 16 := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;>
      grind [RegionPtr.range, show Buffed.Region.Offsets.parent.toInt = 16 from rfl]
  -- the region allocation is disjoint from the operation allocation
  have hdOR := ctx.sim.disjoint_allocs (.operation opPtr.spec) (.region region.spec)
    (by grind) (by grind) (by simp)
  -- Read-preservation bridge over the two writes: any 8-/4-byte read disjoint from both the
  -- region-`parent` slot `[region+16, region+24)` and the region slot `[slot, slot+8)` is
  -- unchanged; the attribute table is untouched.
  have hread : ∀ (a : UInt64),
      (a.toNat + 8 ≤ (opPtr.impl + Buffed.OperationMPtr.computeRegionOffset ctx.buf opPtr.impl idx hnum).toNat
       ∨ (opPtr.impl + Buffed.OperationMPtr.computeRegionOffset ctx.buf opPtr.impl idx hnum).toNat + 8 ≤ a.toNat) →
      (a.toNat + 8 ≤ (region.impl + Buffed.Region.Offsets.parent).toNat
       ∨ (region.impl + Buffed.Region.Offsets.parent).toNat + 8 ≤ a.toNat) →
      (Rewriter.setRegion opPtr.impl ctx.buf idx region.impl hregion hnum hslot).mem.read64! a
        = ctx.buf.mem.read64! a := by
    intro a ha hb
    simp only [Rewriter.setRegion, Buffed.RegionMPtr.writeParent]
    rw [ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
      ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega)]
  have hread32 : ∀ (a : UInt64),
      (a.toNat + 8 ≤ (opPtr.impl + Buffed.OperationMPtr.computeRegionOffset ctx.buf opPtr.impl idx hnum).toNat
       ∨ (opPtr.impl + Buffed.OperationMPtr.computeRegionOffset ctx.buf opPtr.impl idx hnum).toNat + 8 ≤ a.toNat) →
      (a.toNat + 8 ≤ (region.impl + Buffed.Region.Offsets.parent).toNat
       ∨ (region.impl + Buffed.Region.Offsets.parent).toNat + 8 ≤ a.toNat) →
      (Rewriter.setRegion opPtr.impl ctx.buf idx region.impl hregion hnum hslot).mem.read32! a
        = ctx.buf.mem.read32! a := by
    intro a ha hb
    simp only [Rewriter.setRegion, Buffed.RegionMPtr.writeParent]
    rw [ExArray.read32!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
      ExArray.read32!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega)]
  -- reading the freshly written region slot
  have hslotread : (Rewriter.setRegion opPtr.impl ctx.buf idx region.impl hregion hnum hslot).mem.read64!
      (opPtr.impl + Buffed.OperationMPtr.computeRegionOffset ctx.buf opPtr.impl idx hnum) = region.impl := by
    simp only [Rewriter.setRegion, Buffed.RegionMPtr.writeParent]
    rw [ExArray.read64!_blit64_self]
  -- reading the freshly written region-parent link
  have hparentread : (Rewriter.setRegion opPtr.impl ctx.buf idx region.impl hregion hnum hslot).mem.read64!
      (region.impl + Buffed.Region.Offsets.parent) = opPtr.impl := by
    simp only [Rewriter.setRegion, Buffed.RegionMPtr.writeParent]
    rw [ExArray.read64!_blit64_disjoint _ _ _ _ _ (by
        simp only [IsDisjoint]
        simp only [TopLevelPtr.range, OperationPtr.range_ideal ctx.sim.repr opPtrInBounds.ib,
          RegionPtr.range_ideal, IsDisjointI, OperationPtr.rangeInt, Buffed.Operation.rangeInt,
          RegionPtr.rangeInt, Buffed.Region.rangeInt, add_nat_range_def] at hdOR
        have hlow : (0:Int) ≤ opPtr.spec.toFlat + Buffed.Operation.Offsets.regionsInt opPtr.spec ctx.spec := by
          simp only [IsIncludedI] at hincl
          simp only [OperationPtr.toM] at hincl
          grind
        grind [ExArray.range_lower, ExArray.range_upper]),
      ExArray.read64!_blit64_self]
  have hattr : (Rewriter.setRegion opPtr.impl ctx.buf idx region.impl hregion hnum hslot).attributes
      = ctx.buf.attributes := by
    simp only [Rewriter.setRegion, Buffed.RegionMPtr.writeParent]
  have hrange : (Rewriter.setRegion opPtr.impl ctx.buf idx region.impl hregion hnum hslot).mem.range
      = ctx.buf.mem.range := by
    simp only [Rewriter.setRegion, Buffed.RegionMPtr.writeParent, ExArray.range_blit64]
  -- `pushRegion` is a two-step spec update (`setParent` then `pushRegion`); `grind` cannot chain
  -- the two `LayoutUnchanged` facts on its own, so establish the composite up front.
  have hlu : ctx.spec.LayoutUnchanged
      (Rewriter.pushRegion ctx.spec opPtr.spec region.spec (by grind) (by grind) (by grind)) := by
    simp only [Rewriter.pushRegion]
    apply IRContext.LayoutUnchanged.trans (region.spec.setParent ctx.spec opPtr.spec (by grind)) <;> grind
  have hlu' : (Rewriter.pushRegion ctx.spec opPtr.spec region.spec (by grind) (by grind) (by grind)).LayoutUnchanged
      ctx.spec := IRContext.LayoutUnchanged.symm.mp hlu
  constructor
  · -- fieldsInBounds
    have := ctx.sim.fieldsInBounds
    simp only [Rewriter.pushRegion]
    apply OperationPtr.pushRegion_fieldsInBounds (by grind)
    apply RegionPtr.setParent_fieldsInBounds (by grind) (by grind)
  · -- repr
    clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
    (try clear hslot hnum hregion)
    have hrepr := ctx.isRepr
    have hfib := ctx.sim.fieldsInBounds
    simp only [Rewriter.pushRegion]
    grind [layout_grind]
  · -- in_bounds
    simp only
    intros gptr gptrIb
    rw [hrange]
    clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
    have := ctx.sim.in_bounds gptr (by grind [Rewriter.pushRegion])
    grind [TopLevelPtr, Rewriter.pushRegion]
  · -- disjoint_allocs
    simp only
    clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
    have := ctx.sim.disjoint_allocs
    grind [TopLevelPtr, Rewriter.pushRegion]
  · -- encoding_op
    simp only
    intros op opIb
    have hopib : op.InBounds ctx.spec := by
      clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
      grind [Rewriter.pushRegion]
    have hoin := ctx.sim.in_bounds (.operation op) (by grind)
    have henc := ctx.sim.encoding_op op (by grind)
    have hd := ctx.sim.disjoint_allocs (.operation op) (.operation opPtr.spec) (by grind) (by grind)
    have hdr := ctx.sim.disjoint_allocs (.operation op) (.region region.spec) (by grind) (by grind) (by simp)
    have haft := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op hopib
    have hri := ctx.sim.repr.operations_indices op (by grind)
    -- the op's area layout, phrased over the same atoms `layout_grind` produces
    have hareaOP : Buffed.Operation.Offsets.operandsInt op ctx.spec
        = 72 + ((Buffed.Operation.propertySize (op.getOpType! ctx.spec)).toNat : Int) := by rfl
    have hareaBO : Buffed.Operation.Offsets.blockOperandsInt op ctx.spec
        = Buffed.Operation.Offsets.operandsInt op ctx.spec + ((op.get! ctx.spec).capOperands * 32 : Nat) := by rfl
    have hareaRG : Buffed.Operation.Offsets.regionsInt op ctx.spec
        = Buffed.Operation.Offsets.blockOperandsInt op ctx.spec + ((op.get! ctx.spec).capBlockOperands * 32 : Nat) := by rfl
    have hareaAFT : Buffed.Operation.Offsets.afterInt op ctx.spec
        = Buffed.Operation.Offsets.regionsInt op ctx.spec + ((op.get! ctx.spec).capRegions * 8 : Nat) := by rfl
    have hareaRES : Buffed.Operation.Offsets.resultsInt op ctx.spec
        = -(((op.get! ctx.spec).capResults * 40 : Nat) : Int) := by
      simp only [Buffed.Operation.Offsets.resultsInt, Buffed.Operation.Sizes.resultsNat]
      grind
    have hareaOPP : Buffed.Operation.Offsets.operandsInt opPtr.spec ctx.spec
        = 72 + ((Buffed.Operation.propertySize (opPtr.spec.getOpType! ctx.spec)).toNat : Int) := by rfl
    have hopMM : (UInt64.toNat op.toM : Int) = op.toFlat := by
      simp only [OperationPtr.toM]
      grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', OperationPtr.toFlat, layout_grind]
    -- the two ranges, in `Int` form, that must be avoided
    have hri1 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr hopib
    have hri2 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr opPtrInBounds.ib
    have hdrI : IsDisjointI (op.rangeInt ctx.spec) (region.spec.rangeInt) := by
      simp only [TopLevelPtr.range, hri1, RegionPtr.range_ideal] at hdr
      exact hdr
    -- any read inside `op`'s allocation is disjoint from the region's `parent` slot
    have hrgdisj : ∀ (b : Nat), op.toFlat + Buffed.Operation.Offsets.resultsInt op ctx.spec ≤ (b : Int) →
        (b : Int) + 8 ≤ op.toFlat + Buffed.Operation.Offsets.afterInt op ctx.spec →
        (b + 8 ≤ (region.impl + Buffed.Region.Offsets.parent).toNat
          ∨ (region.impl + Buffed.Region.Offsets.parent).toNat + 8 ≤ b) := by
      intro b hb1 hb2
      simp only [IsDisjointI, OperationPtr.rangeInt, Buffed.Operation.rangeInt,
        RegionPtr.rangeInt, Buffed.Region.rangeInt, add_nat_range_def] at hdrI
      have h24 : Buffed.Region.Offsets.afterInt = 24 := by decide
      grind [ExArray.range_lower, ExArray.range_upper]
    -- reads inside `op`'s fixed header are disjoint from both written slots
    have hro8 : ∀ (off : Int64) (n : Nat), off.toInt = n → n + 8 ≤ 72 →
        (Rewriter.setRegion opPtr.impl ctx.buf idx region.impl hregion hnum hslot).mem.read64! (op.toM + off)
          = ctx.buf.mem.read64! (op.toM + off) := by
      intro off n hn h72
      have haddr : ((op.toM + off).toNat : Int) = op.toFlat + n := by
        rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind]
      apply hread
      · by_cases hcase : op = opPtr.spec
        · subst hcase
          grind [layout_grind]
        · have hdd := hd (by simp [hcase])
          simp only [TopLevelPtr.range, hri1, hri2, IsDisjointI, OperationPtr.rangeInt,
            Buffed.Operation.rangeInt, add_nat_range_def] at hdd
          grind [layout_grind]
      · refine hrgdisj _ ?_ ?_ <;> grind [layout_grind]
    have hro4 : ∀ (off : Int64) (n : Nat), off.toInt = n → n + 8 ≤ 72 →
        (Rewriter.setRegion opPtr.impl ctx.buf idx region.impl hregion hnum hslot).mem.read32! (op.toM + off)
          = ctx.buf.mem.read32! (op.toM + off) := by
      intro off n hn h72
      have haddr : ((op.toM + off).toNat : Int) = op.toFlat + n := by
        rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind]
      apply hread32
      · by_cases hcase : op = opPtr.spec
        · subst hcase
          grind [layout_grind]
        · have hdd := hd (by simp [hcase])
          simp only [TopLevelPtr.range, hri1, hri2, IsDisjointI, OperationPtr.rangeInt,
            Buffed.Operation.rangeInt, add_nat_range_def] at hdd
          grind [layout_grind]
      · refine hrgdisj _ ?_ ?_ <;> grind [layout_grind]
    constructor
    · constructor
      · have := henc.prev
        simp only [Buffed.OperationMPtr.readPrev!] at this ⊢
        rw [hro8 Buffed.Operation.Offsets.prev 8 (by decide) (by decide)]
        grind [layout_grind, Rewriter.pushRegion]
      · have := henc.next
        simp only [Buffed.OperationMPtr.readNext!] at this ⊢
        rw [hro8 Buffed.Operation.Offsets.next 16 (by decide) (by decide)]
        grind [layout_grind, Rewriter.pushRegion]
      · have := henc.parent
        simp only [Buffed.OperationMPtr.readParent!] at this ⊢
        rw [hro8 Buffed.Operation.Offsets.parent 24 (by decide) (by decide)]
        grind [layout_grind, Rewriter.pushRegion]
      · have := henc.opType
        simp only [Buffed.OperationMPtr.readOpType!] at this ⊢
        rw [hro4 Buffed.Operation.Offsets.opType 32 (by decide) (by decide)]
        grind [layout_grind, Rewriter.pushRegion]
      · have := henc.attrs
        simp only [Buffed.OperationMPtr.readAttrs!, hattr] at this ⊢
        rw [hro8 Buffed.Operation.Offsets.attrs 64 (by decide) (by decide)]
        grind [layout_grind, Rewriter.pushRegion]
    · constructor
      · have := henc.numBlockOperands
        simp only [Buffed.OperationMPtr.readNumBlockOperands!] at this ⊢
        rw [hro8 Buffed.Operation.Offsets.numBlockOperands 40 (by decide) (by decide)]
        grind [layout_grind, Rewriter.pushRegion]
      · intros bo boIb heq
        dsimp only at boIb
        have hboib : bo.InBounds ctx.spec := by
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
          (try clear hro8 hro4); (try clear hslot hnum hregion)
          grind [Rewriter.pushRegion]
        have := henc.blockOperands bo (by grind) (by grind)
        have hbomeq : bo.toM (Rewriter.pushRegion ctx.spec opPtr.spec region.spec (by grind) (by grind) (by grind))
            = bo.toM ctx.spec := by
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
          simp only [BlockOperandPtr.toM, BlockOperandPtr.toFlat]
          grind [layout_grind, Rewriter.pushRegion]
        have hboget : bo.get! (Rewriter.pushRegion ctx.spec opPtr.spec region.spec (by grind) (by grind) (by grind))
            = bo.get! ctx.spec := by
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
          grind [Rewriter.pushRegion]
        have hboaft := Sim.BlockOperandPtr.after_lt_ctx (ctx := ctx) bo hboib
        have hboM : (UInt64.toNat (bo.toM ctx.spec) : Int) = bo.toFlat ctx.spec := by
          simp only [BlockOperandPtr.toM]
          grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', BlockOperandPtr.toFlat]
        have hboidx : bo.index < (op.get! ctx.spec).capBlockOperands := by
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
          (try clear hro8 hro4); (try clear hslot hnum hregion)
          grind [Veir.BlockOperandPtr.inBounds_def]
        have hboflat : ((bo.toFlat ctx.spec : Nat) : Int)
            = op.toFlat + Buffed.Operation.Offsets.blockOperandsInt op ctx.spec + ((bo.index * 32 : Nat) : Int) := by
          rw [BlockOperandPtr.toFlat_ideal ctx.sim.repr bo hboib]
          simp only [BlockOperandPtr.toFlatNat, heq, show Buffed.BlockOperand.sizeNat = 32 from rfl]
          have h0 : (0:Int) ≤ op.toFlat + Buffed.Operation.Offsets.blockOperandsInt op ctx.spec := by
            rw [hareaBO, hareaOP]
            omega
          omega
        have hbo : ∀ (off : Int64) (n : Nat), off.toInt = n → n + 8 ≤ 32 →
            (Rewriter.setRegion opPtr.impl ctx.buf idx region.impl hregion hnum hslot).mem.read64! (bo.toM ctx.spec + off)
              = ctx.buf.mem.read64! (bo.toM ctx.spec + off) := by
          intro off n hn h32
          have haddr : (((bo.toM ctx.spec) + off).toNat : Int) = bo.toFlat ctx.spec + n := by
            rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind]
          apply hread
          · by_cases hcase : op = opPtr.spec
            · subst hcase
              grind [layout_grind]
            · have hdd := hd (by simp [hcase])
              simp only [TopLevelPtr.range, hri1, hri2, IsDisjointI, OperationPtr.rangeInt,
                Buffed.Operation.rangeInt, add_nat_range_def] at hdd
              grind [layout_grind]
          · refine hrgdisj _ ?_ ?_ <;> grind [layout_grind]
        constructor
        · have := this.nextUse
          simp only [Buffed.BlockOperandMPtr.readNextUse!, hbomeq, hboget] at this ⊢
          rw [hbo Buffed.BlockOperand.Offsets.nextUse 0 (by decide) (by decide)]
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
          grind [layout_grind, Rewriter.pushRegion]
        · have := this.back
          simp only [Buffed.BlockOperandMPtr.readBack!, hbomeq, hboget] at this ⊢
          rw [hbo Buffed.BlockOperand.Offsets.back 8 (by decide) (by decide)]
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
          grind [layout_grind, Rewriter.pushRegion]
        · have := this.owner
          simp only [Buffed.BlockOperandMPtr.readOwner!, hbomeq, hboget] at this ⊢
          rw [hbo Buffed.BlockOperand.Offsets.owner 16 (by decide) (by decide)]
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
          grind [layout_grind, Rewriter.pushRegion]
        · have := this.value
          simp only [Buffed.BlockOperandMPtr.readValue!, hbomeq, hboget] at this ⊢
          rw [hbo Buffed.BlockOperand.Offsets.value 24 (by decide) (by decide)]
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
          grind [layout_grind, Rewriter.pushRegion]
    · constructor
      · have := henc.numRegions
        simp only [Buffed.OperationMPtr.readNumRegions!] at this ⊢
        rw [hro8 Buffed.Operation.Offsets.numRegions 48 (by decide) (by decide)]
        grind [layout_grind, Rewriter.pushRegion]
      · intros ridx ridxIn
        dsimp only at ridxIn
        have hcapr := ctx.sim.repr.operations_indices op (by grind) |>.capRegions
        have hcapr2 := ctx.sim.repr.operations_indices op (by grind) |>.regions
        -- the regions offset is computed from header fields, which are preserved
        have hcro : Buffed.OperationMPtr.computeRegionsOffset!
              (Rewriter.setRegion opPtr.impl ctx.buf idx region.impl hregion hnum hslot) op.toM
            = Buffed.OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
          simp only [Buffed.OperationMPtr.computeRegionsOffset!, Buffed.OperationMPtr.computeBlockOperandsOffset!,
            Buffed.OperationMPtr.computeOperandsOffset!, Buffed.OperationMPtr.readNumBlockOperands!,
            Buffed.OperationMPtr.readNumOperands!, Buffed.OperationMPtr.readOpType!]
          rw [hro8 Buffed.Operation.Offsets.numBlockOperands 40 (by decide) (by decide),
            hro8 Buffed.Operation.Offsets.numOperands 56 (by decide) (by decide),
            hro4 Buffed.Operation.Offsets.opType 32 (by decide) (by decide)]
        have hnumop : UInt64.toNat op.toM + Buffed.Operation.sizeBaseNat ≤ ctx.buf.size := by
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
          (try clear hro8 hro4); (try clear hslot hnum hregion)
          have h5 : op.toFlat = op.id := rfl
          have h6 : Buffed.Operation.sizeBaseNat = 72 := rfl
          simp only [Buffed.IRBufContext.size_def]
          omega
        have hcri : (Buffed.OperationMPtr.computeRegionsOffset! ctx.buf op.toM).toInt
            = Buffed.Operation.Offsets.regionsInt op ctx.spec :=
          Veir.OperationPtr.computeRegionsOffset!_ideal ctx ⟨op.toM, op⟩ (by grind) (by grind) hnumop
        -- the address of `op`'s `j`-th region slot
        have hslotj : ∀ (j : Nat), j < (op.get! ctx.spec).capRegions →
            ((op.toM + Buffed.OperationMPtr.computeRegionOffset! ctx.buf op.toM j.toUInt64).toNat : Int)
              = op.toFlat + (Buffed.Operation.Offsets.regionsInt op ctx.spec + Buffed.ptrSizeNat * j) := by
          intro j hj
          have hjlt : j < 4294967296 := by grind
          have hju : j.toUInt64.toNat = j := by
            grind [Nat.toUInt64_eq, UInt64.toNat_ofNat']
          have hjm : (Buffed.ptrSize * j.toUInt64).toNat = Buffed.ptrSizeNat * j := by
            rw [UInt64.toNat_mul]
            grind
          have hjincl := OperationPtr.nthRegion_range_included_op_range ctx op j.toUInt64 (by grind) hopib
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt
          clear hdOR hopM hrgM hin hrin hcro hro8 hro4 hrgdisj hdrI hdr hd hlu hlu'
          simp only [Buffed.OperationMPtr.computeRegionOffset!]
          grind [Buffed.OperationMPtr.computeRegionOffset!, IsIncludedI, IsIncludedIN]
        by_cases hcase : op = opPtr.spec
        · subst hcase
          have hM : opPtr.spec.toM = opPtr.impl := opPtrInBounds.sim
          have hridx : ridx < idx.toNat + 1 := by
            clear hread hread32 hattr hslotread hparentread hoff hslotaddr hparentaddr hincl hmul
            (try clear hro8 hro4 hcro hslotj)
            grind [Rewriter.pushRegion]
          have hridxcap : ridx < (opPtr.spec.get! ctx.spec).capRegions := by omega
          have hru : ridx.toUInt64.toNat = ridx := by
            grind [Nat.toUInt64_eq, UInt64.toNat_ofNat']
          have hslotR := hslotj ridx hridxcap
          simp only [Buffed.OperationMPtr.computeRegionOffset!] at hslotR
          by_cases hlast : ridx = idx.toNat
          · -- the freshly written slot
            have hidxu : ridx.toUInt64 = idx := by
              grind [Nat.toUInt64_eq, UInt64.toNat_ofNat']
            simp only [Buffed.OperationMPtr.readNthRegion!, Buffed.OperationMPtr.computeRegionOffset!,
              hcro, hidxu]
            rw [show opPtr.spec.toM + (Buffed.OperationMPtr.computeRegionsOffset! ctx.buf opPtr.spec.toM + Buffed.ptrSize * idx)
                  = opPtr.impl + Buffed.OperationMPtr.computeRegionOffset ctx.buf opPtr.impl idx hnum from by
                  simp only [hM, Buffed.OperationMPtr.computeRegionOffset_eq_computeRegionOffset!,
                    Buffed.OperationMPtr.computeRegionOffset!], hslotread]
            rw [Sim.RegionPtr.Sim]
            have hrsim := regionInBounds.sim
            simp only [Sim.RegionPtr.Sim] at hrsim
            clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
            (try clear hro8 hro4 hcro hslotj hslotR)
            grind [Rewriter.pushRegion]
          · -- a pre-existing slot
            have hridx' : ridx < idx.toNat := by omega
            -- `ptrSizeNat` must be a literal or `omega` sees `ptrSizeNat * ridx` as an opaque atom
            have hp8 : Buffed.ptrSizeNat = 8 := rfl
            simp only [hp8] at hslotR hslotaddr
            have := henc.regions ridx (by grind)
            rw [Sim.RegionPtr.Sim] at this ⊢
            simp only [Buffed.OperationMPtr.readNthRegion!, Buffed.OperationMPtr.computeRegionOffset!,
              hcro] at this ⊢
            rw [show (Rewriter.setRegion opPtr.impl ctx.buf idx region.impl hregion hnum hslot).mem.read64!
                    (opPtr.spec.toM + (Buffed.OperationMPtr.computeRegionsOffset! ctx.buf opPtr.spec.toM
                      + Buffed.ptrSize * ridx.toUInt64))
                  = ctx.buf.mem.read64! (opPtr.spec.toM + (Buffed.OperationMPtr.computeRegionsOffset! ctx.buf opPtr.spec.toM
                      + Buffed.ptrSize * ridx.toUInt64)) from by
                apply hread
                · omega
                · refine hrgdisj _ ?_ ?_ <;> grind [layout_grind]]
            clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
            (try clear hro8 hro4 hcro hslotj hslotR)
            grind [Rewriter.pushRegion]
        · -- a different operation: its region slots are untouched
          have hridxOld : ridx < op.getNumRegions! ctx.spec := by
            clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
            (try clear hro8 hro4 hcro hslotj); (try clear hslot hnum hregion)
            grind [Rewriter.pushRegion]
          have hru : ridx.toUInt64.toNat = ridx := by
            grind [Nat.toUInt64_eq, UInt64.toNat_ofNat']
          have := henc.regions ridx (by grind)
          have hnth : Buffed.OperationMPtr.readNthRegion!
                (Rewriter.setRegion opPtr.impl ctx.buf idx region.impl hregion hnum hslot) op.toM ridx.toUInt64
              = Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM ridx.toUInt64 := by
            simp only [Buffed.OperationMPtr.readNthRegion!, Buffed.OperationMPtr.computeRegionOffset!, hcro]
            have hslotR := hslotj ridx (by grind)
            simp only [Buffed.OperationMPtr.computeRegionOffset!] at hslotR
            apply hread
            · have hdd := hd (by simp [hcase])
              simp only [TopLevelPtr.range, hri1, hri2, IsDisjointI, OperationPtr.rangeInt,
                Buffed.Operation.rangeInt, add_nat_range_def] at hdd
              grind [layout_grind]
            · refine hrgdisj _ ?_ ?_ <;> grind [layout_grind]
          rw [Sim.RegionPtr.Sim] at this ⊢
          simp only [hnth]
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz hcro hnth
          (try clear hro8 hro4 hslotj)
          grind [layout_grind, Rewriter.pushRegion]
    · constructor
      · have := henc.numOperands
        simp only [Buffed.OperationMPtr.readNumOperands!] at this ⊢
        rw [hro8 Buffed.Operation.Offsets.numOperands 56 (by decide) (by decide)]
        grind [layout_grind, Rewriter.pushRegion]
      · intros oper operIb heq
        dsimp only at operIb
        have hoperib : oper.InBounds ctx.spec := by
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
          (try clear hro8 hro4); (try clear hslot hnum hregion)
          grind [Rewriter.pushRegion]
        have := henc.operands oper (by grind) (by grind)
        have hopermeq : oper.toM (Rewriter.pushRegion ctx.spec opPtr.spec region.spec (by grind) (by grind) (by grind))
            = oper.toM ctx.spec := by
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
          simp only [OpOperandPtr.toM, OpOperandPtr.toFlat]
          grind [layout_grind, Rewriter.pushRegion]
        have hoperget : oper.get! (Rewriter.pushRegion ctx.spec opPtr.spec region.spec (by grind) (by grind) (by grind))
            = oper.get! ctx.spec := by
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
          grind [Rewriter.pushRegion]
        have hoperaft := Sim.OpOperandPtr.after_lt_ctx (ctx := ctx) oper hoperib
        have hoperM : (UInt64.toNat (oper.toM ctx.spec) : Int) = oper.toFlat ctx.spec := by
          simp only [OpOperandPtr.toM]
          grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', OpOperandPtr.toFlat]
        have hoperidx : oper.index < (op.get! ctx.spec).capOperands := by
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
          (try clear hro8 hro4); (try clear hslot hnum hregion)
          grind [Veir.OpOperandPtr.inBounds_def]
        have hoperflat : ((oper.toFlat ctx.spec : Nat) : Int)
            = op.toFlat + Buffed.Operation.Offsets.operandsInt op ctx.spec + ((oper.index * 32 : Nat) : Int) := by
          rw [OpOperandPtr.toFlat_ideal ctx.sim.repr oper hoperib]
          simp only [OpOperandPtr.toFlatNat, heq, show Buffed.OpOperand.sizeNat = 32 from rfl]
          have h0 : (0:Int) ≤ op.toFlat + Buffed.Operation.Offsets.operandsInt op ctx.spec := by
            rw [hareaOP]
            omega
          omega
        have hop : ∀ (off : Int64) (n : Nat), off.toInt = n → n + 8 ≤ 32 →
            (Rewriter.setRegion opPtr.impl ctx.buf idx region.impl hregion hnum hslot).mem.read64! (oper.toM ctx.spec + off)
              = ctx.buf.mem.read64! (oper.toM ctx.spec + off) := by
          intro off n hn h32
          have haddr : (((oper.toM ctx.spec) + off).toNat : Int) = oper.toFlat ctx.spec + n := by
            rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind]
          apply hread
          · by_cases hcase : op = opPtr.spec
            · subst hcase
              grind [layout_grind]
            · have hdd := hd (by simp [hcase])
              simp only [TopLevelPtr.range, hri1, hri2, IsDisjointI, OperationPtr.rangeInt,
                Buffed.Operation.rangeInt, add_nat_range_def] at hdd
              grind [layout_grind]
          · refine hrgdisj _ ?_ ?_ <;> grind [layout_grind]
        constructor
        · have := this.nextUse
          simp only [Buffed.OpOperandMPtr.readNextUse!, hopermeq, hoperget] at this ⊢
          rw [hop Buffed.OpOperand.Offsets.nextUse 0 (by decide) (by decide)]
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
          grind [layout_grind, Rewriter.pushRegion]
        · have := this.back
          simp only [Buffed.OpOperandMPtr.readBack!, hopermeq, hoperget] at this ⊢
          rw [hop Buffed.OpOperand.Offsets.back 8 (by decide) (by decide)]
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
          grind [layout_grind, Rewriter.pushRegion]
        · have := this.owner
          simp only [Buffed.OpOperandMPtr.readOwner!, hopermeq, hoperget] at this ⊢
          rw [hop Buffed.OpOperand.Offsets.owner 16 (by decide) (by decide)]
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
          grind [layout_grind, Rewriter.pushRegion]
        · have := this.value
          simp only [Buffed.OpOperandMPtr.readValue!, hopermeq, hoperget] at this ⊢
          rw [hop Buffed.OpOperand.Offsets.value 24 (by decide) (by decide)]
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
          grind [layout_grind, Rewriter.pushRegion]
    · constructor
      · have := henc.numResults
        simp only [Buffed.OperationMPtr.readNumResults!] at this ⊢
        rw [hro8 Buffed.Operation.Offsets.numResults 0 (by decide) (by decide)]
        grind [layout_grind, Rewriter.pushRegion]
      · intros res resIb heq
        dsimp only at resIb
        have hresib : res.InBounds ctx.spec := by
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
          (try clear hro8 hro4); (try clear hslot hnum hregion)
          grind [Rewriter.pushRegion]
        have := henc.results res (by grind) (by grind)
        have hresmeq : res.toM (Rewriter.pushRegion ctx.spec opPtr.spec region.spec (by grind) (by grind) (by grind))
            = res.toM ctx.spec := by
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
          simp only [OpResultPtr.toM, OpResultPtr.toFlat]
          grind [layout_grind, Rewriter.pushRegion]
        have hresget : res.get! (Rewriter.pushRegion ctx.spec opPtr.spec region.spec (by grind) (by grind) (by grind))
            = res.get! ctx.spec := by
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
          grind [Rewriter.pushRegion]
        have hresaft := Sim.OpResultPtr.after_lt_ctx (ctx := ctx) res hresib
        have hresM : (UInt64.toNat (res.toM ctx.spec) : Int) = res.toFlat ctx.spec := by
          simp only [OpResultPtr.toM]
          grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', OpResultPtr.toFlat]
        have hresidx : res.index < (op.get! ctx.spec).capResults := by
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
          (try clear hro8 hro4); (try clear hslot hnum hregion)
          grind [Veir.OpResultPtr.inBounds_def]
        have hoplow : (0:Int) ≤ op.toFlat + Buffed.Operation.Offsets.resultsInt op ctx.spec := by
          have hio := hoin
          simp only [TopLevelPtr.range, hri1, OperationPtr.rangeInt, Buffed.Operation.rangeInt,
            add_nat_range_def, IsIncludedIN] at hio
          grind [ExArray.range_lower, ExArray.range_upper]
        have hresflat : ((res.toFlat ctx.spec : Nat) : Int)
            = op.toFlat + Buffed.Operation.Offsets.resultsInt op ctx.spec + ((res.index * 40 : Nat) : Int) := by
          rw [OpResultPtr.toFlat_ideal ctx.sim.repr res hresib]
          simp only [OpResultPtr.toFlatNat, heq, show Buffed.OpResult.sizeNat = 40 from rfl]
          omega
        have hres : ∀ (off : Int64) (n : Nat), off.toInt = n → n + 8 ≤ 40 →
            (Rewriter.setRegion opPtr.impl ctx.buf idx region.impl hregion hnum hslot).mem.read64! (res.toM ctx.spec + off)
              = ctx.buf.mem.read64! (res.toM ctx.spec + off) := by
          intro off n hn h40
          have haddr : (((res.toM ctx.spec) + off).toNat : Int) = res.toFlat ctx.spec + n := by
            rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind]
          apply hread
          · by_cases hcase : op = opPtr.spec
            · subst hcase
              grind [layout_grind]
            · have hdd := hd (by simp [hcase])
              simp only [TopLevelPtr.range, hri1, hri2, IsDisjointI, OperationPtr.rangeInt,
                Buffed.Operation.rangeInt, add_nat_range_def] at hdd
              grind [layout_grind]
          · refine hrgdisj _ ?_ ?_ <;> grind [layout_grind]
        have hres0 : (Rewriter.setRegion opPtr.impl ctx.buf idx region.impl hregion hnum hslot).mem.read64! (res.toM ctx.spec)
            = ctx.buf.mem.read64! (res.toM ctx.spec) := by
          have := hres Buffed.ValueImpl.Offsets.kind 0 (by decide) (by decide)
          simpa using this
        constructor
        · have := this.kind
          simp only [Buffed.OpResultMPtr.readKind!, hresmeq, hresget] at this ⊢
          rw [hres0]
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
          grind [layout_grind, Rewriter.pushRegion]
        · have := this.typee
          simp only [Buffed.OpResultMPtr.readType!, hattr, hresmeq] at this ⊢
          rw [hres Buffed.ValueImpl.Offsets.type 8 (by decide) (by decide)]
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
          grind [layout_grind, Rewriter.pushRegion]
        · have := this.firstUse
          simp only [Buffed.OpResultMPtr.readFirstUse!, hresmeq, hresget] at this ⊢
          rw [hres Buffed.ValueImpl.Offsets.firstUse 16 (by decide) (by decide)]
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
          grind [layout_grind, Rewriter.pushRegion]
        · have := this.index
          simp only [Buffed.OpResultMPtr.readIndex!, hresmeq, hresget] at this ⊢
          rw [hres Buffed.OpResult.Offsets.index 24 (by decide) (by decide)]
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
          grind [layout_grind, Rewriter.pushRegion]
        · have := this.owner
          simp only [Buffed.OpResultMPtr.readOwner!, hresmeq, hresget] at this ⊢
          rw [hres Buffed.OpResult.Offsets.owner 32 (by decide) (by decide)]
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
          grind [layout_grind, Rewriter.pushRegion]
  · -- encoding_block: a block's allocation is disjoint from both the operation's and the
    -- region's, so every read is preserved.
    simp only
    intros blk blkIb
    have hblkib : blk.InBounds ctx.spec := by
      clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
      (try clear hslot hnum hregion)
      grind [Rewriter.pushRegion]
    have hbin := ctx.sim.in_bounds (.block blk) (by grind)
    have henc := ctx.sim.encoding_block blk (by grind)
    have hdd := ctx.sim.disjoint_allocs (.block blk) (.operation opPtr.spec) (by grind) (by grind) (by simp)
    have hdr := ctx.sim.disjoint_allocs (.block blk) (.region region.spec) (by grind) (by grind) (by simp)
    have hbri := ctx.sim.repr.blocks_indices blk (by grind)
    have hareaBLK : Buffed.Block.Offsets.afterInt blk ctx.spec
        = 56 + (((blk.get! ctx.spec).capArguments * 40 : Nat) : Int) := by rfl
    have hblkM : (UInt64.toNat blk.toM : Int) = blk.toFlat := by
      simp only [BlockPtr.toM]
      grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', BlockPtr.toFlat, layout_grind]
    have haft := Sim.BlockPtr.after_lt_ctx (ctx := ctx) blk hblkib
    have hbget : blk.get! (Rewriter.pushRegion ctx.spec opPtr.spec region.spec (by grind) (by grind) (by grind))
        = blk.get! ctx.spec := by
      clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
      (try clear hslot hnum hregion)
      grind [Rewriter.pushRegion]
    have hri1 := BlockPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr hblkib
    have hri2 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr opPtrInBounds.ib
    simp only [TopLevelPtr.range, hri1, hri2, IsDisjointI, BlockPtr.rangeInt, Buffed.Block.rangeInt,
      OperationPtr.rangeInt, Buffed.Operation.rangeInt, add_nat_range_def] at hdd
    simp only [TopLevelPtr.range, hri1, RegionPtr.range_ideal, IsDisjointI, BlockPtr.rangeInt,
      Buffed.Block.rangeInt, RegionPtr.rangeInt, Buffed.Region.rangeInt, add_nat_range_def] at hdr
    have h24 : Buffed.Region.Offsets.afterInt = 24 := by decide
    have hb8 : ∀ (off : Int64) (n : Nat), off.toInt = n → (n : Int) + 8 ≤ Buffed.Block.Offsets.afterInt blk ctx.spec →
        (Rewriter.setRegion opPtr.impl ctx.buf idx region.impl hregion hnum hslot).mem.read64! (blk.toM + off)
          = ctx.buf.mem.read64! (blk.toM + off) := by
      intro off n hn hbnd
      have haddr : ((blk.toM + off).toNat : Int) = blk.toFlat + n := by
        rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind]
      apply hread
      · grind [layout_grind, ExArray.range_lower, ExArray.range_upper]
      · grind [layout_grind, ExArray.range_lower, ExArray.range_upper]
    constructor
    · constructor
      · have := henc.firstUse
        simp only [Buffed.BlockMPtr.readFirstUse!, hbget] at this ⊢
        rw [hb8 Buffed.Block.Offsets.firstUse 0 (by decide) (by simp only [hareaBLK]; omega)]
        clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
        (try clear hslot hnum hregion)
        grind [layout_grind, Rewriter.pushRegion]
      · have := henc.prev
        simp only [Buffed.BlockMPtr.readPrev!, hbget] at this ⊢
        rw [hb8 Buffed.Block.Offsets.prev 8 (by decide) (by simp only [hareaBLK]; omega)]
        clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
        (try clear hslot hnum hregion)
        grind [layout_grind, Rewriter.pushRegion]
      · have := henc.next
        simp only [Buffed.BlockMPtr.readNext!, hbget] at this ⊢
        rw [hb8 Buffed.Block.Offsets.next 16 (by decide) (by simp only [hareaBLK]; omega)]
        clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
        (try clear hslot hnum hregion)
        grind [layout_grind, Rewriter.pushRegion]
      · have := henc.parent
        simp only [Buffed.BlockMPtr.readParent!, hbget] at this ⊢
        rw [hb8 Buffed.Block.Offsets.parent 24 (by decide) (by simp only [hareaBLK]; omega)]
        clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
        (try clear hslot hnum hregion)
        grind [layout_grind, Rewriter.pushRegion]
      · have := henc.firstOp
        simp only [Buffed.BlockMPtr.readFirstOp!, hbget] at this ⊢
        rw [hb8 Buffed.Block.Offsets.firstOp 32 (by decide) (by simp only [hareaBLK]; omega)]
        clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
        (try clear hslot hnum hregion)
        grind [layout_grind, Rewriter.pushRegion]
      · have := henc.lastOp
        simp only [Buffed.BlockMPtr.readLastOp!, hbget] at this ⊢
        rw [hb8 Buffed.Block.Offsets.lastOp 40 (by decide) (by simp only [hareaBLK]; omega)]
        clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
        (try clear hslot hnum hregion)
        grind [layout_grind, Rewriter.pushRegion]
    · constructor
      · have := henc.numArguments
        simp only [Buffed.BlockMPtr.readNumArguments!, hbget] at this ⊢
        rw [hb8 Buffed.Block.Offsets.numArguments 48 (by decide) (by simp only [hareaBLK]; omega)]
        clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
        (try clear hslot hnum hregion)
        grind [layout_grind, Rewriter.pushRegion]
      · intros arg argIn heq
        dsimp only at argIn
        have hargib : arg.InBounds ctx.spec := by
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
          (try clear hslot hnum hregion)
          grind [Rewriter.pushRegion]
        have := henc.arguments arg (by grind) (by grind)
        have hargget : arg.get! (Rewriter.pushRegion ctx.spec opPtr.spec region.spec (by grind) (by grind) (by grind))
            = arg.get! ctx.spec := by
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
          (try clear hslot hnum hregion)
          grind [Rewriter.pushRegion]
        have hargidx : arg.index < (blk.get! ctx.spec).capArguments := by
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
          (try clear hslot hnum hregion)
          grind [Veir.BlockArgumentPtr.inBounds_def]
        have hargaft := Sim.BlockArgumentPtr.after_lt_ctx (ctx := ctx) arg hargib
        have hargM : (UInt64.toNat arg.toM : Int) = arg.toFlat := by
          simp only [BlockArgumentPtr.toM]
          grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', BlockArgumentPtr.toFlat]
        have hargflat : ((arg.toFlat : Nat) : Int) = blk.toFlat + 56 + ((arg.index * 40 : Nat) : Int) := by
          rw [BlockArgumentPtr.toFlat_ideal]
          simp only [BlockArgumentPtr.toFlatNat, heq, show Buffed.BlockArgument.sizeNat = 40 from rfl,
            show Buffed.Block.Offsets.argumentsInt = 56 from rfl]
          omega
        have harg : ∀ (off : Int64) (n : Nat), off.toInt = n → n + 8 ≤ 40 →
            (Rewriter.setRegion opPtr.impl ctx.buf idx region.impl hregion hnum hslot).mem.read64! (arg.toM + off)
              = ctx.buf.mem.read64! (arg.toM + off) := by
          intro off n hn h40
          have haddr : ((arg.toM + off).toNat : Int) = arg.toFlat + n := by
            rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind]
          apply hread
          · grind [layout_grind, ExArray.range_lower, ExArray.range_upper]
          · grind [layout_grind, ExArray.range_lower, ExArray.range_upper]
        have harg0 : (Rewriter.setRegion opPtr.impl ctx.buf idx region.impl hregion hnum hslot).mem.read64! arg.toM
            = ctx.buf.mem.read64! arg.toM := by
          have := harg Buffed.ValueImpl.Offsets.kind 0 (by decide) (by decide)
          simpa using this
        constructor
        · have := this.kind
          simp only [Buffed.BlockArgumentMPtr.readKind!] at this ⊢
          rw [harg0]
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
          (try clear hslot hnum hregion)
          grind [layout_grind, Rewriter.pushRegion]
        · have := this.type
          simp only [Buffed.BlockArgumentMPtr.readType!, hattr, hargget] at this ⊢
          rw [harg Buffed.ValueImpl.Offsets.type 8 (by decide) (by decide)]
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
          (try clear hslot hnum hregion)
          grind [layout_grind, Rewriter.pushRegion]
        · have := this.firstUse
          simp only [Buffed.BlockArgumentMPtr.readFirstUse!, hargget] at this ⊢
          rw [harg Buffed.ValueImpl.Offsets.firstUse 16 (by decide) (by decide)]
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
          (try clear hslot hnum hregion)
          grind [layout_grind, Rewriter.pushRegion]
        · have := this.index
          simp only [Buffed.BlockArgumentMPtr.readIndex!, hargget] at this ⊢
          rw [harg Buffed.BlockArgument.Offsets.index 24 (by decide) (by decide)]
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
          (try clear hslot hnum hregion)
          grind [layout_grind, Rewriter.pushRegion]
        · have := this.owner
          simp only [Buffed.BlockArgumentMPtr.readOwner!, hargget] at this ⊢
          rw [harg Buffed.BlockArgument.Offsets.owner 32 (by decide) (by decide)]
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
          (try clear hslot hnum hregion)
          grind [layout_grind, Rewriter.pushRegion]
  · -- encoding_region
    simp only
    intros rg rgIb
    have hrgib : rg.InBounds ctx.spec := by
      clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
      (try clear hslot hnum hregion)
      grind [Rewriter.pushRegion]
    have hrgin := ctx.sim.in_bounds (.region rg) (by grind)
    have henc := ctx.sim.encoding_region rg (by grind)
    have hdd := ctx.sim.disjoint_allocs (.region rg) (.operation opPtr.spec) (by grind) (by grind) (by simp)
    have hrgtoM : (UInt64.toNat rg.toM : Int) = rg.toFlat := by
      simp only [RegionPtr.toM]
      grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', RegionPtr.toFlat, layout_grind]
    have hrgget : rg.get! (Rewriter.pushRegion ctx.spec opPtr.spec region.spec (by grind) (by grind) (by grind))
        = if region.spec = rg then { rg.get! ctx.spec with parent := some opPtr.spec } else rg.get! ctx.spec := by
      clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
      (try clear hslot hnum hregion)
      grind [Rewriter.pushRegion]
    have hri2 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr opPtrInBounds.ib
    simp only [TopLevelPtr.range, RegionPtr.range_ideal, hri2, IsDisjointI, RegionPtr.rangeInt,
      Buffed.Region.rangeInt, OperationPtr.rangeInt, Buffed.Operation.rangeInt, add_nat_range_def] at hdd
    have h24 : Buffed.Region.Offsets.afterInt = 24 := by decide
    -- the `firstBlock`/`lastBlock` fields sit below the `parent` slot, so they are preserved
    -- for *every* region (including the one being re-parented).
    have hrg8 : ∀ (off : Int64) (n : Nat), off.toInt = n → n + 8 ≤ 16 →
        (Rewriter.setRegion opPtr.impl ctx.buf idx region.impl hregion hnum hslot).mem.read64! (rg.toM + off)
          = ctx.buf.mem.read64! (rg.toM + off) := by
      intro off n hn h16
      have haddr : ((rg.toM + off).toNat : Int) = rg.toFlat + n := by
        rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind, RegionPtr.range]
      apply hread
      · grind [layout_grind, ExArray.range_lower, ExArray.range_upper]
      · by_cases hcase : rg = region.spec
        · subst hcase
          grind [layout_grind]
        · have hdr := ctx.sim.disjoint_allocs (.region rg) (.region region.spec) (by grind) (by grind)
            (by simp [hcase])
          simp only [TopLevelPtr.range, RegionPtr.range_ideal, IsDisjointI, RegionPtr.rangeInt,
            Buffed.Region.rangeInt, add_nat_range_def] at hdr
          grind [layout_grind]
    constructor
    · have := henc.firstBlock
      simp only [Buffed.RegionMPtr.readFirstBlock!, hrgget] at this ⊢
      rw [hrg8 Buffed.Region.Offsets.firstBlock 0 (by decide) (by decide)]
      clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
      (try clear hslot hnum hregion)
      grind [layout_grind, Rewriter.pushRegion]
    · have := henc.lastBlock
      simp only [Buffed.RegionMPtr.readLastBlock!, hrgget] at this ⊢
      rw [hrg8 Buffed.Region.Offsets.lastBlock 8 (by decide) (by decide)]
      clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
      (try clear hslot hnum hregion)
      grind [layout_grind, Rewriter.pushRegion]
    · -- the `parent` field: the re-parented region reads back the freshly written link,
      -- every other region is untouched.
      by_cases hcase : rg = region.spec
      · subst hcase
        have hrgeq : region.spec.toM = region.impl := regionInBounds.sim
        simp only [Buffed.RegionMPtr.readParent!, hrgget, hrgeq, hparentread]
        simp only [Sim.OptionOperationPtr.Sim]
        have hop := opPtrInBounds.sim
        simp only [Sim.OperationPtr.Sim] at hop
        clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
        (try clear hslot hnum hregion)
        grind [OperationPtr.toO]
      · have := henc.parent
        have hrgp : (Rewriter.setRegion opPtr.impl ctx.buf idx region.impl hregion hnum hslot).mem.read64!
              (rg.toM + Buffed.Region.Offsets.parent) = ctx.buf.mem.read64! (rg.toM + Buffed.Region.Offsets.parent) := by
          have haddr : ((rg.toM + Buffed.Region.Offsets.parent).toNat : Int) = rg.toFlat + 16 := by
            rw [UInt64.uint64_add_int64_toNat_lt] <;>
              grind [layout_grind, RegionPtr.range, show Buffed.Region.Offsets.parent.toInt = 16 from rfl]
          apply hread
          · grind [layout_grind, ExArray.range_lower, ExArray.range_upper]
          · have hdr := ctx.sim.disjoint_allocs (.region rg) (.region region.spec) (by grind) (by grind)
              (by simp [hcase])
            simp only [TopLevelPtr.range, RegionPtr.range_ideal, IsDisjointI, RegionPtr.rangeInt,
              Buffed.Region.rangeInt, add_nat_range_def] at hdr
            grind [layout_grind]
        simp only [Buffed.RegionMPtr.readParent!, hrgget, hrgp] at this ⊢
        clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz
        (try clear hslot hnum hregion)
        grind [layout_grind, Rewriter.pushRegion]
  · -- attr_empty: the writes leave the attribute table untouched
    (try dsimp only)
    rw [hattr]
    exact ctx.sim.attr_empty

end Veir
