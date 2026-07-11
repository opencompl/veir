module

public import ExArray.CompilerExtras
public import Veir.IR
public import Veir.Rewriter.LinkedList.Basic
public import Veir.Rewriter.LinkedList.GetSet

meta import Veir.IR.Buffed.Basic
import Veir.IR.Buffed.Frames
import Veir.IR.Buffed.RawAccessorsLemmas
import Veir.IR.Buffed.Meta
import Veir.IR.Buffed.InBounds
import Veir.Rewriter.LinkedList.LayoutUnchanged

set_option linter.unusedSectionVars false

/-! Region push simulation proofs -/

@[expose] public section
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
  -- Compute the region slot from `ctx₀` (the region-`writeParent` below touches the region, not the operation's count fields, so the offset is the same), then write the parent link and blit the region pointer into the slot.
  let slot := opPtr + opPtr.computeRegionOffset ctx₀ idx hnum
  let ctx := region.writeParent ctx₀ opPtr hregion
  let mem := ctx.mem.blit64 slot region (by
    have hb := ctx₀.mem.fits_in_memory
    simp only [Buffed.IRBufContext.size_def] at *
    grind [UInt64.uint64_add_int64_toInt_lt, Buffed.RegionMPtr.writeParent_range,
      Buffed.RegionMPtr.writeParent_size])
  { ctx with mem := mem }

set_option maxHeartbeats 1000000000 in
/-- The `Sim` relation survives writing `region` into slot `idx` of `opPtr`'s (pre-allocated) region array and back-linking the region's `parent` to `opPtr`, while the spec performs the matching `Rewriter.pushRegion`. -/
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
    simp only [Sim.OperationPtr.Sim_def, OperationPtr.toM] at this
    grind [OperationPtr.toFlat, OperationPtr.range]
  have hrgM : (UInt64.toNat region.impl : Int) = region.spec.toFlat := by
    have := regionInBounds.sim
    simp only [Sim.RegionPtr.Sim_def, RegionPtr.toM] at this
    grind [RegionPtr.toFlat, RegionPtr.range]
  have hslotaddr : ((opPtr.impl + Buffed.OperationMPtr.computeRegionOffset ctx.buf opPtr.impl idx hnum).toNat : Int)
      = opPtr.spec.toFlat + (Buffed.Operation.Offsets.regionsInt opPtr.spec ctx.spec + Buffed.ptrSizeNat * idx.toNat) := by
    simp only [Buffed.OperationMPtr.computeRegionOffset,
      Buffed.OperationMPtr.computeRegionsOffset_eq_computeRegionsOffset!]
    grind [Buffed.OperationMPtr.computeRegionOffset, IsIncludedI, IsIncludedIN]
  have hparentaddr : ((region.impl + Buffed.Region.Offsets.parent).toNat : Int) = region.spec.toFlat + 16 := by
    rw [UInt64.uint64_add_int64_toNat_lt] <;>
      grind [RegionPtr.range, show Buffed.Region.Offsets.parent.toInt = 16 from rfl]
  have hdOR := ctx.sim.disjoint_allocs (.operation opPtr.spec) (.region region.spec)
    (by grind) (by grind) (by simp)
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
      (a.toNat + 4 ≤ (opPtr.impl + Buffed.OperationMPtr.computeRegionOffset ctx.buf opPtr.impl idx hnum).toNat
       ∨ (opPtr.impl + Buffed.OperationMPtr.computeRegionOffset ctx.buf opPtr.impl idx hnum).toNat + 8 ≤ a.toNat) →
      (a.toNat + 4 ≤ (region.impl + Buffed.Region.Offsets.parent).toNat
       ∨ (region.impl + Buffed.Region.Offsets.parent).toNat + 8 ≤ a.toNat) →
      (Rewriter.setRegion opPtr.impl ctx.buf idx region.impl hregion hnum hslot).mem.read32! a
        = ctx.buf.mem.read32! a := by
    intro a ha hb
    simp only [Rewriter.setRegion, Buffed.RegionMPtr.writeParent]
    rw [ExArray.read32!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega),
      ExArray.read32!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; omega)]
  have hslotread : (Rewriter.setRegion opPtr.impl ctx.buf idx region.impl hregion hnum hslot).mem.read64!
      (opPtr.impl + Buffed.OperationMPtr.computeRegionOffset ctx.buf opPtr.impl idx hnum) = region.impl := by
    simp only [Rewriter.setRegion, Buffed.RegionMPtr.writeParent]
    rw [ExArray.read64!_blit64_self]
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
  have hlu : ctx.spec.LayoutUnchanged
      (Rewriter.pushRegion ctx.spec opPtr.spec region.spec (by grind) (by grind) (by grind)) := by
    simp only [Rewriter.pushRegion]
    apply IRContext.LayoutUnchanged.trans (region.spec.setParent ctx.spec opPtr.spec (by grind)) <;> grind
  have hlu' : (Rewriter.pushRegion ctx.spec opPtr.spec region.spec (by grind) (by grind) (by grind)).LayoutUnchanged
      ctx.spec := IRContext.LayoutUnchanged.symm.mp hlu
  have hlay : ctx.spec.LayoutPreserved (Rewriter.pushRegion ctx.spec opPtr.spec region.spec (by grind) (by grind) (by grind)) :=
    IRContext.LayoutPreserved.of_layoutUnchanged_ltr hlu
  have hwrangeW := Veir.Sim.OperationPtr.range_linear (ctx := ctx) opPtr.spec opPtrInBounds.ib
  have hwrangeR := Veir.Sim.RegionPtr.range_linear (ctx := ctx) region.spec regionInBounds.ib
  -- The two writes stay inside the fresh slot word and the region's `parent` word; any
  -- window disjoint from both agrees.
  have hagreeD : ∀ lo hi : Nat,
      (hi ≤ (opPtr.impl + Buffed.OperationMPtr.computeRegionOffset ctx.buf opPtr.impl idx hnum).toNat
       ∨ (opPtr.impl + Buffed.OperationMPtr.computeRegionOffset ctx.buf opPtr.impl idx hnum).toNat + 8 ≤ lo) →
      (hi ≤ (region.impl + Buffed.Region.Offsets.parent).toNat
       ∨ (region.impl + Buffed.Region.Offsets.parent).toNat + 8 ≤ lo) →
      Buffed.AgreesOn (Rewriter.setRegion opPtr.impl ctx.buf idx region.impl hregion hnum hslot) ctx.buf lo hi :=
    fun lo hi hd1 hd2 => ⟨fun a h1 h2 => hread a (by omega) (by omega),
      fun a h1 h2 => hread32 a (by omega) (by omega), fun _ _ h => by simp only [hattr]; exact h⟩
  constructor
  · -- fieldsInBounds
    have := ctx.sim.fieldsInBounds
    simp only [Rewriter.pushRegion]
    apply OperationPtr.pushRegion_fieldsInBounds (by grind)
    apply RegionPtr.setParent_fieldsInBounds (by grind) (by grind)
  · -- repr
    clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz hagreeD
    (try clear hslot hnum hregion)
    have hrepr := ctx.isRepr
    have hfib := ctx.sim.fieldsInBounds
    simp only [Rewriter.pushRegion]
    grind [layout_grind]
  · -- in_bounds
    simp only
    intros gptr gptrIb
    rw [hrange]
    clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz hagreeD
    have := ctx.sim.in_bounds gptr (by grind [Rewriter.pushRegion])
    grind [TopLevelPtr, Rewriter.pushRegion]
  · -- disjoint_allocs
    simp only
    clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz hagreeD
    have := ctx.sim.disjoint_allocs
    grind [TopLevelPtr, Rewriter.pushRegion]
  · -- encoding_op
    simp only
    intros op opIb
    have hopib : op.InBounds ctx.spec := by
      clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz hagreeD
      grind [Rewriter.pushRegion]
    have hoin := ctx.sim.in_bounds (.operation op) (by grind)
    have henc := ctx.sim.encoding_op op (by grind)
    have hd := ctx.sim.disjoint_allocs (.operation op) (.operation opPtr.spec) (by grind) (by grind)
    have hdr := ctx.sim.disjoint_allocs (.operation op) (.region region.spec) (by grind) (by grind) (by simp)
    have haft := Sim.OperationPtr.after_lt_ctx (ctx := ctx) op hopib
    have hri := ctx.sim.repr.operations_indices op (by grind)
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
    have hri1 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr hopib
    have hri2 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr opPtrInBounds.ib
    have hdrI : IsDisjointI (op.rangeInt ctx.spec) (region.spec.rangeInt) := by
      simp only [TopLevelPtr.range, hri1, RegionPtr.range_ideal] at hdr
      exact hdr
    have hrgdisj : ∀ (b : Nat), op.toFlat + Buffed.Operation.Offsets.resultsInt op ctx.spec ≤ (b : Int) →
        (b : Int) + 8 ≤ op.toFlat + Buffed.Operation.Offsets.afterInt op ctx.spec →
        (b + 8 ≤ (region.impl + Buffed.Region.Offsets.parent).toNat
          ∨ (region.impl + Buffed.Region.Offsets.parent).toNat + 8 ≤ b) := by
      intro b hb1 hb2
      simp only [IsDisjointI, OperationPtr.rangeInt, Buffed.Operation.rangeInt,
        RegionPtr.rangeInt, Buffed.Region.rangeInt, add_nat_range_def] at hdrI
      have h24 : Buffed.Region.Offsets.afterInt = 24 := by decide
      grind [ExArray.range_lower, ExArray.range_upper]
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
      · have h := hrgdisj ((op.toM + off).toNat) (by grind [layout_grind]) (by grind [layout_grind])
        omega
    have hdisj := fun hne : op ≠ opPtr.spec =>
      Veir.Sim.disjoint_operation_operation (ctx := ctx) op opPtr.spec hopib opPtrInBounds.ib hne
    have hrrange := Veir.Sim.OperationPtr.range_linear (ctx := ctx) op hopib
    have hgets : ((op.get! (Rewriter.pushRegion ctx.spec opPtr.spec region.spec (by grind) (by grind) (by grind))).prev = (op.get! ctx.spec).prev
        ∧ (op.get! (Rewriter.pushRegion ctx.spec opPtr.spec region.spec (by grind) (by grind) (by grind))).next = (op.get! ctx.spec).next
        ∧ (op.get! (Rewriter.pushRegion ctx.spec opPtr.spec region.spec (by grind) (by grind) (by grind))).parent = (op.get! ctx.spec).parent
        ∧ (op.get! (Rewriter.pushRegion ctx.spec opPtr.spec region.spec (by grind) (by grind) (by grind))).attrs = (op.get! ctx.spec).attrs
        ∧ op.getOpType! (Rewriter.pushRegion ctx.spec opPtr.spec region.spec (by grind) (by grind) (by grind)) = op.getOpType! ctx.spec
        ∧ (op.get! (Rewriter.pushRegion ctx.spec opPtr.spec region.spec (by grind) (by grind) (by grind))).capBlockOperands = (op.get! ctx.spec).capBlockOperands
        ∧ (op.get! (Rewriter.pushRegion ctx.spec opPtr.spec region.spec (by grind) (by grind) (by grind))).capRegions = (op.get! ctx.spec).capRegions
        ∧ (op.get! (Rewriter.pushRegion ctx.spec opPtr.spec region.spec (by grind) (by grind) (by grind))).capOperands = (op.get! ctx.spec).capOperands
        ∧ (op.get! (Rewriter.pushRegion ctx.spec opPtr.spec region.spec (by grind) (by grind) (by grind))).capResults = (op.get! ctx.spec).capResults) := by
      clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz hagreeD
      (try clear hro8 hro4 hrgdisj hdrI hd hdr hri1 hri2)
      grind [Rewriter.pushRegion]
    obtain ⟨hgprev, hgnext, hgpar, hgattrs, hgty, hgcB, hgcRg, hgcO, hgcR⟩ := hgets
    constructor
    · -- MatchesBase: framed — both writes land outside the 72-byte header.
      refine OperationPtr.matchesBase_frame ctx op hopib henc.toMatchesBase (hagreeD _ _ ?_ ?_) hlay
        hgprev hgnext hgpar hgattrs hgty opIb
      · clear hread hread32 hattr hslotread hparentread hrange hagreeD hoff hmul hidxlt
        (try clear hro8 hro4 hrgdisj)
        grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
          Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
          _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
          _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
      · clear hread hread32 hattr hslotread hparentread hrange hagreeD hoff hmul hidxlt
        (try clear hro8 hro4 hrgdisj)
        grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
          Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
          _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
          _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
    · constructor
      · refine OperationPtr.numBlockOperands_frame ctx op hopib henc.numBlockOperands (hagreeD _ _ ?_ ?_) hgcB
        · clear hread hread32 hattr hslotread hparentread hrange hagreeD hoff hmul hidxlt
          (try clear hro8 hro4 hrgdisj)
          grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
        · clear hread hread32 hattr hslotread hparentread hrange hagreeD hoff hmul hidxlt
          (try clear hro8 hro4 hrgdisj)
          grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
      · intros bo boIb heq
        dsimp only at boIb
        have hboib : bo.InBounds ctx.spec := by
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz hagreeD
          (try clear hro8 hro4 hrgdisj hdrI hd hdr hri1 hri2)
          grind [Rewriter.pushRegion]
        have hbincl := Veir.Sim.BlockOperandPtr.slot_included (ctx := ctx) bo hboib
        have hboget : bo.get! (Rewriter.pushRegion ctx.spec opPtr.spec region.spec (by grind) (by grind) (by grind)) = bo.get! ctx.spec := by
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz hagreeD
          (try clear hro8 hro4 hrgdisj hdrI hd hdr hri1 hri2)
          grind [Rewriter.pushRegion]
        refine BlockOperandPtr.matches_frame ctx bo hboib (henc.blockOperands bo hboib heq)
          (hagreeD _ _ ?_ ?_) hlay hboget boIb
        · clear hread hread32 hattr hslotread hparentread hrange hagreeD hoff hmul hidxlt
          (try clear hro8 hro4 hrgdisj)
          grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
        · clear hread hread32 hattr hslotread hparentread hrange hagreeD hoff hmul hidxlt
          (try clear hro8 hro4 hrgdisj)
          grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
    · constructor
      · refine OperationPtr.numRegions_frame ctx op hopib henc.numRegions (hagreeD _ _ ?_ ?_) hgcRg
        · clear hread hread32 hattr hslotread hparentread hrange hagreeD hoff hmul hidxlt
          (try clear hro8 hro4 hrgdisj)
          grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
        · clear hread hread32 hattr hslotread hparentread hrange hagreeD hoff hmul hidxlt
          (try clear hro8 hro4 hrgdisj)
          grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
      · intros ridx ridxIn
        dsimp only at ridxIn
        have hcapr := ctx.sim.repr.operations_indices op (by grind) |>.capRegions
        have hcapr2 := ctx.sim.repr.operations_indices op (by grind) |>.regions
        by_cases hnewslot : op = opPtr.spec ∧ ridx = idx.toNat
        · -- the freshly written slot: reads back the just-written region pointer
          obtain ⟨hcase, hlast⟩ := hnewslot
          subst hcase
          have hM : opPtr.spec.toM = opPtr.impl := opPtrInBounds.sim.out
          have hcro : Buffed.OperationMPtr.computeRegionsOffset!
                (Rewriter.setRegion opPtr.impl ctx.buf idx region.impl hregion hnum hslot) opPtr.spec.toM
              = Buffed.OperationMPtr.computeRegionsOffset! ctx.buf opPtr.spec.toM := by
            simp only [Buffed.OperationMPtr.computeRegionsOffset!, Buffed.OperationMPtr.computeBlockOperandsOffset!,
              Buffed.OperationMPtr.computeOperandsOffset!, Buffed.OperationMPtr.readNumBlockOperands!,
              Buffed.OperationMPtr.readNumOperands!, Buffed.OperationMPtr.readOpType!]
            rw [hro8 Buffed.Operation.Offsets.numBlockOperands 40 (by decide) (by decide),
              hro8 Buffed.Operation.Offsets.numOperands 56 (by decide) (by decide),
              hro4 Buffed.Operation.Offsets.opType 32 (by decide) (by decide)]
          have hidxu : ridx.toUInt64 = idx := by
            grind [Nat.toUInt64_eq, UInt64.toNat_ofNat']
          simp only [Buffed.OperationMPtr.readNthRegion!, Buffed.OperationMPtr.computeRegionOffset!,
            hcro, hidxu]
          rw [show opPtr.spec.toM + (Buffed.OperationMPtr.computeRegionsOffset! ctx.buf opPtr.spec.toM + Buffed.ptrSize * idx)
                = opPtr.impl + Buffed.OperationMPtr.computeRegionOffset ctx.buf opPtr.impl idx hnum from by
                simp only [hM, Buffed.OperationMPtr.computeRegionOffset_eq_computeRegionOffset!,
                  Buffed.OperationMPtr.computeRegionOffset!], hslotread]
          rw [Sim.RegionPtr.Sim_def]
          have hrsim := regionInBounds.sim
          simp only [Sim.RegionPtr.Sim_def] at hrsim
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz hagreeD
          (try clear hro8 hro4 hrgdisj hdrI hd hdr hri1 hri2)
          grind [Rewriter.pushRegion]
        · -- an untouched slot: framed
          have hnr : ridx < op.getNumRegions! ctx.spec := by
            clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz hagreeD
            (try clear hro8 hro4 hrgdisj hdrI hd hdr hri1 hri2)
            grind [Rewriter.pushRegion]
          have hrlt : op = opPtr.spec → ridx < idx.toNat := by
            clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz hagreeD
            (try clear hro8 hro4 hrgdisj hdrI hd hdr hri1 hri2)
            intro hop
            grind [Rewriter.pushRegion]
          refine OperationPtr.nthRegion_frame ctx op hopib ridx hnr (henc.regions ridx hnr)
            (hagreeD _ _ ?_ ?_) (hagreeD _ _ ?_ ?_)
            (by clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz hagreeD
                (try clear hro8 hro4 hrgdisj hdrI hd hdr hri1 hri2)
                grind [Rewriter.pushRegion])
          · clear hread hread32 hattr hslotread hparentread hrange hagreeD hoff hmul hidxlt
            (try clear hro8 hro4 hrgdisj)
            grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
              Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
              _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
              _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
          · clear hread hread32 hattr hslotread hparentread hrange hagreeD hoff hmul hidxlt
            (try clear hro8 hro4 hrgdisj)
            grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
              Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
              _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
              _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
          · have hidxc : ridx < (op.get! ctx.spec).capRegions := by
              clear hread hread32 hattr hslotread hparentread hrange hagreeD
              grind
            have haddrR : ((op.toM.toNat : Nat) : Int) = op.id := by
              grind [Veir.OperationPtr.toM, _root_.Veir.OperationPtr.toFlat]
            have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op ridx.toUInt64
              (by clear hread hread32 hattr hslotread hparentread hrange hagreeD hoff hmul hidxlt
                  grind [UInt64.toNat_ofNat']) hopib
            clear hread hread32 hattr hslotread hparentread hrange hagreeD hoff hmul hidxlt
            (try clear hro8 hro4 hrgdisj)
            grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
              Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
              _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
              _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt, UInt64.toNat_ofNat']
          · have hidxc : ridx < (op.get! ctx.spec).capRegions := by
              clear hread hread32 hattr hslotread hparentread hrange hagreeD
              grind
            have haddrR : ((op.toM.toNat : Nat) : Int) = op.id := by
              grind [Veir.OperationPtr.toM, _root_.Veir.OperationPtr.toFlat]
            have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op ridx.toUInt64
              (by clear hread hread32 hattr hslotread hparentread hrange hagreeD hoff hmul hidxlt
                  grind [UInt64.toNat_ofNat']) hopib
            clear hread hread32 hattr hslotread hparentread hrange hagreeD hoff hmul hidxlt
            (try clear hro8 hro4 hrgdisj)
            grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
              Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
              _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
              _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt, UInt64.toNat_ofNat']
    · constructor
      · refine OperationPtr.numOperands_frame ctx op hopib henc.numOperands (hagreeD _ _ ?_ ?_) hgcO
        · clear hread hread32 hattr hslotread hparentread hrange hagreeD hoff hmul hidxlt
          (try clear hro8 hro4 hrgdisj)
          grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
        · clear hread hread32 hattr hslotread hparentread hrange hagreeD hoff hmul hidxlt
          (try clear hro8 hro4 hrgdisj)
          grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
      · intros oper operIb heq
        dsimp only at operIb
        have hoperib : oper.InBounds ctx.spec := by
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz hagreeD
          (try clear hro8 hro4 hrgdisj hdrI hd hdr hri1 hri2)
          grind [Rewriter.pushRegion]
        have hoincl := Veir.Sim.OpOperandPtr.slot_included (ctx := ctx) oper hoperib
        have hoperget : oper.get! (Rewriter.pushRegion ctx.spec opPtr.spec region.spec (by grind) (by grind) (by grind)) = oper.get! ctx.spec := by
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz hagreeD
          (try clear hro8 hro4 hrgdisj hdrI hd hdr hri1 hri2)
          grind [Rewriter.pushRegion]
        refine OpOperandPtr.matches_frame ctx oper hoperib (henc.operands oper hoperib heq)
          (hagreeD _ _ ?_ ?_) hlay hoperget operIb
        · clear hread hread32 hattr hslotread hparentread hrange hagreeD hoff hmul hidxlt
          (try clear hro8 hro4 hrgdisj)
          grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
        · clear hread hread32 hattr hslotread hparentread hrange hagreeD hoff hmul hidxlt
          (try clear hro8 hro4 hrgdisj)
          grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
    · constructor
      · refine OperationPtr.numResults_frame ctx op hopib henc.numResults (hagreeD _ _ ?_ ?_) hgcR
        · clear hread hread32 hattr hslotread hparentread hrange hagreeD hoff hmul hidxlt
          (try clear hro8 hro4 hrgdisj)
          grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
        · clear hread hread32 hattr hslotread hparentread hrange hagreeD hoff hmul hidxlt
          (try clear hro8 hro4 hrgdisj)
          grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
      · intros res resIb heq
        dsimp only at resIb
        have hresib : res.InBounds ctx.spec := by
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz hagreeD
          (try clear hro8 hro4 hrgdisj hdrI hd hdr hri1 hri2)
          grind [Rewriter.pushRegion]
        have hrincl := Veir.Sim.OpResultPtr.slot_included (ctx := ctx) res hresib
        have hresget : res.get! (Rewriter.pushRegion ctx.spec opPtr.spec region.spec (by grind) (by grind) (by grind)) = res.get! ctx.spec := by
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz hagreeD
          (try clear hro8 hro4 hrgdisj hdrI hd hdr hri1 hri2)
          grind [Rewriter.pushRegion]
        refine OpResultPtr.matches_frame ctx res hresib (henc.results res hresib heq)
          (hagreeD _ _ ?_ ?_) hlay hresget resIb
        · clear hread hread32 hattr hslotread hparentread hrange hagreeD hoff hmul hidxlt
          (try clear hro8 hro4 hrgdisj)
          grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
        · clear hread hread32 hattr hslotread hparentread hrange hagreeD hoff hmul hidxlt
          (try clear hro8 hro4 hrgdisj)
          grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
  · -- encoding_block: framed — blocks are disjoint from both written words.
    simp only
    intros blk blkIb
    have hblkib : blk.InBounds ctx.spec := by
      clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz hagreeD
      (try clear hro8 hro4 hrgdisj hdrI hd hdr hri1 hri2)
      grind [Rewriter.pushRegion]
    have henc := ctx.sim.encoding_block blk hblkib
    have hbrange := Veir.Sim.BlockPtr.range_linear (ctx := ctx) blk hblkib
    have hdisjB := Veir.Sim.disjoint_block_operation (ctx := ctx) blk opPtr.spec hblkib opPtrInBounds.ib
    have hdisjBR := Veir.Sim.disjoint_block_region (ctx := ctx) blk region.spec hblkib regionInBounds.ib
    have hbget : blk.get! (Rewriter.pushRegion ctx.spec opPtr.spec region.spec (by grind) (by grind) (by grind)) = blk.get! ctx.spec := by
      clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz hagreeD
      (try clear hro8 hro4 hrgdisj hdrI hd hdr hri1 hri2)
      grind [Rewriter.pushRegion]
    constructor
    · refine BlockPtr.matchesBase_frame ctx blk hblkib henc.toMatchesBase (hagreeD _ _ ?_ ?_) hlay
        (by rw [hbget]) (by rw [hbget]) (by rw [hbget]) (by rw [hbget]) (by rw [hbget]) (by rw [hbget]) blkIb
      · clear hread hread32 hattr hslotread hparentread hrange hagreeD hoff hmul hidxlt
        (try clear hro8 hro4 hrgdisj)
        grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
          Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
          _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
          _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
      · clear hread hread32 hattr hslotread hparentread hrange hagreeD hoff hmul hidxlt
        (try clear hro8 hro4 hrgdisj)
        grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
          Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
          _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
          _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
    · constructor
      · refine BlockPtr.numArguments_frame ctx blk hblkib henc.numArguments (hagreeD _ _ ?_ ?_) (by rw [hbget])
        · clear hread hread32 hattr hslotread hparentread hrange hagreeD hoff hmul hidxlt
          (try clear hro8 hro4 hrgdisj)
          grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
        · clear hread hread32 hattr hslotread hparentread hrange hagreeD hoff hmul hidxlt
          (try clear hro8 hro4 hrgdisj)
          grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
      · intros arg argIn heq
        dsimp only at argIn
        have hargib : arg.InBounds ctx.spec := by
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz hagreeD
          (try clear hro8 hro4 hrgdisj hdrI hd hdr hri1 hri2)
          grind [Rewriter.pushRegion]
        have haincl := Veir.Sim.BlockArgumentPtr.slot_included (ctx := ctx) arg hargib
        have hargget : arg.get! (Rewriter.pushRegion ctx.spec opPtr.spec region.spec (by grind) (by grind) (by grind)) = arg.get! ctx.spec := by
          clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz hagreeD
          (try clear hro8 hro4 hrgdisj hdrI hd hdr hri1 hri2)
          grind [Rewriter.pushRegion]
        refine BlockArgumentPtr.matches_frame ctx arg hargib (henc.arguments arg hargib heq)
          (hagreeD _ _ ?_ ?_) hlay hargget argIn
        · clear hread hread32 hattr hslotread hparentread hrange hagreeD hoff hmul hidxlt
          (try clear hro8 hro4 hrgdisj)
          grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
        · clear hread hread32 hattr hslotread hparentread hrange hagreeD hoff hmul hidxlt
          (try clear hro8 hro4 hrgdisj)
          grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
  · -- encoding_region
    simp only
    intros rg rgIb
    have hrgib : rg.InBounds ctx.spec := by
      clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz hagreeD
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
      clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz hagreeD
      (try clear hslot hnum hregion)
      grind [Rewriter.pushRegion]
    have hri2 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr opPtrInBounds.ib
    simp only [TopLevelPtr.range, RegionPtr.range_ideal, hri2, IsDisjointI, RegionPtr.rangeInt,
      Buffed.Region.rangeInt, OperationPtr.rangeInt, Buffed.Operation.rangeInt, add_nat_range_def] at hdd
    have h24 : Buffed.Region.Offsets.afterInt = 24 := by decide
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
      clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz hagreeD
      (try clear hslot hnum hregion)
      grind [layout_grind, Rewriter.pushRegion]
    · have := henc.lastBlock
      simp only [Buffed.RegionMPtr.readLastBlock!, hrgget] at this ⊢
      rw [hrg8 Buffed.Region.Offsets.lastBlock 8 (by decide) (by decide)]
      clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz hagreeD
      (try clear hslot hnum hregion)
      grind [layout_grind, Rewriter.pushRegion]
    · -- the `parent` field: the re-parented region reads back the freshly written link,
      by_cases hcase : rg = region.spec
      · subst hcase
        have hrgeq : region.spec.toM = region.impl := regionInBounds.sim.out
        simp only [Buffed.RegionMPtr.readParent!, hrgget, hrgeq, hparentread]
        simp only [Sim.OptionOperationPtr.Sim_def]
        have hop := opPtrInBounds.sim
        simp only [Sim.OperationPtr.Sim_def] at hop
        clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz hagreeD
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
        clear hread hread32 hattr hslotread hparentread hrange hoff hslotaddr hparentaddr hincl hmul hidxlt hdOR hopM hrgM hin hrin hsz hagreeD
        (try clear hslot hnum hregion)
        grind [layout_grind, Rewriter.pushRegion]
  · -- attr_empty: the writes leave the attribute table untouched
    (try dsimp only)
    rw [hattr]
    exact ctx.sim.attr_empty

end Veir

