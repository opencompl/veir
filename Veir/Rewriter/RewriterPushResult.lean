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

/-! Rewriter simulation proofs: result push -/

@[expose] public section
namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo] [SerializableOpInfo OpInfo]
variable {ctx : Sim.IRContext OpInfo}

@[inline]
protected def Rewriter.setResult (opPtr : Buffed.OperationMPtr) (ctx₀ : Buffed.IRBufContext OpInfo) (idx : UInt64)
    (hnum : (opPtr + Buffed.Operation.Offsets.numResults).toInt + Buffed.Operation.Sizes.numResults.toInt ≤ ctx₀.size)
    (hslot : (opPtr.getResultPtr ctx₀ idx hnum).toNat + Buffed.OpResult.size.toNat ≤ ctx₀.size)
    (type : TypeAttr) : Option (Buffed.IRBufContext OpInfo) :=
  let res := opPtr.getResultPtr ctx₀ idx hnum
  rlet hattr : (ctx, typeIdx) ← ctx₀.insertAttrs type
  have hsz : ctx.size = ctx₀.size := ctx₀.insertAttrs_size hattr
  let ctx := Buffed.ValueImplMPtr.writeKind ctx res Buffed.ValueImpl.kindResult (by prove_setSlotBounds ctx₀)
  let ctx := res.writeType ctx typeIdx (by prove_setSlotBounds ctx₀)
  let ctx := res.writeFirstUse ctx .none (by prove_setSlotBounds ctx₀)
  let ctx := res.writeIndex ctx idx (by prove_setSlotBounds ctx₀)
  let ctx := res.writeOwner ctx opPtr (by prove_setSlotBounds ctx₀)
  some ctx

def Rewriter.pushResult (ctx : IRContext OpInfo) (op : OperationPtr) (type : TypeAttr)
    (hop : op.InBounds ctx := by grind)
    : IRContext OpInfo :=
  let index := op.getNumResults! ctx
  let result : OpResult := { type := type, firstUse := none, index := index, owner := op }
  op.pushResult ctx result (by grind)

set_option maxHeartbeats 1000000000 in
/-- The `Sim` relation survives writing a fresh result into slot `idx` of `opPtr`'s (pre-allocated, back-allocated) result array while the spec pushes the corresponding `OpResult`. -/
theorem Rewriter.setResult_pushResult_sim (opPtr : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo)
    (idx : UInt64) (type : TypeAttr)
    (opPtrInBounds : opPtr.InBounds ctx)
    (hidx : idx.toNat = opPtr.spec.getNumResults! ctx.spec)
    (hcap : idx.toNat < (opPtr.spec.get! ctx.spec).capResults)
    (hnum : (opPtr.impl + Buffed.Operation.Offsets.numResults).toInt + Buffed.Operation.Sizes.numResults.toInt ≤ ctx.buf.size)
    (hslot : (Buffed.OperationMPtr.getResultPtr ctx.buf opPtr.impl idx hnum).toNat + Buffed.OpResult.size.toNat ≤ ctx.buf.size)
    {bufctx : Buffed.IRBufContext OpInfo}
    (heq : Rewriter.setResult opPtr.impl ctx.buf idx hnum hslot type = some bufctx) :
    Veir.Sim ⟨bufctx, Rewriter.pushResult ctx.spec opPtr.spec type (by grind)⟩ := by
  simp only [Rewriter.setResult] at heq
  split at heq
  case h_1 => simp at heq
  case h_2 ctx1 typeIdx heqAttr =>
  rw [Option.some_inj] at heq
  simp only [Buffed.OperationMPtr.getResultPtr_eq_getResultPtr!] at heq
  have hslotB : (Buffed.OperationMPtr.getResultPtr! ctx.buf opPtr.impl idx).toNat + Buffed.OpResult.size.toNat ≤ ctx.buf.size := by
    rw [← Buffed.OperationMPtr.getResultPtr_eq_getResultPtr! (h := hnum)]
    exact hslot
  have hmem1 : ctx1.mem = ctx.buf.mem := by
    clear heq
    grind [Buffed.IRBufContext.insertAttrs]
  have hattr1 : ctx1.attributes = ctx.buf.attributes.push type := by
    clear heq
    grind [Buffed.IRBufContext.insertAttrs]
  have htidx : typeIdx.toNat = ctx.buf.attributes.size := by
    clear heq
    grind [Buffed.IRBufContext.insertAttrs]
  have hin := ctx.sim.in_bounds (.operation opPtr.spec) (by clear heq heqAttr hmem1 hattr1 htidx; grind)
  have hsz : ctx.buf.mem.size < 2^63 := by clear heq heqAttr hmem1 hattr1 htidx; grind
  have hincl := OperationPtr.nthResult_range_included_op_range ctx opPtr.spec idx hcap (by clear heq heqAttr hmem1 hattr1 htidx; grind)
  have hidxlt : idx.toNat < 4294967296 := by
    clear heq heqAttr hmem1 hattr1 htidx
    have := ctx.isRepr.operations_indices opPtr.spec (by grind) |>.capResults
    grind
  have hmul : (Buffed.OpResult.size * idx).toNat = Buffed.OpResult.sizeNat * idx.toNat := by
    clear heq heqAttr hmem1 hattr1 htidx
    rw [UInt64.toNat_mul]
    grind
  have hoff := OperationPtr.computeResultsOffset!_ideal ctx opPtr (by clear heq heqAttr hmem1 hattr1 htidx; grind) (by clear heq heqAttr hmem1 hattr1 htidx; grind) hnum
  have hopM : (UInt64.toNat opPtr.impl : Int) = opPtr.spec.toFlat := by
    clear heq heqAttr hmem1 hattr1 htidx
    have := opPtrInBounds.sim
    simp only [Sim.OperationPtr.Sim_def, OperationPtr.toM] at this
    grind [OperationPtr.toFlat, OperationPtr.range]
  have hslotaddr : ((Buffed.OperationMPtr.getResultPtr! ctx.buf opPtr.impl idx).toNat : Int)
      = opPtr.spec.toFlat + (Buffed.Operation.Offsets.resultsInt opPtr.spec ctx.spec + Buffed.OpResult.sizeNat * idx.toNat) := by
    clear heq heqAttr hmem1 hattr1 htidx
    simp only [Buffed.OperationMPtr.getResultPtr!, Buffed.OperationMPtr.computeResultOffset!]
    grind [IsIncludedI, IsIncludedIN]
  have husz : (Buffed.OperationMPtr.getResultPtr! ctx.buf opPtr.impl idx).toNat + 40 ≤ ctx.buf.mem.size := by
    clear heq heqAttr hmem1 hattr1 htidx
    grind
  have ek : ∀ (off : Int64) (n : Nat), off.toInt = n → n + 8 ≤ 40 →
      ((Buffed.OperationMPtr.getResultPtr! ctx.buf opPtr.impl idx) + off).toNat
        = (Buffed.OperationMPtr.getResultPtr! ctx.buf opPtr.impl idx).toNat + n := by
    intro off n hn h40
    clear heq heqAttr hmem1 hattr1 htidx
    rw [UInt64.uint64_add_int64_toNat_lt] <;> grind
  have hread : ∀ (a : UInt64),
      (a.toNat + 8 ≤ (Buffed.OperationMPtr.getResultPtr! ctx.buf opPtr.impl idx).toNat
       ∨ (Buffed.OperationMPtr.getResultPtr! ctx.buf opPtr.impl idx).toNat + 40 ≤ a.toNat) →
      bufctx.mem.read64! a = ctx.buf.mem.read64! a := by
    intro a ha
    rw [← heq]
    simp only [Buffed.OpResultMPtr.writeOwner, Buffed.OpResultMPtr.writeIndex,
      Buffed.OpResultMPtr.writeFirstUse, Buffed.OpResultMPtr.writeType, Buffed.ValueImplMPtr.writeKind]
    rw [ExArray.read64!_blit64_disjoint _ _ _ _ _
        (by simp only [IsDisjoint]; have := ek Buffed.OpResult.Offsets.owner 32 (by decide) (by decide); omega),
      ExArray.read64!_blit64_disjoint _ _ _ _ _
        (by simp only [IsDisjoint]; have := ek Buffed.OpResult.Offsets.index 24 (by decide) (by decide); omega),
      ExArray.read64!_blit64_disjoint _ _ _ _ _
        (by simp only [IsDisjoint]; have := ek Buffed.ValueImpl.Offsets.firstUse 16 (by decide) (by decide); omega),
      ExArray.read64!_blit64_disjoint _ _ _ _ _
        (by simp only [IsDisjoint]; have := ek Buffed.ValueImpl.Offsets.type 8 (by decide) (by decide); omega),
      ExArray.read64!_blit64_disjoint _ _ _ _ _
        (by simp only [IsDisjoint]; omega),
      hmem1]
  have hread32 : ∀ (a : UInt64),
      (a.toNat + 4 ≤ (Buffed.OperationMPtr.getResultPtr! ctx.buf opPtr.impl idx).toNat
       ∨ (Buffed.OperationMPtr.getResultPtr! ctx.buf opPtr.impl idx).toNat + 40 ≤ a.toNat) →
      bufctx.mem.read32! a = ctx.buf.mem.read32! a := by
    intro a ha
    rw [← heq]
    simp only [Buffed.OpResultMPtr.writeOwner, Buffed.OpResultMPtr.writeIndex,
      Buffed.OpResultMPtr.writeFirstUse, Buffed.OpResultMPtr.writeType, Buffed.ValueImplMPtr.writeKind]
    rw [ExArray.read32!_blit64_disjoint _ _ _ _ _
        (by simp only [IsDisjoint]; have := ek Buffed.OpResult.Offsets.owner 32 (by decide) (by decide); omega),
      ExArray.read32!_blit64_disjoint _ _ _ _ _
        (by simp only [IsDisjoint]; have := ek Buffed.OpResult.Offsets.index 24 (by decide) (by decide); omega),
      ExArray.read32!_blit64_disjoint _ _ _ _ _
        (by simp only [IsDisjoint]; have := ek Buffed.ValueImpl.Offsets.firstUse 16 (by decide) (by decide); omega),
      ExArray.read32!_blit64_disjoint _ _ _ _ _
        (by simp only [IsDisjoint]; have := ek Buffed.ValueImpl.Offsets.type 8 (by decide) (by decide); omega),
      ExArray.read32!_blit64_disjoint _ _ _ _ _
        (by simp only [IsDisjoint]; omega),
      hmem1]
  have hattrB : bufctx.attributes = ctx.buf.attributes.push type := by
    rw [← heq]
    simp only [Buffed.OpResultMPtr.writeOwner, Buffed.OpResultMPtr.writeIndex,
      Buffed.OpResultMPtr.writeFirstUse, Buffed.OpResultMPtr.writeType, Buffed.ValueImplMPtr.writeKind]
    exact hattr1
  have hbsz : bufctx.mem.size = ctx.buf.mem.size := by
    rw [← heq]
    simp only [Buffed.OpResultMPtr.writeOwner, Buffed.OpResultMPtr.writeIndex,
      Buffed.OpResultMPtr.writeFirstUse, Buffed.OpResultMPtr.writeType, Buffed.ValueImplMPtr.writeKind,
      ExArray.size_blit64, hmem1]
  have hbrange : bufctx.mem.range = ctx.buf.mem.range := by
    rw [← heq]
    simp only [Buffed.OpResultMPtr.writeOwner, Buffed.OpResultMPtr.writeIndex,
      Buffed.OpResultMPtr.writeFirstUse, Buffed.OpResultMPtr.writeType, Buffed.ValueImplMPtr.writeKind,
      ExArray.range_blit64, hmem1]
  have hlay : ctx.spec.LayoutPreserved (Rewriter.pushResult ctx.spec opPtr.spec type (by grind)) :=
    IRContext.LayoutPreserved.of_layoutUnchanged_ltr (by
      clear hread hread32 ek heq
      (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
      grind [Rewriter.pushResult])
  -- The five writes stay inside the fresh 40-byte slot, and the attribute table only
  -- grows, so any window disjoint from the slot agrees (lookup-preserving `AgreesOn`).
  have hagreeD : ∀ lo hi : Nat,
      (hi ≤ (Buffed.OperationMPtr.getResultPtr! ctx.buf opPtr.impl idx).toNat ∨ (Buffed.OperationMPtr.getResultPtr! ctx.buf opPtr.impl idx).toNat + 40 ≤ lo) →
      Buffed.AgreesOn bufctx ctx.buf lo hi :=
    fun lo hi hd => ⟨fun a h1 h2 => hread a (by omega), fun a h1 h2 => hread32 a (by omega),
      fun i a h => by
        rw [hattrB]
        grind [Array.getElem?_push_lt, Array.getElem?_eq_some_iff]⟩
  constructor
  · -- fieldsInBounds
    clear hread hread32 ek hagreeD heq
    (try clear hslotB hbsz hbrange hmem1 hattr1 heqAttr)
    have hofib : OpResult.FieldsInBounds
        { type := type, firstUse := none, index := opPtr.spec.getNumResults! ctx.spec,
          owner := opPtr.spec } ctx.spec := by
      constructor <;> grind
    have hofibP : OpResult.FieldsInBounds
        { type := type, firstUse := none, index := opPtr.spec.getNumResults! ctx.spec,
          owner := opPtr.spec } (Rewriter.pushResult ctx.spec opPtr.spec type (by grind)) := by
      constructor <;> grind [Rewriter.pushResult]
    grind [Rewriter.pushResult]
  · -- repr
    clear hread hread32 ek hagreeD heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
    grind [Rewriter.pushResult, layout_grind]
  · -- in_bounds
    simp only
    intros gptr gptrIb
    clear hread hread32 ek hagreeD heq; (try clear hslotB hattrB hbsz hmem1 hattr1 htidx heqAttr)
    have := ctx.sim.in_bounds gptr (by grind [Rewriter.pushResult])
    grind [TopLevelPtr, Rewriter.pushResult]
  · -- disjoint_allocs
    simp only
    clear hread hread32 ek hagreeD heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
    have := ctx.sim.disjoint_allocs
    grind [TopLevelPtr, Rewriter.pushResult]
  · -- encoding_op
    simp only
    intros op opIb
    have hopib : op.InBounds ctx.spec := by
      clear hread hread32 ek hagreeD heq hoff hslotaddr husz hincl hmul hidxlt
      (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
      grind [Rewriter.pushResult]
    have henc := ctx.sim.encoding_op op hopib
    have hrrange := Veir.Sim.OperationPtr.range_linear (ctx := ctx) op hopib
    have hwrange := Veir.Sim.OperationPtr.range_linear (ctx := ctx) opPtr.spec opPtrInBounds.ib
    have hdisj := fun hne : op ≠ opPtr.spec =>
      Veir.Sim.disjoint_operation_operation (ctx := ctx) op opPtr.spec hopib opPtrInBounds.ib hne
    have hoin := ctx.sim.in_bounds (.operation op) (by grind)
    have hopM : (UInt64.toNat op.toM : Int) = op.toFlat := by
      clear hread hread32 ek hagreeD heq
      (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
      simp only [OperationPtr.toM]
      grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', OperationPtr.toFlat, layout_grind]
    have hgets : ((op.get! (Rewriter.pushResult ctx.spec opPtr.spec type (by grind))).prev = (op.get! ctx.spec).prev
        ∧ (op.get! (Rewriter.pushResult ctx.spec opPtr.spec type (by grind))).next = (op.get! ctx.spec).next
        ∧ (op.get! (Rewriter.pushResult ctx.spec opPtr.spec type (by grind))).parent = (op.get! ctx.spec).parent
        ∧ (op.get! (Rewriter.pushResult ctx.spec opPtr.spec type (by grind))).attrs = (op.get! ctx.spec).attrs
        ∧ op.getOpType! (Rewriter.pushResult ctx.spec opPtr.spec type (by grind)) = op.getOpType! ctx.spec
        ∧ (op.get! (Rewriter.pushResult ctx.spec opPtr.spec type (by grind))).capBlockOperands = (op.get! ctx.spec).capBlockOperands
        ∧ (op.get! (Rewriter.pushResult ctx.spec opPtr.spec type (by grind))).capRegions = (op.get! ctx.spec).capRegions
        ∧ (op.get! (Rewriter.pushResult ctx.spec opPtr.spec type (by grind))).capOperands = (op.get! ctx.spec).capOperands
        ∧ (op.get! (Rewriter.pushResult ctx.spec opPtr.spec type (by grind))).capResults = (op.get! ctx.spec).capResults) := by
      clear hread hread32 ek hagreeD heq hoff hslotaddr husz hincl hmul hidxlt
      (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
      grind [Rewriter.pushResult]
    obtain ⟨hgprev, hgnext, hgpar, hgattrs, hgty, hgcB, hgcRg, hgcO, hgcR⟩ := hgets
    constructor
    · -- MatchesBase: framed — the write lands in the result array, below the header.
      refine OperationPtr.matchesBase_frame ctx op hopib henc.toMatchesBase (hagreeD _ _ ?_) hlay
        hgprev hgnext hgpar hgattrs hgty opIb
      clear hread hread32 ek hagreeD heq hoff husz hmul hidxlt
      (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
      grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
        Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
        _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
        _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
    · constructor
      · refine OperationPtr.numBlockOperands_frame ctx op hopib henc.numBlockOperands (hagreeD _ _ ?_) hgcB
        clear hread hread32 ek hagreeD heq hoff husz hmul hidxlt
        (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
        grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
          Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
          _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
          _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
      · intros bo boIb heq2
        dsimp only at boIb
        have hboib : bo.InBounds ctx.spec := by
          clear hread hread32 ek hagreeD heq hoff hslotaddr husz hincl hmul hidxlt
          (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
          grind [Rewriter.pushResult]
        have hbincl := Veir.Sim.BlockOperandPtr.slot_included (ctx := ctx) bo hboib
        have hboget : bo.get! (Rewriter.pushResult ctx.spec opPtr.spec type (by grind)) = bo.get! ctx.spec := by
          clear hread hread32 ek hagreeD heq hoff hslotaddr husz hincl hmul hidxlt
          (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
          grind [Rewriter.pushResult]
        refine BlockOperandPtr.matches_frame ctx bo hboib (henc.blockOperands bo hboib heq2)
          (hagreeD _ _ ?_) hlay hboget boIb
        clear hread hread32 ek hagreeD heq hoff husz hmul hidxlt
        (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
        grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
          Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
          _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
          _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
    · constructor
      · refine OperationPtr.numRegions_frame ctx op hopib henc.numRegions (hagreeD _ _ ?_) hgcRg
        clear hread hread32 ek hagreeD heq hoff husz hmul hidxlt
        (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
        grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
          Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
          _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
          _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
      · intros ridx ridxIn
        dsimp only at ridxIn
        have hnr : ridx < op.getNumRegions! ctx.spec := by
          clear hread hread32 ek hagreeD heq hoff hslotaddr husz hincl hmul hidxlt
          (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
          grind [Rewriter.pushResult]
        have hcapr := ctx.sim.repr.operations_indices op hopib |>.capRegions
        refine OperationPtr.nthRegion_frame ctx op hopib ridx hnr (henc.regions ridx hnr)
          (hagreeD _ _ ?_) ?_
          (by clear hread hread32 ek hagreeD heq hoff hslotaddr husz hincl hmul hidxlt
              (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
              grind [Rewriter.pushResult])
        · clear hread hread32 ek hagreeD heq hoff husz hmul hidxlt
          (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
          grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
        · have hidxc : ridx < (op.get! ctx.spec).capRegions := by
            clear hread hread32 ek hagreeD heq
            grind
          have haddrR : ((op.toM.toNat : Nat) : Int) = op.id := by
            grind [Veir.OperationPtr.toM, _root_.Veir.OperationPtr.toFlat]
          have hcntr := ctx.sim.repr.operations_indices op hopib |>.regions
          have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op ridx.toUInt64
            (by clear hread hread32 ek hagreeD heq hoff husz hmul hidxlt
                grind [UInt64.toNat_ofNat']) hopib
          refine hagreeD _ _ ?_
          clear hread hread32 ek hagreeD heq hoff husz hmul hidxlt
          (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
          grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt, UInt64.toNat_ofNat']
    · constructor
      · refine OperationPtr.numOperands_frame ctx op hopib henc.numOperands (hagreeD _ _ ?_) hgcO
        clear hread hread32 ek hagreeD heq hoff husz hmul hidxlt
        (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
        grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
          Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
          _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
          _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
      · intros oper operIb heq2
        dsimp only at operIb
        have hoperib : oper.InBounds ctx.spec := by
          clear hread hread32 ek hagreeD heq hoff hslotaddr husz hincl hmul hidxlt
          (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
          grind [Rewriter.pushResult]
        have hoincl := Veir.Sim.OpOperandPtr.slot_included (ctx := ctx) oper hoperib
        have hoperget : oper.get! (Rewriter.pushResult ctx.spec opPtr.spec type (by grind)) = oper.get! ctx.spec := by
          clear hread hread32 ek hagreeD heq hoff hslotaddr husz hincl hmul hidxlt
          (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
          grind [Rewriter.pushResult]
        refine OpOperandPtr.matches_frame ctx oper hoperib (henc.operands oper hoperib heq2)
          (hagreeD _ _ ?_) hlay hoperget operIb
        clear hread hread32 ek hagreeD heq hoff husz hmul hidxlt
        (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
        grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
          Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
          _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
          _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
    · constructor
      · refine OperationPtr.numResults_frame ctx op hopib henc.numResults (hagreeD _ _ ?_) hgcR
        clear hread hread32 ek hagreeD heq hoff husz hmul hidxlt
        (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
        grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
          Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
          _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
          _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
      · intros res resIb heq2
        dsimp only at resIb
        by_cases hnewres : res = opPtr.spec.nextResult ctx.spec
        · -- the freshly pushed result: reads land on the five writes just made
          have hopeq : op = opPtr.spec := by
            clear hread hread32 ek hagreeD hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
            (try clear hro8 hro4); (try clear hslot hnum)
            grind
          subst hopeq
          subst hnewres
          have hnidx : (opPtr.spec.nextResult ctx.spec).index = idx.toNat := by
            clear hread hread32 ek hagreeD hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
            (try clear hro8 hro4); (try clear hslot hnum)
            grind
          have hnop : (opPtr.spec.nextResult ctx.spec).op = opPtr.spec := by
            clear hread hread32 ek hagreeD hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
            (try clear hro8 hro4); (try clear hslot hnum)
            grind
          have hreprN : (Rewriter.pushResult ctx.spec opPtr.spec type (by grind)).IsRepr := by
            clear hread hread32 ek hagreeD hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
            (try clear hro8 hro4); (try clear hslot hnum)
            grind [Rewriter.pushResult, layout_grind]
          have hnget : (opPtr.spec.nextResult ctx.spec).get! (Rewriter.pushResult ctx.spec opPtr.spec type (by grind))
              = { type := type, firstUse := none, index := opPtr.spec.getNumResults! ctx.spec,
                  owner := opPtr.spec } := by
            clear hread hread32 ek hagreeD hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
            (try clear hro8 hro4); (try clear hslot hnum)
            grind [Rewriter.pushResult]
          have hopsame : Buffed.Operation.Offsets.resultsInt opPtr.spec (Rewriter.pushResult ctx.spec opPtr.spec type (by grind))
              = Buffed.Operation.Offsets.resultsInt opPtr.spec ctx.spec := by
            clear hread hread32 ek hagreeD hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
            (try clear hro8 hro4); (try clear hslot hnum)
            grind [Rewriter.pushResult]
          have hoplow : (0:Int) ≤ opPtr.spec.toFlat + Buffed.Operation.Offsets.resultsInt opPtr.spec ctx.spec := by
            have hio := hin
            have hr := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr opPtrInBounds.ib
            simp only [TopLevelPtr.range, hr, OperationPtr.rangeInt, Buffed.Operation.rangeInt,
              add_nat_range_def, IsIncludedIN] at hio
            grind [ExArray.range_lower, ExArray.range_upper]
          have hnflat : ((((opPtr.spec.nextResult ctx.spec).toFlat (Rewriter.pushResult ctx.spec opPtr.spec type (by grind))) : Nat) : Int)
              = opPtr.spec.toFlat + Buffed.Operation.Offsets.resultsInt opPtr.spec ctx.spec + ((idx.toNat * 40 : Nat) : Int) := by
            rw [OpResultPtr.toFlat_ideal hreprN _ resIb]
            simp only [OpResultPtr.toFlatNat, hnop, hnidx, hopsame, show Buffed.OpResult.sizeNat = 40 from rfl]
            omega
          have hnMeq : (opPtr.spec.nextResult ctx.spec).toM (Rewriter.pushResult ctx.spec opPtr.spec type (by grind))
              = Buffed.OperationMPtr.getResultPtr! ctx.buf opPtr.impl idx := by
            clear hread hread32 ek hagreeD heq hoff hincl husz hmul
            (try clear hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr hslotB)
            (try clear hro8 hro4)
            (try clear hnget hreprN hopsame)
            (try clear henc hd haft hri hareaOP hareaBO hareaRG hareaAFT hareaRES hareaRESP hoin hin)
            (try clear hrrange hwrange hdisj hlay)
            simp only [OpResultPtr.toM]
            grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', UInt64.toNat_inj]
          constructor
          · -- kind
            simp only [Buffed.OpResultMPtr.readKind!, hnMeq]
            rw [← heq]
            simp only [Buffed.OpResultMPtr.writeOwner, Buffed.OpResultMPtr.writeIndex,
              Buffed.OpResultMPtr.writeFirstUse, Buffed.OpResultMPtr.writeType, Buffed.ValueImplMPtr.writeKind]
            rw [ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have h1 := ek Buffed.OpResult.Offsets.owner 32 (by decide) (by decide); omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have h1 := ek Buffed.OpResult.Offsets.index 24 (by decide) (by decide); omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have h1 := ek Buffed.ValueImpl.Offsets.firstUse 16 (by decide) (by decide); omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have h1 := ek Buffed.ValueImpl.Offsets.type 8 (by decide) (by decide); omega),
              ExArray.read64!_blit64_self]
          · -- typee
            simp only [Buffed.OpResultMPtr.readType!, hnMeq, hnget, hattrB]
            rw [← heq]
            simp only [Buffed.OpResultMPtr.writeOwner, Buffed.OpResultMPtr.writeIndex,
              Buffed.OpResultMPtr.writeFirstUse, Buffed.OpResultMPtr.writeType, Buffed.ValueImplMPtr.writeKind]
            rw [ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have h1 := ek Buffed.OpResult.Offsets.owner 32 (by decide) (by decide); have h2 := ek Buffed.ValueImpl.Offsets.type 8 (by decide) (by decide); omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have h1 := ek Buffed.OpResult.Offsets.index 24 (by decide) (by decide); have h2 := ek Buffed.ValueImpl.Offsets.type 8 (by decide) (by decide); omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have h1 := ek Buffed.ValueImpl.Offsets.firstUse 16 (by decide) (by decide); have h2 := ek Buffed.ValueImpl.Offsets.type 8 (by decide) (by decide); omega),
              ExArray.read64!_blit64_self]
            (try dsimp only)
            clear hread hread32 ek hagreeD heq
            (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 heqAttr)
            grind
          · -- firstUse
            simp only [Buffed.OpResultMPtr.readFirstUse!, hnMeq, hnget]
            rw [← heq]
            simp only [Buffed.OpResultMPtr.writeOwner, Buffed.OpResultMPtr.writeIndex,
              Buffed.OpResultMPtr.writeFirstUse, Buffed.OpResultMPtr.writeType, Buffed.ValueImplMPtr.writeKind]
            rw [ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have h1 := ek Buffed.OpResult.Offsets.owner 32 (by decide) (by decide); have h2 := ek Buffed.ValueImpl.Offsets.firstUse 16 (by decide) (by decide); omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have h1 := ek Buffed.OpResult.Offsets.index 24 (by decide) (by decide); have h2 := ek Buffed.ValueImpl.Offsets.firstUse 16 (by decide) (by decide); omega),
              ExArray.read64!_blit64_self]
            exact (Sim.OptionOpOperandPtr.Sim_def _ _).mpr rfl
          · -- index
            simp only [Buffed.OpResultMPtr.readIndex!, hnMeq, hnget]
            rw [← heq]
            simp only [Buffed.OpResultMPtr.writeOwner, Buffed.OpResultMPtr.writeIndex,
              Buffed.OpResultMPtr.writeFirstUse, Buffed.OpResultMPtr.writeType, Buffed.ValueImplMPtr.writeKind]
            rw [ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have h1 := ek Buffed.OpResult.Offsets.owner 32 (by decide) (by decide); have h2 := ek Buffed.OpResult.Offsets.index 24 (by decide) (by decide); omega),
              ExArray.read64!_blit64_self]
            clear hread hread32 ek hagreeD heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
            grind
          · -- owner
            simp only [Buffed.OpResultMPtr.readOwner!, hnMeq, hnget]
            rw [← heq]
            simp only [Buffed.OpResultMPtr.writeOwner, Buffed.OpResultMPtr.writeIndex,
              Buffed.OpResultMPtr.writeFirstUse, Buffed.OpResultMPtr.writeType, Buffed.ValueImplMPtr.writeKind]
            rw [ExArray.read64!_blit64_self]
            have := opPtrInBounds.sim
            clear hread hread32 ek hagreeD hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
            (try clear hro8 hro4); (try clear hslot hnum)
            grind [Rewriter.pushResult]
        · -- pre-existing result: framed — its slot sits strictly below the written one.
          have hresib : res.InBounds ctx.spec := by
            clear hread hread32 ek hagreeD heq hoff hslotaddr husz hincl hmul hidxlt
            (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
            grind [Rewriter.pushResult]
          have hrincl := Veir.Sim.OpResultPtr.slot_included (ctx := ctx) res hresib
          have hridxc : op = opPtr.spec → res.index < idx.toNat := by
            clear hread hread32 ek hagreeD heq hoff hslotaddr husz hincl hmul hidxlt
            (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
            intro hop
            grind [Veir.OpResultPtr.inBounds_def]
          have hoplow : (0:Int) ≤ op.toFlat + Buffed.Operation.Offsets.resultsInt op ctx.spec := by
            have hio := hoin
            have hr := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr hopib
            simp only [TopLevelPtr.range, hr, OperationPtr.rangeInt, Buffed.Operation.rangeInt,
              add_nat_range_def, IsIncludedIN] at hio
            grind [ExArray.range_lower, ExArray.range_upper]
          have hresflat : ((res.toFlatNat ctx.spec : Nat) : Int)
              = op.toFlat + Buffed.Operation.Offsets.resultsInt op ctx.spec + ((res.index * 40 : Nat) : Int) := by
            simp only [OpResultPtr.toFlatNat, heq2, show Buffed.OpResult.sizeNat = 40 from rfl]
            omega
          have hresget : res.get! (Rewriter.pushResult ctx.spec opPtr.spec type (by grind)) = res.get! ctx.spec := by
            clear hread hread32 ek hagreeD heq hoff hslotaddr husz hincl hmul hidxlt
            (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
            grind [Rewriter.pushResult]
          refine OpResultPtr.matches_frame ctx res hresib (henc.results res hresib heq2)
            (hagreeD _ _ ?_) hlay hresget resIb
          clear hread hread32 ek hagreeD heq hoff husz hmul hidxlt
          (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
          grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
  · -- encoding_block
    simp only
    intros blk blkIb
    have hblkib : blk.InBounds ctx.spec := by
      clear hread hread32 ek hagreeD heq hoff hslotaddr husz hincl hmul hidxlt
      (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
      grind [Rewriter.pushResult]
    have henc := ctx.sim.encoding_block blk hblkib
    have hbrange2 := Veir.Sim.BlockPtr.range_linear (ctx := ctx) blk hblkib
    have hwrange := Veir.Sim.OperationPtr.range_linear (ctx := ctx) opPtr.spec opPtrInBounds.ib
    have hdisjB := Veir.Sim.disjoint_block_operation (ctx := ctx) blk opPtr.spec hblkib opPtrInBounds.ib
    have hbget : blk.get! (Rewriter.pushResult ctx.spec opPtr.spec type (by grind)) = blk.get! ctx.spec := by
      clear hread hread32 ek hagreeD heq hoff hslotaddr husz hincl hmul hidxlt
      (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
      grind [Rewriter.pushResult]
    constructor
    · refine BlockPtr.matchesBase_frame ctx blk hblkib henc.toMatchesBase (hagreeD _ _ ?_) hlay
        (by rw [hbget]) (by rw [hbget]) (by rw [hbget]) (by rw [hbget]) (by rw [hbget]) (by rw [hbget]) blkIb
      clear hread hread32 ek hagreeD heq hoff husz hmul hidxlt
      (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
      grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
        Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
        _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
        _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
    · constructor
      · refine BlockPtr.numArguments_frame ctx blk hblkib henc.numArguments (hagreeD _ _ ?_) (by rw [hbget])
        clear hread hread32 ek hagreeD heq hoff husz hmul hidxlt
        (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
        grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
          Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
          _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
          _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
      · intros arg argIn heq2
        dsimp only at argIn
        have hargib : arg.InBounds ctx.spec := by
          clear hread hread32 ek hagreeD heq hoff hslotaddr husz hincl hmul hidxlt
          (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
          grind [Rewriter.pushResult]
        have haincl := Veir.Sim.BlockArgumentPtr.slot_included (ctx := ctx) arg hargib
        have hargget : arg.get! (Rewriter.pushResult ctx.spec opPtr.spec type (by grind)) = arg.get! ctx.spec := by
          clear hread hread32 ek hagreeD heq hoff hslotaddr husz hincl hmul hidxlt
          (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
          grind [Rewriter.pushResult]
        refine BlockArgumentPtr.matches_frame ctx arg hargib (henc.arguments arg hargib heq2)
          (hagreeD _ _ ?_) hlay hargget argIn
        clear hread hread32 ek hagreeD heq hoff husz hmul hidxlt
        (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
        grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
          Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
          _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
          _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
  · -- encoding_region
    simp only
    intros rg rgIb
    have hrgib : rg.InBounds ctx.spec := by
      clear hread hread32 ek hagreeD heq hoff hslotaddr husz hincl hmul hidxlt
      (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
      grind [Rewriter.pushResult]
    have henc := ctx.sim.encoding_region rg hrgib
    have hrgrange := Veir.Sim.RegionPtr.range_linear (ctx := ctx) rg hrgib
    have hwrange := Veir.Sim.OperationPtr.range_linear (ctx := ctx) opPtr.spec opPtrInBounds.ib
    have hdisjR := Veir.Sim.disjoint_region_operation (ctx := ctx) rg opPtr.spec hrgib opPtrInBounds.ib
    have hrgget : rg.get! (Rewriter.pushResult ctx.spec opPtr.spec type (by grind)) = rg.get! ctx.spec := by
      clear hread hread32 ek hagreeD heq hoff hslotaddr husz hincl hmul hidxlt
      (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
      grind [Rewriter.pushResult]
    refine RegionPtr.matches_frame ctx rg hrgib henc (hagreeD _ _ ?_) hlay hrgget rgIb
    clear hread hread32 ek hagreeD heq hoff husz hmul hidxlt
    (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
    grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
      Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
      _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
      _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
  · -- attr_empty: the table only gained a new entry, slot 0 is untouched
    (try dsimp only)
    rw [hattrB]
    have := ctx.sim.attr_empty
    clear hread hread32 ek hagreeD heq
    grind

end Veir
