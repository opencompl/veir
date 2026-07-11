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

/-! Block-argument push simulation proofs -/

@[expose] public section
namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo] [SerializableOpInfo OpInfo]
variable {ctx : Sim.IRContext OpInfo}

/-- Unfolding equation for `BlockPtr.pushArgument`, phrased at the `setArguments` level where the `GetSet` transport lemmas live. -/
private theorem BlockPtr.pushArgument_def {ctx : IRContext OpInfo} (block : BlockPtr) (result : BlockArgument)
    (h : block.InBounds ctx) :
    block.pushArgument ctx result h
      = block.setArguments ctx ((block.get ctx h).arguments.push result) h := rfl

protected def Rewriter.pushBlockArgument (ctx : IRContext OpInfo) (blockPtr : BlockPtr) (type : TypeAttr)
    (blockPtrInBounds : blockPtr.InBounds ctx := by grind) : IRContext OpInfo :=
  let index := blockPtr.getNumArguments ctx (by grind)
  let argument := { type := type, firstUse := none, index := index, loc := (), owner := blockPtr : BlockArgument }
  blockPtr.pushArgument ctx argument (by grind)

/-- The five 8-byte field writes into the (pre-allocated) argument slot `idx` of `blockPtr`. -/
@[inline]
protected def Rewriter.setBlockArgumentRaw (blockPtr : Buffed.BlockMPtr) (ctx₁ : Buffed.IRBufContext OpInfo)
    (idx : UInt64) (typeIdx : UInt64)
    (hslot : (blockPtr.getArgumentPtr idx).toNat + Buffed.BlockArgument.size.toNat ≤ ctx₁.size) :
    Buffed.IRBufContext OpInfo :=
  let arg := blockPtr.getArgumentPtr idx
  let ctx := Buffed.ValueImplMPtr.writeKind ctx₁ arg Buffed.ValueImpl.kindArgument (by prove_setSlotBounds ctx₁)
  let ctx := arg.writeType ctx typeIdx (by prove_setSlotBounds ctx₁)
  let ctx := arg.writeFirstUse ctx .none (by prove_setSlotBounds ctx₁)
  let ctx := arg.writeIndex ctx idx (by prove_setSlotBounds ctx₁)
  let ctx := arg.writeOwner ctx blockPtr (by prove_setSlotBounds ctx₁)
  ctx

@[inline]
protected def Rewriter.setBlockArgument (blockPtr : Buffed.BlockMPtr) (ctx₀ : Buffed.IRBufContext OpInfo) (idx : UInt64)
    (hslot : (blockPtr.getArgumentPtr idx).toNat + Buffed.BlockArgument.size.toNat ≤ ctx₀.size)
    (type : TypeAttr) : Option (Buffed.IRBufContext OpInfo) :=
  rlet hattr : (ctx, typeIdx) ← ctx₀.insertAttrs type
  have hsz : ctx.size = ctx₀.size := ctx₀.insertAttrs_size hattr
  some (Rewriter.setBlockArgumentRaw blockPtr ctx idx typeIdx (by grind))

set_option maxHeartbeats 1000000000 in
/-- The `Sim` relation survives writing a fresh block argument into slot `idx` of `blockPtr`'s (pre-allocated) argument array while the spec pushes the corresponding `BlockArgument`. -/
theorem Rewriter.setBlockArgumentRaw_pushBlockArgument_sim (blockPtr : Sim.BlockPtr) (ctx : Sim.IRContext OpInfo)
    (idx : UInt64) (type : TypeAttr)
    (blockPtrInBounds : blockPtr.InBounds ctx)
    (hidx : idx.toNat = blockPtr.spec.getNumArguments! ctx.spec)
    (hcap : idx.toNat < (blockPtr.spec.get! ctx.spec).capArguments)
    (buf₁ : Buffed.IRBufContext OpInfo) (typeIdx : UInt64)
    (hmem : buf₁.mem = ctx.buf.mem)
    (hattrs : buf₁.attributes = ctx.buf.attributes.push type)
    (htidx : typeIdx.toNat = ctx.buf.attributes.size)
    (hslot' : (Buffed.BlockMPtr.getArgumentPtr blockPtr.impl idx).toNat + Buffed.BlockArgument.size.toNat ≤ buf₁.size) :
    Veir.Sim (OpInfo := OpInfo)
      ⟨Rewriter.setBlockArgumentRaw blockPtr.impl buf₁ idx typeIdx hslot',
       Rewriter.pushBlockArgument ctx.spec blockPtr.spec type (by grind)⟩ := by
  have hin := ctx.sim.in_bounds (.block blockPtr.spec) (by grind)
  have hszb : ctx.buf.mem.size < 2^63 := by grind
  have hincl := BlockPtr.nthArgument_range_included_block_range ctx blockPtr.spec idx hcap (by grind)
  have hidxlt : idx.toNat < 4294967296 := by
    have := ctx.isRepr.blocks_indices blockPtr.spec (by grind) |>.arguments
    grind
  have hmul : (Buffed.BlockArgument.size * idx).toNat = Buffed.BlockArgument.sizeNat * idx.toNat := by
    rw [UInt64.toNat_mul]
    grind
  have hoff := BlockPtr.computeArgumentOffset_ideal ctx blockPtr idx (by grind) hcap
  have hblM : (UInt64.toNat blockPtr.impl : Int) = blockPtr.spec.toFlat := by
    have := blockPtrInBounds.sim
    simp only [Sim.BlockPtr.Sim_def, BlockPtr.toM] at this
    grind [BlockPtr.toFlat, BlockPtr.range]
  have hbM : blockPtr.spec.toM = blockPtr.impl := blockPtrInBounds.sim.out
  have hslotaddr : ((Buffed.BlockMPtr.getArgumentPtr blockPtr.impl idx).toNat : Int)
      = blockPtr.spec.toFlat + (Buffed.Block.Offsets.argumentsInt + Buffed.BlockArgument.sizeNat * idx.toNat) := by
    simp only [Buffed.BlockMPtr.getArgumentPtr]
    rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [IsIncludedI, IsIncludedIN]
  have husz : (Buffed.BlockMPtr.getArgumentPtr blockPtr.impl idx).toNat + 40 ≤ ctx.buf.mem.size := by
    have := buf₁.size_def
    grind
  have ek : ∀ (off : Int64) (n : Nat), off.toInt = n → n + 8 ≤ 40 →
      ((Buffed.BlockMPtr.getArgumentPtr blockPtr.impl idx) + off).toNat
        = (Buffed.BlockMPtr.getArgumentPtr blockPtr.impl idx).toNat + n := by
    intro off n hn h40
    rw [UInt64.uint64_add_int64_toNat_lt] <;> grind
  have hread : ∀ (a : UInt64),
      (a.toNat + 8 ≤ (Buffed.BlockMPtr.getArgumentPtr blockPtr.impl idx).toNat
       ∨ (Buffed.BlockMPtr.getArgumentPtr blockPtr.impl idx).toNat + 40 ≤ a.toNat) →
      (Rewriter.setBlockArgumentRaw blockPtr.impl buf₁ idx typeIdx hslot').mem.read64! a = ctx.buf.mem.read64! a := by
    intro a ha
    simp only [Rewriter.setBlockArgumentRaw, Buffed.BlockArgumentMPtr.writeOwner,
      Buffed.BlockArgumentMPtr.writeIndex, Buffed.BlockArgumentMPtr.writeFirstUse,
      Buffed.BlockArgumentMPtr.writeType, Buffed.ValueImplMPtr.writeKind, hmem]
    rw [ExArray.read64!_blit64_disjoint _ _ _ _ _
        (by simp only [IsDisjoint]; have := ek Buffed.BlockArgument.Offsets.owner 32 (by decide) (by decide); omega),
      ExArray.read64!_blit64_disjoint _ _ _ _ _
        (by simp only [IsDisjoint]; have := ek Buffed.BlockArgument.Offsets.index 24 (by decide) (by decide); omega),
      ExArray.read64!_blit64_disjoint _ _ _ _ _
        (by simp only [IsDisjoint]; have := ek Buffed.ValueImpl.Offsets.firstUse 16 (by decide) (by decide); omega),
      ExArray.read64!_blit64_disjoint _ _ _ _ _
        (by simp only [IsDisjoint]; have := ek Buffed.ValueImpl.Offsets.type 8 (by decide) (by decide); omega),
      ExArray.read64!_blit64_disjoint _ _ _ _ _
        (by simp only [IsDisjoint]; omega)]
  have hread32 : ∀ (a : UInt64),
      (a.toNat + 4 ≤ (Buffed.BlockMPtr.getArgumentPtr blockPtr.impl idx).toNat
       ∨ (Buffed.BlockMPtr.getArgumentPtr blockPtr.impl idx).toNat + 40 ≤ a.toNat) →
      (Rewriter.setBlockArgumentRaw blockPtr.impl buf₁ idx typeIdx hslot').mem.read32! a = ctx.buf.mem.read32! a := by
    intro a ha
    simp only [Rewriter.setBlockArgumentRaw, Buffed.BlockArgumentMPtr.writeOwner,
      Buffed.BlockArgumentMPtr.writeIndex, Buffed.BlockArgumentMPtr.writeFirstUse,
      Buffed.BlockArgumentMPtr.writeType, Buffed.ValueImplMPtr.writeKind, hmem]
    rw [ExArray.read32!_blit64_disjoint _ _ _ _ _
        (by simp only [IsDisjoint]; have := ek Buffed.BlockArgument.Offsets.owner 32 (by decide) (by decide); omega),
      ExArray.read32!_blit64_disjoint _ _ _ _ _
        (by simp only [IsDisjoint]; have := ek Buffed.BlockArgument.Offsets.index 24 (by decide) (by decide); omega),
      ExArray.read32!_blit64_disjoint _ _ _ _ _
        (by simp only [IsDisjoint]; have := ek Buffed.ValueImpl.Offsets.firstUse 16 (by decide) (by decide); omega),
      ExArray.read32!_blit64_disjoint _ _ _ _ _
        (by simp only [IsDisjoint]; have := ek Buffed.ValueImpl.Offsets.type 8 (by decide) (by decide); omega),
      ExArray.read32!_blit64_disjoint _ _ _ _ _
        (by simp only [IsDisjoint]; omega)]
  have hattr : (Rewriter.setBlockArgumentRaw blockPtr.impl buf₁ idx typeIdx hslot').attributes
      = ctx.buf.attributes.push type := by
    simp only [Rewriter.setBlockArgumentRaw, Buffed.BlockArgumentMPtr.writeOwner,
      Buffed.BlockArgumentMPtr.writeIndex, Buffed.BlockArgumentMPtr.writeFirstUse,
      Buffed.BlockArgumentMPtr.writeType, Buffed.ValueImplMPtr.writeKind, hattrs]
  have hattrget : ∀ (i : Nat) (t : Attribute), ctx.buf.attributes[i]? = some t →
      (ctx.buf.attributes.push type)[i]? = some t := by
    grind
  have hlay : ctx.spec.LayoutPreserved (Rewriter.pushBlockArgument ctx.spec blockPtr.spec type (by grind)) :=
    IRContext.LayoutPreserved.of_layoutUnchanged_ltr (by
      clear hread hread32 hattr ek
      grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def])
  have hwrangeB := Veir.Sim.BlockPtr.range_linear (ctx := ctx) blockPtr.spec blockPtrInBounds.ib
  -- The five writes stay inside the fresh 40-byte slot, and the attribute table only
  -- grows, so any window disjoint from the slot agrees (lookup-preserving `AgreesOn`).
  have hagreeD : ∀ lo hi : Nat,
      (hi ≤ (Buffed.BlockMPtr.getArgumentPtr blockPtr.impl idx).toNat ∨ (Buffed.BlockMPtr.getArgumentPtr blockPtr.impl idx).toNat + 40 ≤ lo) →
      Buffed.AgreesOn (Rewriter.setBlockArgumentRaw blockPtr.impl buf₁ idx typeIdx hslot') ctx.buf lo hi :=
    fun lo hi hd => ⟨fun a h1 h2 => hread a (by omega), fun a h1 h2 => hread32 a (by omega),
      fun i a h => by rw [hattr]; exact hattrget i a h⟩
  constructor
  · -- fieldsInBounds
    have hafib : BlockArgument.FieldsInBounds
        { type := type, firstUse := none, index := blockPtr.spec.getNumArguments! ctx.spec,
          loc := (), owner := blockPtr.spec } ctx.spec := by
      constructor <;> grind
    grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
  · -- repr
    clear hread hread32 hattr ek hagreeD hoff hslotaddr husz hincl hmul hidxlt
    grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def, layout_grind]
  · -- in_bounds
    simp only
    intros gptr gptrIb
    have hrange : (Rewriter.setBlockArgumentRaw blockPtr.impl buf₁ idx typeIdx hslot').mem.range
        = ctx.buf.mem.range := by
      simp only [Rewriter.setBlockArgumentRaw, Buffed.BlockArgumentMPtr.writeOwner,
        Buffed.BlockArgumentMPtr.writeIndex, Buffed.BlockArgumentMPtr.writeFirstUse,
        Buffed.BlockArgumentMPtr.writeType, Buffed.ValueImplMPtr.writeKind,
        ExArray.range_blit64, hmem]
    clear hread hread32 hattr ek hagreeD hoff hslotaddr husz hincl hmul hidxlt
    have := ctx.sim.in_bounds gptr (by grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def])
    grind [TopLevelPtr, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def, layout_grind]
  · -- disjoint_allocs
    simp only
    clear hread hread32 hattr ek hagreeD hoff hslotaddr husz hincl hmul hidxlt
    have := ctx.sim.disjoint_allocs
    grind [TopLevelPtr, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
  · -- encoding_op: framed — every operation is disjoint from `blockPtr`'s allocation.
    simp only
    intros op opIb
    have hopib : op.InBounds ctx.spec := by
      clear hagreeD hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
      grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
    have henc := ctx.sim.encoding_op op hopib
    have hrrange := Veir.Sim.OperationPtr.range_linear (ctx := ctx) op hopib
    have hdisjOB := Veir.Sim.disjoint_operation_block (ctx := ctx) op blockPtr.spec hopib blockPtrInBounds.ib
    have hopM : (UInt64.toNat op.toM : Int) = op.toFlat := by
      simp only [OperationPtr.toM]
      grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', OperationPtr.toFlat, layout_grind]
    have hget : op.get! (Rewriter.pushBlockArgument ctx.spec blockPtr.spec type (by grind)) = op.get! ctx.spec := by
      clear hagreeD hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
      grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
    have hgty : op.getOpType! (Rewriter.pushBlockArgument ctx.spec blockPtr.spec type (by grind)) = op.getOpType! ctx.spec := by
      clear hagreeD hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
      grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
    constructor
    · refine OperationPtr.matchesBase_frame ctx op hopib henc.toMatchesBase (hagreeD _ _ ?_) hlay
        (by rw [hget]) (by rw [hget]) (by rw [hget]) (by rw [hget]) hgty opIb
      clear hagreeD hread hread32 hattr ek hoff husz hmul hidxlt
      grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
        Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
        _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
        _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
    · constructor
      · refine OperationPtr.numBlockOperands_frame ctx op hopib henc.numBlockOperands (hagreeD _ _ ?_) (by rw [hget])
        clear hagreeD hread hread32 hattr ek hoff husz hmul hidxlt
        grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
          Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
          _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
          _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
      · intros bo boIb heqbo
        dsimp only at boIb
        have hboib : bo.InBounds ctx.spec := by
          clear hagreeD hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
          grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
        have hbincl := Veir.Sim.BlockOperandPtr.slot_included (ctx := ctx) bo hboib
        have hboget : bo.get! (Rewriter.pushBlockArgument ctx.spec blockPtr.spec type (by grind)) = bo.get! ctx.spec := by
          clear hagreeD hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
          grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
        refine BlockOperandPtr.matches_frame ctx bo hboib (henc.blockOperands bo hboib heqbo)
          (hagreeD _ _ ?_) hlay hboget boIb
        clear hagreeD hread hread32 hattr ek hoff husz hmul hidxlt
        grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
          Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
          _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
          _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
    · constructor
      · refine OperationPtr.numRegions_frame ctx op hopib henc.numRegions (hagreeD _ _ ?_) (by rw [hget])
        clear hagreeD hread hread32 hattr ek hoff husz hmul hidxlt
        grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
          Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
          _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
          _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
      · intros ridx ridxIn
        dsimp only at ridxIn
        have hnr : ridx < op.getNumRegions! ctx.spec := by
          clear hagreeD hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
          grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
        have hcapr := ctx.sim.repr.operations_indices op hopib |>.capRegions
        refine OperationPtr.nthRegion_frame ctx op hopib ridx hnr (henc.regions ridx hnr)
          (hagreeD _ _ ?_) ?_
          (by clear hagreeD hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
              grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def])
        · clear hagreeD hread hread32 hattr ek hoff husz hmul hidxlt
          grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
        · have hidxc : ridx < (op.get! ctx.spec).capRegions := by
            clear hagreeD hread hread32 hattr ek
            grind
          have haddrR : ((op.toM.toNat : Nat) : Int) = op.id := by
            grind [Veir.OperationPtr.toM, _root_.Veir.OperationPtr.toFlat]
          have hcntr := ctx.sim.repr.operations_indices op hopib |>.regions
          have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op ridx.toUInt64
            (by clear hagreeD hread hread32 hattr ek hoff husz hmul hidxlt
                grind [UInt64.toNat_ofNat']) hopib
          refine hagreeD _ _ ?_
          clear hagreeD hread hread32 hattr ek hoff husz hmul hidxlt
          grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt, UInt64.toNat_ofNat']
    · constructor
      · refine OperationPtr.numOperands_frame ctx op hopib henc.numOperands (hagreeD _ _ ?_) (by rw [hget])
        clear hagreeD hread hread32 hattr ek hoff husz hmul hidxlt
        grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
          Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
          _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
          _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
      · intros oper operIb heqop
        dsimp only at operIb
        have hoperib : oper.InBounds ctx.spec := by
          clear hagreeD hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
          grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
        have hoincl := Veir.Sim.OpOperandPtr.slot_included (ctx := ctx) oper hoperib
        have hoperget : oper.get! (Rewriter.pushBlockArgument ctx.spec blockPtr.spec type (by grind)) = oper.get! ctx.spec := by
          clear hagreeD hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
          grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
        refine OpOperandPtr.matches_frame ctx oper hoperib (henc.operands oper hoperib heqop)
          (hagreeD _ _ ?_) hlay hoperget operIb
        clear hagreeD hread hread32 hattr ek hoff husz hmul hidxlt
        grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
          Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
          _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
          _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
    · constructor
      · refine OperationPtr.numResults_frame ctx op hopib henc.numResults (hagreeD _ _ ?_) (by rw [hget])
        clear hagreeD hread hread32 hattr ek hoff husz hmul hidxlt
        grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
          Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
          _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
          _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
      · intros res resIb heqres
        dsimp only at resIb
        have hresib : res.InBounds ctx.spec := by
          clear hagreeD hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
          grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
        have hrincl := Veir.Sim.OpResultPtr.slot_included (ctx := ctx) res hresib
        have hresget : res.get! (Rewriter.pushBlockArgument ctx.spec blockPtr.spec type (by grind)) = res.get! ctx.spec := by
          clear hagreeD hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
          grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
        refine OpResultPtr.matches_frame ctx res hresib (henc.results res hresib heqres)
          (hagreeD _ _ ?_) hlay hresget resIb
        clear hagreeD hread hread32 hattr ek hoff husz hmul hidxlt
        grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
          Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
          _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
          _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
  · -- encoding_block
    simp only
    intros blk blkIb
    have hblkib : blk.InBounds ctx.spec := by
      clear hagreeD hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
      grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
    have henc := ctx.sim.encoding_block blk hblkib
    have hbrange := Veir.Sim.BlockPtr.range_linear (ctx := ctx) blk hblkib
    have hdisjBB := fun hne : blk ≠ blockPtr.spec =>
      Veir.Sim.disjoint_block_block (ctx := ctx) blk blockPtr.spec hblkib blockPtrInBounds.ib hne
    have hbgets : ((blk.get! (Rewriter.pushBlockArgument ctx.spec blockPtr.spec type (by grind))).firstUse = (blk.get! ctx.spec).firstUse
        ∧ (blk.get! (Rewriter.pushBlockArgument ctx.spec blockPtr.spec type (by grind))).prev = (blk.get! ctx.spec).prev
        ∧ (blk.get! (Rewriter.pushBlockArgument ctx.spec blockPtr.spec type (by grind))).next = (blk.get! ctx.spec).next
        ∧ (blk.get! (Rewriter.pushBlockArgument ctx.spec blockPtr.spec type (by grind))).parent = (blk.get! ctx.spec).parent
        ∧ (blk.get! (Rewriter.pushBlockArgument ctx.spec blockPtr.spec type (by grind))).firstOp = (blk.get! ctx.spec).firstOp
        ∧ (blk.get! (Rewriter.pushBlockArgument ctx.spec blockPtr.spec type (by grind))).lastOp = (blk.get! ctx.spec).lastOp
        ∧ (blk.get! (Rewriter.pushBlockArgument ctx.spec blockPtr.spec type (by grind))).capArguments = (blk.get! ctx.spec).capArguments) := by
      clear hagreeD hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
      grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
    obtain ⟨hgfu, hgprev, hgnext, hgpar, hgfop, hglop, hgcA⟩ := hbgets
    constructor
    · refine BlockPtr.matchesBase_frame ctx blk hblkib henc.toMatchesBase (hagreeD _ _ ?_) hlay
        hgfu hgprev hgnext hgpar hgfop hglop blkIb
      clear hagreeD hread hread32 hattr ek hoff husz hmul hidxlt
      grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
        Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
        _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
        _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
    · constructor
      · refine BlockPtr.numArguments_frame ctx blk hblkib henc.numArguments (hagreeD _ _ ?_) hgcA
        clear hagreeD hread hread32 hattr ek hoff husz hmul hidxlt
        grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
          Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
          _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
          _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
      · intros arg argIn heqarg
        dsimp only at argIn
        by_cases hnewarg : blk = blockPtr.spec ∧ arg.index = idx.toNat
        · -- the freshly pushed argument: reads land on the five writes just made
          obtain ⟨hblkeq, hargidx⟩ := hnewarg
          subst hblkeq
          have hargeq : arg = ⟨blockPtr.spec, idx.toNat⟩ := by
            cases arg
            simp only at heqarg hargidx
            subst heqarg hargidx
            rfl
          have hnget : arg.get! (Rewriter.pushBlockArgument ctx.spec blockPtr.spec type (by grind))
              = { type := type, firstUse := none, index := blockPtr.spec.getNumArguments! ctx.spec,
                  loc := (), owner := blockPtr.spec } := by
            clear hread hread32 hattr ek hagreeD hoff hslotaddr husz hincl hmul hidxlt
            grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
          have hnflat : ((arg.toFlat : Nat) : Int)
              = blockPtr.spec.toFlat + (Buffed.Block.Offsets.argumentsInt + Buffed.BlockArgument.sizeNat * idx.toNat) := by
            rw [BlockArgumentPtr.toFlat_ideal]
            simp only [BlockArgumentPtr.toFlatNat, hargeq,
              show Buffed.Block.Offsets.argumentsInt = 56 from rfl,
              show Buffed.BlockArgument.sizeNat = 40 from rfl]
            have h0 : (0:Int) ≤ blockPtr.spec.toFlat + 56 := by omega
            omega
          have hnMeq : arg.toM = Buffed.BlockMPtr.getArgumentPtr blockPtr.impl idx := by
            simp only [BlockArgumentPtr.toM]
            have h1 : arg.toFlat = (Buffed.BlockMPtr.getArgumentPtr blockPtr.impl idx).toNat := by
              have := hslotaddr
              omega
            rw [h1]
            clear hread hread32 hattr ek hagreeD hoff hslotaddr husz hincl hmul hidxlt
            grind [Nat.toUInt64_eq, UInt64.ofNat_toNat]
          constructor
          · -- kind
            simp only [Buffed.BlockArgumentMPtr.readKind!, hnMeq, Rewriter.setBlockArgumentRaw,
              Buffed.BlockArgumentMPtr.writeOwner, Buffed.BlockArgumentMPtr.writeIndex,
              Buffed.BlockArgumentMPtr.writeFirstUse, Buffed.BlockArgumentMPtr.writeType,
              Buffed.ValueImplMPtr.writeKind]
            rw [ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have h1 := ek Buffed.BlockArgument.Offsets.owner 32 (by decide) (by decide); omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have h1 := ek Buffed.BlockArgument.Offsets.index 24 (by decide) (by decide); omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have h1 := ek Buffed.ValueImpl.Offsets.firstUse 16 (by decide) (by decide); omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have h1 := ek Buffed.ValueImpl.Offsets.type 8 (by decide) (by decide); omega),
              ExArray.read64!_blit64_self]
          · -- type
            simp only [Buffed.BlockArgumentMPtr.readType!, hnMeq, hnget, Rewriter.setBlockArgumentRaw,
              Buffed.BlockArgumentMPtr.writeOwner, Buffed.BlockArgumentMPtr.writeIndex,
              Buffed.BlockArgumentMPtr.writeFirstUse, Buffed.BlockArgumentMPtr.writeType,
              Buffed.ValueImplMPtr.writeKind]
            rw [ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have h1 := ek Buffed.BlockArgument.Offsets.owner 32 (by decide) (by decide); have h2 := ek Buffed.ValueImpl.Offsets.type 8 (by decide) (by decide); omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have h1 := ek Buffed.BlockArgument.Offsets.index 24 (by decide) (by decide); have h2 := ek Buffed.ValueImpl.Offsets.type 8 (by decide) (by decide); omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have h1 := ek Buffed.ValueImpl.Offsets.firstUse 16 (by decide) (by decide); have h2 := ek Buffed.ValueImpl.Offsets.type 8 (by decide) (by decide); omega),
              ExArray.read64!_blit64_self]
            clear hread hread32 ek
            grind
          · -- firstUse
            simp only [Buffed.BlockArgumentMPtr.readFirstUse!, hnMeq, hnget, Rewriter.setBlockArgumentRaw,
              Buffed.BlockArgumentMPtr.writeOwner, Buffed.BlockArgumentMPtr.writeIndex,
              Buffed.BlockArgumentMPtr.writeFirstUse, Buffed.BlockArgumentMPtr.writeType,
              Buffed.ValueImplMPtr.writeKind]
            rw [ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have h1 := ek Buffed.BlockArgument.Offsets.owner 32 (by decide) (by decide); have h2 := ek Buffed.ValueImpl.Offsets.firstUse 16 (by decide) (by decide); omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have h1 := ek Buffed.BlockArgument.Offsets.index 24 (by decide) (by decide); have h2 := ek Buffed.ValueImpl.Offsets.firstUse 16 (by decide) (by decide); omega),
              ExArray.read64!_blit64_self]
            simp only [Sim.OptionOpOperandPtr.Sim_def]
            rfl
          · -- index
            simp only [Buffed.BlockArgumentMPtr.readIndex!, hnMeq, hnget, Rewriter.setBlockArgumentRaw,
              Buffed.BlockArgumentMPtr.writeOwner, Buffed.BlockArgumentMPtr.writeIndex,
              Buffed.BlockArgumentMPtr.writeFirstUse, Buffed.BlockArgumentMPtr.writeType,
              Buffed.ValueImplMPtr.writeKind]
            rw [ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have h1 := ek Buffed.BlockArgument.Offsets.owner 32 (by decide) (by decide); have h2 := ek Buffed.BlockArgument.Offsets.index 24 (by decide) (by decide); omega),
              ExArray.read64!_blit64_self]
            clear hread hread32 ek
            grind
          · -- owner
            simp only [Buffed.BlockArgumentMPtr.readOwner!, hnMeq, hnget, Rewriter.setBlockArgumentRaw,
              Buffed.BlockArgumentMPtr.writeOwner, Buffed.BlockArgumentMPtr.writeIndex,
              Buffed.BlockArgumentMPtr.writeFirstUse, Buffed.BlockArgumentMPtr.writeType,
              Buffed.ValueImplMPtr.writeKind]
            rw [ExArray.read64!_blit64_self]
            simp only [Sim.BlockPtr.Sim_def]
            exact hbM
        · -- pre-existing argument: framed — its slot sits strictly below the written one.
          have hargib : arg.InBounds ctx.spec := by
            clear hagreeD hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
            grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
          have haincl := Veir.Sim.BlockArgumentPtr.slot_included (ctx := ctx) arg hargib
          have hargidx : blk = blockPtr.spec → arg.index < idx.toNat := by
            clear hagreeD hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
            intro hb
            grind [Veir.BlockArgumentPtr.inBounds_def]
          have hargflat : ((arg.toFlatNat : Nat) : Int)
              = blk.toFlat + 56 + ((arg.index * 40 : Nat) : Int) := by
            simp only [BlockArgumentPtr.toFlatNat, heqarg, show Buffed.BlockArgument.sizeNat = 40 from rfl,
              show Buffed.Block.Offsets.argumentsInt = 56 from rfl]
            omega
          have hargget : arg.get! (Rewriter.pushBlockArgument ctx.spec blockPtr.spec type (by grind)) = arg.get! ctx.spec := by
            clear hagreeD hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
            grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
          refine BlockArgumentPtr.matches_frame ctx arg hargib (henc.arguments arg hargib heqarg)
            (hagreeD _ _ ?_) hlay hargget argIn
          clear hagreeD hread hread32 hattr ek hoff husz hmul hidxlt
          grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
  · -- encoding_region: framed — regions are disjoint from `blockPtr`'s allocation.
    simp only
    intros rg rgIb
    have hrgib : rg.InBounds ctx.spec := by
      clear hagreeD hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
      grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
    have henc := ctx.sim.encoding_region rg hrgib
    have hrgrange := Veir.Sim.RegionPtr.range_linear (ctx := ctx) rg hrgib
    have hdisjRB := Veir.Sim.disjoint_region_block (ctx := ctx) rg blockPtr.spec hrgib blockPtrInBounds.ib
    have hrgget : rg.get! (Rewriter.pushBlockArgument ctx.spec blockPtr.spec type (by grind)) = rg.get! ctx.spec := by
      clear hagreeD hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
      grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
    refine RegionPtr.matches_frame ctx rg hrgib henc (hagreeD _ _ ?_) hlay hrgget rgIb
    clear hagreeD hread hread32 hattr ek hoff husz hmul hidxlt
    grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
      Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
      _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
      _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
  · -- attr_empty: the table only gained a new entry, slot 0 is untouched
    (try dsimp only)
    rw [hattr]
    exact hattrget 0 _ ctx.sim.attr_empty

/-- Option-level wrapper of `setBlockArgumentRaw_pushBlockArgument_sim`: destructures the `insertAttrs` success and hands the pieces to the raw theorem. -/
theorem Rewriter.setBlockArgument_pushBlockArgument_sim (blockPtr : Sim.BlockPtr) (ctx : Sim.IRContext OpInfo)
    (idx : UInt64) (type : TypeAttr)
    (blockPtrInBounds : blockPtr.InBounds ctx)
    (hidx : idx.toNat = blockPtr.spec.getNumArguments! ctx.spec)
    (hcap : idx.toNat < (blockPtr.spec.get! ctx.spec).capArguments)
    (hslot : (Buffed.BlockMPtr.getArgumentPtr blockPtr.impl idx).toNat + Buffed.BlockArgument.size.toNat ≤ ctx.buf.size)
    {newBuf : Buffed.IRBufContext OpInfo}
    (heq : Rewriter.setBlockArgument blockPtr.impl ctx.buf idx hslot type = some newBuf) :
    Veir.Sim (OpInfo := OpInfo)
      ⟨newBuf, Rewriter.pushBlockArgument ctx.spec blockPtr.spec type (by grind)⟩ := by
  rw [Rewriter.setBlockArgument] at heq
  split at heq
  · exact absurd heq (by simp)
  · rename_i buf₁ typeIdx hattr
    simp only [Option.some.injEq] at heq
    subst heq
    have hmem : buf₁.mem = ctx.buf.mem := by
      simp only [Buffed.IRBufContext.insertAttrs] at hattr
      split at hattr <;> grind
    have hattrs : buf₁.attributes = ctx.buf.attributes.push type := by
      simp only [Buffed.IRBufContext.insertAttrs] at hattr
      split at hattr <;> grind
    have htidx : typeIdx.toNat = ctx.buf.attributes.size := by
      simp only [Buffed.IRBufContext.insertAttrs] at hattr
      split at hattr <;> grind [Nat.toUInt64_eq, UInt64.toNat_ofNat']
    exact Rewriter.setBlockArgumentRaw_pushBlockArgument_sim blockPtr ctx idx type
      blockPtrInBounds hidx hcap buf₁ typeIdx hmem hattrs htidx _

end Veir
