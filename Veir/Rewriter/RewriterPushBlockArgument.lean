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

/-! # Block-argument push simulation proofs

The raw block-argument slot setter, its spec-level counterpart, and the (large) proof that
the `Sim` relation survives them. Split out of `Veir.Rewriter.Basic` to keep that file
readable, mirroring `Veir.Rewriter.RewriterPushOperand`. -/

public section
namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo] [SerializableOpInfo OpInfo]
variable {ctx : Sim.IRContext OpInfo}

/-- Unfolding equation for `BlockPtr.pushArgument`, phrased at the `setArguments` level where
the `GetSet` transport lemmas live. `grind` cannot derive a usable pattern from the def itself
(its in-bounds arguments are autoparams), so the simulation proof passes this instead. -/
private theorem BlockPtr.pushArgument_def {ctx : IRContext OpInfo} (block : BlockPtr) (result : BlockArgument)
    (h : block.InBounds ctx) :
    block.pushArgument ctx result h
      = block.setArguments ctx ((block.get ctx h).arguments.push result) h := rfl

-- TODO: for now `pushBlockArgument` only works in the specification world,
-- because the buffed implementation does not handle changing the size of the
-- argument array.
protected def Rewriter.pushBlockArgument (ctx : IRContext OpInfo) (blockPtr : BlockPtr) (type : TypeAttr)
    (blockPtrInBounds : blockPtr.InBounds ctx := by grind) : IRContext OpInfo :=
  let index := blockPtr.getNumArguments ctx (by grind)
  let argument := { type := type, firstUse := none, index := index, loc := (), owner := blockPtr : BlockArgument }
  blockPtr.pushArgument ctx argument (by grind)

/-- The five 8-byte field writes into the (pre-allocated) argument slot `idx` of `blockPtr`.
Factored out of `Rewriter.setBlockArgument` so that the simulation proof can refer to the
written buffer by a compact name. -/
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
/-- The `Sim` relation survives writing a fresh block argument into slot `idx` of `blockPtr`'s
(pre-allocated) argument array while the spec pushes the corresponding `BlockArgument`.
`buf₁` is the attribute-extended buffer produced by `insertAttrs` (same memory, one more
attribute) and `typeIdx` the index of the freshly inserted `type`. -/
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
    simp only [Sim.BlockPtr.Sim, BlockPtr.toM] at this
    grind [BlockPtr.toFlat, BlockPtr.range]
  have hbM : blockPtr.spec.toM = blockPtr.impl := blockPtrInBounds.sim
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
  -- Read-preservation bridges over the five slot writes: any 8-/4-byte read disjoint from the
  -- written slot `[arg, arg+40)` is unchanged.
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
  -- The slot writes only touch `mem`; the attribute table is the pushed one.
  have hattr : (Rewriter.setBlockArgumentRaw blockPtr.impl buf₁ idx typeIdx hslot').attributes
      = ctx.buf.attributes.push type := by
    simp only [Rewriter.setBlockArgumentRaw, Buffed.BlockArgumentMPtr.writeOwner,
      Buffed.BlockArgumentMPtr.writeIndex, Buffed.BlockArgumentMPtr.writeFirstUse,
      Buffed.BlockArgumentMPtr.writeType, Buffed.ValueImplMPtr.writeKind, hattrs]
  -- Pushing an attribute preserves every existing table lookup.
  have hattrget : ∀ (i : Nat) (t : Attribute), ctx.buf.attributes[i]? = some t →
      (ctx.buf.attributes.push type)[i]? = some t := by
    grind
  constructor
  · -- fieldsInBounds
    have hafib : BlockArgument.FieldsInBounds
        { type := type, firstUse := none, index := blockPtr.spec.getNumArguments! ctx.spec,
          loc := (), owner := blockPtr.spec } ctx.spec := by
      constructor <;> grind
    grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
  · -- repr
    clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
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
    clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
    have := ctx.sim.in_bounds gptr (by grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def])
    grind [TopLevelPtr, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def, layout_grind]
  · -- disjoint_allocs
    simp only
    clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
    have := ctx.sim.disjoint_allocs
    grind [TopLevelPtr, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
  · -- encoding_op: every operation's range is disjoint from `blockPtr`'s range, which
    -- contains the written slot, so all its reads are preserved.
    simp only
    intros op opIb
    have hopib : op.InBounds ctx.spec := by
      clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
      grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
    have hoin := ctx.sim.in_bounds (.operation op) (by grind)
    have henc := ctx.sim.encoding_op op (by grind)
    have hd := ctx.sim.disjoint_allocs (.operation op) (.block blockPtr.spec) (by grind) (by grind) (by simp)
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
    have hopM : (UInt64.toNat op.toM : Int) = op.toFlat := by
      simp only [OperationPtr.toM]
      grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', OperationPtr.toFlat, layout_grind]
    -- any read inside the op's byte range is disjoint from the freshly written argument slot
    have hro8 : ∀ (off : Int64) (n : Nat), off.toInt = n → n + 8 ≤ 72 →
        (Rewriter.setBlockArgumentRaw blockPtr.impl buf₁ idx typeIdx hslot').mem.read64! (op.toM + off) = ctx.buf.mem.read64! (op.toM + off) := by
      intro off n hn h72
      apply hread
      have hri1 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr hopib
      have hri2 := BlockPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr blockPtrInBounds.ib
      simp only [TopLevelPtr.range, hri1, hri2, IsDisjointI, OperationPtr.rangeInt,
        Buffed.Operation.rangeInt, BlockPtr.rangeInt, Buffed.Block.rangeInt, add_nat_range_def] at hd
      rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind]
    have hro4 : ∀ (off : Int64) (n : Nat), off.toInt = n → n + 4 ≤ 72 →
        (Rewriter.setBlockArgumentRaw blockPtr.impl buf₁ idx typeIdx hslot').mem.read32! (op.toM + off) = ctx.buf.mem.read32! (op.toM + off) := by
      intro off n hn h72
      apply hread32
      have hri1 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr hopib
      have hri2 := BlockPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr blockPtrInBounds.ib
      simp only [TopLevelPtr.range, hri1, hri2, IsDisjointI, OperationPtr.rangeInt,
        Buffed.Operation.rangeInt, BlockPtr.rangeInt, Buffed.Block.rangeInt, add_nat_range_def] at hd
      rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind]
    constructor
    · constructor
      · have := henc.prev
        simp only [Buffed.OperationMPtr.readPrev!] at this ⊢
        rw [hro8 Buffed.Operation.Offsets.prev 8 (by decide) (by decide)]
        grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
      · have := henc.next
        simp only [Buffed.OperationMPtr.readNext!] at this ⊢
        rw [hro8 Buffed.Operation.Offsets.next 16 (by decide) (by decide)]
        grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
      · have := henc.parent
        simp only [Buffed.OperationMPtr.readParent!] at this ⊢
        rw [hro8 Buffed.Operation.Offsets.parent 24 (by decide) (by decide)]
        grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
      · have := henc.opType
        simp only [Buffed.OperationMPtr.readOpType!] at this ⊢
        rw [hro4 Buffed.Operation.Offsets.opType 32 (by decide) (by decide)]
        grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
      · have := henc.attrs
        simp only [Buffed.OperationMPtr.readAttrs!, hattr] at this ⊢
        rw [hro8 Buffed.Operation.Offsets.attrs 64 (by decide) (by decide)]
        have := hattrget _ _ this
        grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
    · constructor
      · have := henc.numBlockOperands
        simp only [Buffed.OperationMPtr.readNumBlockOperands!] at this ⊢
        rw [hro8 Buffed.Operation.Offsets.numBlockOperands 40 (by decide) (by decide)]
        grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
      · intros bo boIb heqbo
        dsimp only at boIb
        have hboib : bo.InBounds ctx.spec := by
          clear hread hread32 hattr ek hro8 hro4 hoff hslotaddr husz hincl hmul hidxlt
          grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
        have := henc.blockOperands bo (by grind) (by grind)
        have hbomeq : bo.toM (Rewriter.pushBlockArgument ctx.spec blockPtr.spec type (by grind)) = bo.toM ctx.spec := by
          clear hread hread32 hattr ek hro8 hro4 hoff hslotaddr husz hincl hmul hidxlt
          simp only [BlockOperandPtr.toM, BlockOperandPtr.toFlat]
          grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
        have hboget : bo.get! (Rewriter.pushBlockArgument ctx.spec blockPtr.spec type (by grind)) = bo.get! ctx.spec := by
          clear hread hread32 hattr ek hro8 hro4 hoff hslotaddr husz hincl hmul hidxlt
          grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
        have hboaft := Sim.BlockOperandPtr.after_lt_ctx (ctx := ctx) bo hboib
        have hboM : (UInt64.toNat (bo.toM ctx.spec) : Int) = bo.toFlat ctx.spec := by
          simp only [BlockOperandPtr.toM]
          grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', BlockOperandPtr.toFlat]
        have hboidx : bo.index < (op.get! ctx.spec).capBlockOperands := by
          clear hread hread32 hattr ek hro8 hro4 hoff hslotaddr husz hincl hmul hidxlt
          grind [Veir.BlockOperandPtr.inBounds_def]
        have hboflat : ((bo.toFlat ctx.spec : Nat) : Int) = op.toFlat + Buffed.Operation.Offsets.blockOperandsInt op ctx.spec + ((bo.index * 32 : Nat) : Int) := by
          rw [BlockOperandPtr.toFlat_ideal ctx.sim.repr bo hboib]
          simp only [BlockOperandPtr.toFlatNat, heqbo, show Buffed.BlockOperand.sizeNat = 32 from rfl]
          have h0 : (0:Int) ≤ op.toFlat + Buffed.Operation.Offsets.blockOperandsInt op ctx.spec := by
            rw [hareaBO, hareaOP]
            omega
          omega
        have hbo : ∀ (off : Int64) (n : Nat), off.toInt = n → n + 8 ≤ 32 →
            (Rewriter.setBlockArgumentRaw blockPtr.impl buf₁ idx typeIdx hslot').mem.read64! (bo.toM ctx.spec + off) = ctx.buf.mem.read64! (bo.toM ctx.spec + off) := by
          intro off n hn h32
          apply hread
          have hri1 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr hopib
          have hri2 := BlockPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr blockPtrInBounds.ib
          simp only [TopLevelPtr.range, hri1, hri2, IsDisjointI, OperationPtr.rangeInt,
            Buffed.Operation.rangeInt, BlockPtr.rangeInt, Buffed.Block.rangeInt, add_nat_range_def] at hd
          rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind]
        constructor
        · have := this.nextUse
          simp only [Buffed.BlockOperandMPtr.readNextUse!, hbomeq, hboget] at this ⊢
          rw [hbo Buffed.BlockOperand.Offsets.nextUse 0 (by decide) (by decide)]
          clear hread hread32 hattr ek hro8 hro4 hoff hslotaddr husz hincl hmul hidxlt
          grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
        · have := this.back
          simp only [Buffed.BlockOperandMPtr.readBack!, hbomeq, hboget] at this ⊢
          rw [hbo Buffed.BlockOperand.Offsets.back 8 (by decide) (by decide)]
          clear hread hread32 hattr ek hro8 hro4 hoff hslotaddr husz hincl hmul hidxlt
          grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
        · have := this.owner
          simp only [Buffed.BlockOperandMPtr.readOwner!, hbomeq, hboget] at this ⊢
          rw [hbo Buffed.BlockOperand.Offsets.owner 16 (by decide) (by decide)]
          clear hread hread32 hattr ek hro8 hro4 hoff hslotaddr husz hincl hmul hidxlt
          grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
        · have := this.value
          simp only [Buffed.BlockOperandMPtr.readValue!, hbomeq, hboget] at this ⊢
          rw [hbo Buffed.BlockOperand.Offsets.value 24 (by decide) (by decide)]
          clear hread hread32 hattr ek hro8 hro4 hoff hslotaddr husz hincl hmul hidxlt
          grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
    · constructor
      · have := henc.numRegions
        simp only [Buffed.OperationMPtr.readNumRegions!] at this ⊢
        rw [hro8 Buffed.Operation.Offsets.numRegions 48 (by decide) (by decide)]
        grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
      · intros ridx ridxIn
        dsimp only at ridxIn
        have hridxOld : ridx < op.getNumRegions! ctx.spec := by
          clear hread hread32 hattr ek hro8 hro4 hoff hslotaddr husz hincl hmul hidxlt
          grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
        have := henc.regions ridx (by
          clear hread hread32 hattr ek hro8 hro4 hoff hslotaddr husz hincl hmul hidxlt
          grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def])
        have hcapr := ctx.sim.repr.operations_indices op (by grind) |>.capRegions
        have hcro : Buffed.OperationMPtr.computeRegionsOffset! (Rewriter.setBlockArgumentRaw blockPtr.impl buf₁ idx typeIdx hslot') op.toM
            = Buffed.OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
          simp only [Buffed.OperationMPtr.computeRegionsOffset!, Buffed.OperationMPtr.computeBlockOperandsOffset!,
            Buffed.OperationMPtr.computeOperandsOffset!, Buffed.OperationMPtr.readNumBlockOperands!,
            Buffed.OperationMPtr.readNumOperands!, Buffed.OperationMPtr.readOpType!]
          rw [hro8 Buffed.Operation.Offsets.numBlockOperands 40 (by decide) (by decide),
            hro8 Buffed.Operation.Offsets.numOperands 56 (by decide) (by decide),
            hro4 Buffed.Operation.Offsets.opType 32 (by decide) (by decide)]
        have hcri := Veir.OperationPtr.computeRegionsOffset!_ideal ctx ⟨op.toM, op⟩ (by grind) (by grind) (by
          clear hread hread32 hattr ek hro8 hro4 hoff hslotaddr husz hincl hmul hidxlt
          have h5 : op.toFlat = op.id := rfl
          have h6 : Buffed.Operation.sizeBaseNat = 72 := rfl
          simp only [Buffed.IRBufContext.size_def]
          omega)
        have hnth : Buffed.OperationMPtr.readNthRegion! (Rewriter.setBlockArgumentRaw blockPtr.impl buf₁ idx typeIdx hslot') op.toM ridx.toUInt64
            = Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM ridx.toUInt64 := by
          simp only [Buffed.OperationMPtr.readNthRegion!, Buffed.OperationMPtr.computeRegionOffset!, hcro]
          apply hread
          have hri1 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr hopib
          have hri2 := BlockPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr blockPtrInBounds.ib
          simp only [TopLevelPtr.range, hri1, hri2, IsDisjointI, OperationPtr.rangeInt,
            Buffed.Operation.rangeInt, BlockPtr.rangeInt, Buffed.Block.rangeInt, add_nat_range_def] at hd
          rw [UInt64.uint64_add_int64_toNat_lt] <;>
            grind [layout_grind, UInt64.toNat_mul]
        rw [Sim.RegionPtr.Sim] at this ⊢
        simp only [hnth]
        clear hread hread32 hattr ek hro8 hro4 hcro hnth
        grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
    · constructor
      · have := henc.numOperands
        simp only [Buffed.OperationMPtr.readNumOperands!] at this ⊢
        rw [hro8 Buffed.Operation.Offsets.numOperands 56 (by decide) (by decide)]
        grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
      · intros oper operIb heqop
        dsimp only at operIb
        have hoperib : oper.InBounds ctx.spec := by
          clear hread hread32 hattr ek hro8 hro4 hoff hslotaddr husz hincl hmul hidxlt
          grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
        have := henc.operands oper (by grind) (by grind)
        have hopermeq : oper.toM (Rewriter.pushBlockArgument ctx.spec blockPtr.spec type (by grind)) = oper.toM ctx.spec := by
          clear hread hread32 hattr ek hro8 hro4 hoff hslotaddr husz hincl hmul hidxlt
          simp only [OpOperandPtr.toM, OpOperandPtr.toFlat]
          grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
        have hoperget : oper.get! (Rewriter.pushBlockArgument ctx.spec blockPtr.spec type (by grind)) = oper.get! ctx.spec := by
          clear hread hread32 hattr ek hro8 hro4 hoff hslotaddr husz hincl hmul hidxlt
          grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
        have hoperaft := Sim.OpOperandPtr.after_lt_ctx (ctx := ctx) oper hoperib
        have hoperM : (UInt64.toNat (oper.toM ctx.spec) : Int) = oper.toFlat ctx.spec := by
          simp only [OpOperandPtr.toM]
          grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', OpOperandPtr.toFlat]
        have hoperidx : oper.index < (op.get! ctx.spec).capOperands := by
          clear hread hread32 hattr ek hro8 hro4 hoff hslotaddr husz hincl hmul hidxlt
          grind [Veir.OpOperandPtr.inBounds_def]
        have hoperflat : ((oper.toFlat ctx.spec : Nat) : Int) = op.toFlat + Buffed.Operation.Offsets.operandsInt op ctx.spec + ((oper.index * 32 : Nat) : Int) := by
          rw [OpOperandPtr.toFlat_ideal ctx.sim.repr oper hoperib]
          simp only [OpOperandPtr.toFlatNat, heqop, show Buffed.OpOperand.sizeNat = 32 from rfl]
          have h0 : (0:Int) ≤ op.toFlat + Buffed.Operation.Offsets.operandsInt op ctx.spec := by
            rw [hareaOP]
            omega
          omega
        have hop : ∀ (off : Int64) (n : Nat), off.toInt = n → n + 8 ≤ 32 →
            (Rewriter.setBlockArgumentRaw blockPtr.impl buf₁ idx typeIdx hslot').mem.read64! (oper.toM ctx.spec + off) = ctx.buf.mem.read64! (oper.toM ctx.spec + off) := by
          intro off n hn h32
          apply hread
          have hri1 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr hopib
          have hri2 := BlockPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr blockPtrInBounds.ib
          simp only [TopLevelPtr.range, hri1, hri2, IsDisjointI, OperationPtr.rangeInt,
            Buffed.Operation.rangeInt, BlockPtr.rangeInt, Buffed.Block.rangeInt, add_nat_range_def] at hd
          rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind, Veir.OpOperandPtr.inBounds_def]
        constructor
        · have := this.nextUse
          simp only [Buffed.OpOperandMPtr.readNextUse!, hopermeq, hoperget] at this ⊢
          rw [hop Buffed.OpOperand.Offsets.nextUse 0 (by decide) (by decide)]
          clear hread hread32 hattr ek hro8 hro4 hoff hslotaddr husz hincl hmul hidxlt
          grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
        · have := this.back
          simp only [Buffed.OpOperandMPtr.readBack!, hopermeq, hoperget] at this ⊢
          rw [hop Buffed.OpOperand.Offsets.back 8 (by decide) (by decide)]
          clear hread hread32 hattr ek hro8 hro4 hoff hslotaddr husz hincl hmul hidxlt
          grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
        · have := this.owner
          simp only [Buffed.OpOperandMPtr.readOwner!, hopermeq, hoperget] at this ⊢
          rw [hop Buffed.OpOperand.Offsets.owner 16 (by decide) (by decide)]
          clear hread hread32 hattr ek hro8 hro4 hoff hslotaddr husz hincl hmul hidxlt
          grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
        · have := this.value
          simp only [Buffed.OpOperandMPtr.readValue!, hopermeq, hoperget] at this ⊢
          rw [hop Buffed.OpOperand.Offsets.value 24 (by decide) (by decide)]
          clear hread hread32 hattr ek hro8 hro4 hoff hslotaddr husz hincl hmul hidxlt
          grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
    · constructor
      · have := henc.numResults
        simp only [Buffed.OperationMPtr.readNumResults!] at this ⊢
        rw [hro8 Buffed.Operation.Offsets.numResults 0 (by decide) (by decide)]
        grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
      · intros res resIb heqres
        dsimp only at resIb
        have hresib : res.InBounds ctx.spec := by
          clear hread hread32 hattr ek hro8 hro4 hoff hslotaddr husz hincl hmul hidxlt
          grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
        have := henc.results res (by grind) (by grind)
        have hresmeq : res.toM (Rewriter.pushBlockArgument ctx.spec blockPtr.spec type (by grind)) = res.toM ctx.spec := by
          clear hread hread32 hattr ek hro8 hro4 hoff hslotaddr husz hincl hmul hidxlt
          simp only [OpResultPtr.toM, OpResultPtr.toFlat]
          grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
        have hresget : res.get! (Rewriter.pushBlockArgument ctx.spec blockPtr.spec type (by grind)) = res.get! ctx.spec := by
          clear hread hread32 hattr ek hro8 hro4 hoff hslotaddr husz hincl hmul hidxlt
          grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
        have hresaft := Sim.OpResultPtr.after_lt_ctx (ctx := ctx) res hresib
        have hresM : (UInt64.toNat (res.toM ctx.spec) : Int) = res.toFlat ctx.spec := by
          simp only [OpResultPtr.toM]
          grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', OpResultPtr.toFlat]
        have hresidx : res.index < (op.get! ctx.spec).capResults := by
          clear hread hread32 hattr ek hro8 hro4 hoff hslotaddr husz hincl hmul hidxlt
          grind [Veir.OpResultPtr.inBounds_def]
        have hoplow : (0:Int) ≤ op.toFlat + Buffed.Operation.Offsets.resultsInt op ctx.spec := by
          have hio := hoin
          have hr := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr hopib
          simp only [TopLevelPtr.range, hr, OperationPtr.rangeInt, Buffed.Operation.rangeInt,
            add_nat_range_def, IsIncludedIN] at hio
          grind [ExArray.range_lower, ExArray.range_upper]
        have hresflat : ((res.toFlat ctx.spec : Nat) : Int) = op.toFlat + Buffed.Operation.Offsets.resultsInt op ctx.spec + ((res.index * 40 : Nat) : Int) := by
          rw [OpResultPtr.toFlat_ideal ctx.sim.repr res hresib]
          simp only [OpResultPtr.toFlatNat, heqres, show Buffed.OpResult.sizeNat = 40 from rfl]
          omega
        have hres : ∀ (off : Int64) (n : Nat), off.toInt = n → n + 8 ≤ 40 →
            (Rewriter.setBlockArgumentRaw blockPtr.impl buf₁ idx typeIdx hslot').mem.read64! (res.toM ctx.spec + off) = ctx.buf.mem.read64! (res.toM ctx.spec + off) := by
          intro off n hn h32
          apply hread
          have hri1 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr hopib
          have hri2 := BlockPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr blockPtrInBounds.ib
          simp only [TopLevelPtr.range, hri1, hri2, IsDisjointI, OperationPtr.rangeInt,
            Buffed.Operation.rangeInt, BlockPtr.rangeInt, Buffed.Block.rangeInt, add_nat_range_def] at hd
          rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind]
        have hres0 : (Rewriter.setBlockArgumentRaw blockPtr.impl buf₁ idx typeIdx hslot').mem.read64! (res.toM ctx.spec) = ctx.buf.mem.read64! (res.toM ctx.spec) := by
          apply hread
          have hri1 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr hopib
          have hri2 := BlockPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr blockPtrInBounds.ib
          simp only [TopLevelPtr.range, hri1, hri2, IsDisjointI, OperationPtr.rangeInt,
            Buffed.Operation.rangeInt, BlockPtr.rangeInt, Buffed.Block.rangeInt, add_nat_range_def] at hd
          grind [layout_grind]
        constructor
        · have := this.kind
          simp only [Buffed.OpResultMPtr.readKind!, hresmeq, hresget] at this ⊢
          rw [hres0]
          clear hread hread32 hattr ek hro8 hro4 hoff hslotaddr husz hincl hmul hidxlt
          grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
        · have := this.typee
          simp only [Buffed.OpResultMPtr.readType!, hattr, hresmeq] at this ⊢
          rw [hres Buffed.ValueImpl.Offsets.type 8 (by decide) (by decide)]
          have := hattrget _ _ this
          clear hread hread32 hattr ek hro8 hro4 hoff hslotaddr husz hincl hmul hidxlt
          grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
        · have := this.firstUse
          simp only [Buffed.OpResultMPtr.readFirstUse!, hresmeq, hresget] at this ⊢
          rw [hres Buffed.ValueImpl.Offsets.firstUse 16 (by decide) (by decide)]
          clear hread hread32 hattr ek hro8 hro4 hoff hslotaddr husz hincl hmul hidxlt
          grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
        · have := this.index
          simp only [Buffed.OpResultMPtr.readIndex!, hresmeq, hresget] at this ⊢
          rw [hres Buffed.OpResult.Offsets.index 24 (by decide) (by decide)]
          clear hread hread32 hattr ek hro8 hro4 hoff hslotaddr husz hincl hmul hidxlt
          grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
        · have := this.owner
          simp only [Buffed.OpResultMPtr.readOwner!, hresmeq, hresget] at this ⊢
          rw [hres Buffed.OpResult.Offsets.owner 32 (by decide) (by decide)]
          clear hread hread32 hattr ek hro8 hro4 hoff hslotaddr husz hincl hmul hidxlt
          grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
  · -- encoding_block
    simp only
    intros blk blkIb
    have hblkib : blk.InBounds ctx.spec := by
      clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
      grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
    have hbin := ctx.sim.in_bounds (.block blk) (by grind)
    have henc := ctx.sim.encoding_block blk (by grind)
    have hbri := ctx.sim.repr.blocks_indices blk (by grind)
    have hareaBLK : Buffed.Block.Offsets.afterInt blk ctx.spec
        = 56 + (((blk.get! ctx.spec).capArguments * 40 : Nat) : Int) := by rfl
    have hblkM : (UInt64.toNat blk.toM : Int) = blk.toFlat := by
      simp only [BlockPtr.toM]
      grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', BlockPtr.toFlat, layout_grind]
    have haft := Sim.BlockPtr.after_lt_ctx (ctx := ctx) blk hblkib
    -- Any 8-byte read strictly inside `blk`'s range but outside the written slot is unchanged:
    -- for `blk ≠ blockPtr.spec` by allocation disjointness, for `blk = blockPtr.spec` because
    -- the header (< 56) and the other argument slots are disjoint from slot `idx`.
    have hb8 : ∀ (off : Int64) (n : Nat), off.toInt = n → (n : Int) + 8 ≤ 56 →
        (Rewriter.setBlockArgumentRaw blockPtr.impl buf₁ idx typeIdx hslot').mem.read64! (blk.toM + off) = ctx.buf.mem.read64! (blk.toM + off) := by
      intro off n hn hbnd
      apply hread
      by_cases hcase : blk = blockPtr.spec
      · subst hcase
        rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind]
      · have hdd := ctx.sim.disjoint_allocs (.block blk) (.block blockPtr.spec) (by grind) (by grind) (by simp [hcase])
        have hri1 := BlockPtr.range_ideal ctx.sim.repr hblkib
        have hri2 := BlockPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr blockPtrInBounds.ib
        simp only [TopLevelPtr.range, hri1, hri2, IsDisjointI, BlockPtr.rangeInt, Buffed.Block.rangeInt,
          add_nat_range_def] at hdd
        rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind]
    constructor
    · constructor
      · have := henc.firstUse
        simp only [Buffed.BlockMPtr.readFirstUse!] at this ⊢
        rw [hb8 Buffed.Block.Offsets.firstUse 0 (by decide) (by decide)]
        clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
        grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
      · have := henc.prev
        simp only [Buffed.BlockMPtr.readPrev!] at this ⊢
        rw [hb8 Buffed.Block.Offsets.prev 8 (by decide) (by decide)]
        clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
        grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
      · have := henc.next
        simp only [Buffed.BlockMPtr.readNext!] at this ⊢
        rw [hb8 Buffed.Block.Offsets.next 16 (by decide) (by decide)]
        clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
        grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
      · have := henc.parent
        simp only [Buffed.BlockMPtr.readParent!] at this ⊢
        rw [hb8 Buffed.Block.Offsets.parent 24 (by decide) (by decide)]
        clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
        grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
      · have := henc.firstOp
        simp only [Buffed.BlockMPtr.readFirstOp!] at this ⊢
        rw [hb8 Buffed.Block.Offsets.firstOp 32 (by decide) (by decide)]
        clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
        grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
      · have := henc.lastOp
        simp only [Buffed.BlockMPtr.readLastOp!] at this ⊢
        rw [hb8 Buffed.Block.Offsets.lastOp 40 (by decide) (by decide)]
        clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
        grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
    · constructor
      · have := henc.numArguments
        simp only [Buffed.BlockMPtr.readNumArguments!] at this ⊢
        rw [hb8 Buffed.Block.Offsets.numArguments 48 (by decide) (by decide)]
        clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
        grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
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
            clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
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
            clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
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
            simp only [Buffed.BlockArgumentMPtr.readType!, hnMeq, hnget, hattr, Rewriter.setBlockArgumentRaw,
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
            simp only [Sim.OptionOpOperandPtr.Sim]
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
            simp only [Sim.BlockPtr.Sim]
            exact hbM
        · -- pre-existing argument: reads are disjoint from the written slot
          have hargib : arg.InBounds ctx.spec := by
            clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
            grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def,
              Veir.BlockArgumentPtr.inBounds_def]
          have := henc.arguments arg (by grind) (by grind)
          have hargget : arg.get! (Rewriter.pushBlockArgument ctx.spec blockPtr.spec type (by grind)) = arg.get! ctx.spec := by
            clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
            grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def,
              Veir.BlockArgumentPtr.inBounds_def, Veir.BlockArgumentPtr.get!,
              Veir.BlockPtr.getNumArguments!, Array.getElem_push]
          have hargidx : arg.index < (blk.get! ctx.spec).capArguments := by
            clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
            grind [Veir.BlockArgumentPtr.inBounds_def]
          have hargaft := Sim.BlockArgumentPtr.after_lt_ctx (ctx := ctx) arg hargib
          have hargM : (UInt64.toNat arg.toM : Int) = arg.toFlat := by
            simp only [BlockArgumentPtr.toM]
            grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', BlockArgumentPtr.toFlat]
          have hargflat : ((arg.toFlat : Nat) : Int) = blk.toFlat + 56 + ((arg.index * 40 : Nat) : Int) := by
            rw [BlockArgumentPtr.toFlat_ideal]
            simp only [BlockArgumentPtr.toFlatNat, heqarg, show Buffed.BlockArgument.sizeNat = 40 from rfl,
              show Buffed.Block.Offsets.argumentsInt = 56 from rfl]
            omega
          have harg : ∀ (off : Int64) (n : Nat), off.toInt = n → n + 8 ≤ 40 →
              (Rewriter.setBlockArgumentRaw blockPtr.impl buf₁ idx typeIdx hslot').mem.read64! (arg.toM + off) = ctx.buf.mem.read64! (arg.toM + off) := by
            intro off n hn h40
            apply hread
            by_cases hcase : blk = blockPtr.spec
            · subst hcase
              have hne : arg.index ≠ idx.toNat := by grind
              rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind]
            · have hdd := ctx.sim.disjoint_allocs (.block blk) (.block blockPtr.spec) (by grind) (by grind) (by simp [hcase])
              have hri1 := BlockPtr.range_ideal ctx.sim.repr hblkib
              have hri2 := BlockPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr blockPtrInBounds.ib
              simp only [TopLevelPtr.range, hri1, hri2, IsDisjointI, BlockPtr.rangeInt, Buffed.Block.rangeInt,
                add_nat_range_def] at hdd
              rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind]
          have harg0 : (Rewriter.setBlockArgumentRaw blockPtr.impl buf₁ idx typeIdx hslot').mem.read64! arg.toM = ctx.buf.mem.read64! arg.toM := by
            have := harg 0 0 (by decide) (by decide)
            simpa using this
          constructor
          · have := this.kind
            simp only [Buffed.BlockArgumentMPtr.readKind!] at this ⊢
            rw [harg0]
            clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
            grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
          · have := this.type
            simp only [Buffed.BlockArgumentMPtr.readType!, hattr, hargget] at this ⊢
            rw [harg Buffed.ValueImpl.Offsets.type 8 (by decide) (by decide)]
            have := hattrget _ _ this
            clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
            grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
          · have := this.firstUse
            simp only [Buffed.BlockArgumentMPtr.readFirstUse!, hargget] at this ⊢
            rw [harg Buffed.ValueImpl.Offsets.firstUse 16 (by decide) (by decide)]
            clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
            grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
          · have := this.index
            simp only [Buffed.BlockArgumentMPtr.readIndex!, hargget] at this ⊢
            rw [harg Buffed.BlockArgument.Offsets.index 24 (by decide) (by decide)]
            clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
            grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
          · have := this.owner
            simp only [Buffed.BlockArgumentMPtr.readOwner!, hargget] at this ⊢
            rw [harg Buffed.BlockArgument.Offsets.owner 32 (by decide) (by decide)]
            clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
            grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
  · -- encoding_region
    simp only
    intros rg rgIb
    have hrgib : rg.InBounds ctx.spec := by
      clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
      grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
    have hrin := ctx.sim.in_bounds (.region rg) (by grind)
    have henc := ctx.sim.encoding_region rg (by grind)
    have hdd := ctx.sim.disjoint_allocs (.region rg) (.block blockPtr.spec) (by grind) (by grind) (by simp)
    have hrgM : (UInt64.toNat rg.toM : Int) = rg.toFlat := by
      simp only [RegionPtr.toM]
      grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', RegionPtr.toFlat, layout_grind]
    have hrgget : rg.get! (Rewriter.pushBlockArgument ctx.spec blockPtr.spec type (by grind)) = rg.get! ctx.spec := by
      clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
      grind [Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
    have hrg8 : ∀ (off : Int64) (n : Nat), off.toInt = n → n + 8 ≤ 24 →
        (Rewriter.setBlockArgumentRaw blockPtr.impl buf₁ idx typeIdx hslot').mem.read64! (rg.toM + off) = ctx.buf.mem.read64! (rg.toM + off) := by
      intro off n hn h24
      apply hread
      have hri2 := BlockPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr blockPtrInBounds.ib
      simp only [TopLevelPtr.range, RegionPtr.range_ideal, hri2, IsDisjointI, RegionPtr.rangeInt,
        Buffed.Region.rangeInt, BlockPtr.rangeInt, Buffed.Block.rangeInt, add_nat_range_def] at hdd
      rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind]
    constructor
    · have := henc.firstBlock
      simp only [Buffed.RegionMPtr.readFirstBlock!, hrgget] at this ⊢
      rw [hrg8 Buffed.Region.Offsets.firstBlock 0 (by decide) (by decide)]
      clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
      grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
    · have := henc.lastBlock
      simp only [Buffed.RegionMPtr.readLastBlock!, hrgget] at this ⊢
      rw [hrg8 Buffed.Region.Offsets.lastBlock 8 (by decide) (by decide)]
      clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
      grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]
    · have := henc.parent
      simp only [Buffed.RegionMPtr.readParent!, hrgget] at this ⊢
      rw [hrg8 Buffed.Region.Offsets.parent 16 (by decide) (by decide)]
      clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
      grind [layout_grind, Rewriter.pushBlockArgument, Veir.BlockPtr.pushArgument_def]

/-- Option-level wrapper of `setBlockArgumentRaw_pushBlockArgument_sim`: destructures the
`insertAttrs` success and hands the pieces to the raw theorem. Discharges the `admitted_sim`
in `Rewriter.pushBlockArgumentAtSim`. -/
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
