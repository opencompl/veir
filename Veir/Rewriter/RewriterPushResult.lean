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
import all Veir.Rewriter.LinkedList.Basic
import all Veir.IR.Buffed.Basic
import all Veir.IR.Buffed.RawAccessors
import all Veir.IR.Buffed.SimDefs

set_option linter.unusedSectionVars false

/-! Rewriter simulation proofs: result push -/

public section
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
    grind [Buffed.IRBufContext.insertAttrs]
  have hattr1 : ctx1.attributes = ctx.buf.attributes.push type := by
    grind [Buffed.IRBufContext.insertAttrs]
  have htidx : typeIdx.toNat = ctx.buf.attributes.size := by
    grind [Buffed.IRBufContext.insertAttrs]
  have hin := ctx.sim.in_bounds (.operation opPtr.spec) (by grind)
  have hsz : ctx.buf.mem.size < 2^63 := by grind
  have hincl := OperationPtr.nthResult_range_included_op_range ctx opPtr.spec idx hcap (by grind)
  have hidxlt : idx.toNat < 4294967296 := by
    have := ctx.isRepr.operations_indices opPtr.spec (by grind) |>.capResults
    grind
  have hmul : (Buffed.OpResult.size * idx).toNat = Buffed.OpResult.sizeNat * idx.toNat := by
    rw [UInt64.toNat_mul]
    grind
  have hoff := OperationPtr.computeResultsOffset!_ideal ctx opPtr (by grind) (by grind) hnum
  have hopM : (UInt64.toNat opPtr.impl : Int) = opPtr.spec.toFlat := by
    have := opPtrInBounds.sim
    simp only [Sim.OperationPtr.Sim, OperationPtr.toM] at this
    grind [OperationPtr.toFlat, OperationPtr.range]
  have hslotaddr : ((Buffed.OperationMPtr.getResultPtr! ctx.buf opPtr.impl idx).toNat : Int)
      = opPtr.spec.toFlat + (Buffed.Operation.Offsets.resultsInt opPtr.spec ctx.spec + Buffed.OpResult.sizeNat * idx.toNat) := by
    simp only [Buffed.OperationMPtr.getResultPtr!, Buffed.OperationMPtr.computeResultOffset!]
    grind [IsIncludedI, IsIncludedIN]
  have husz : (Buffed.OperationMPtr.getResultPtr! ctx.buf opPtr.impl idx).toNat + 40 ≤ ctx.buf.mem.size := by
    grind
  have ek : ∀ (off : Int64) (n : Nat), off.toInt = n → n + 8 ≤ 40 →
      ((Buffed.OperationMPtr.getResultPtr! ctx.buf opPtr.impl idx) + off).toNat
        = (Buffed.OperationMPtr.getResultPtr! ctx.buf opPtr.impl idx).toNat + n := by
    intro off n hn h40
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
  constructor
  · -- fieldsInBounds
    have hofib : OpResult.FieldsInBounds
        { type := type, firstUse := none, index := opPtr.spec.getNumResults! ctx.spec,
          owner := opPtr.spec } ctx.spec := by
      constructor <;> grind
    have hofibP : OpResult.FieldsInBounds
        { type := type, firstUse := none, index := opPtr.spec.getNumResults! ctx.spec,
          owner := opPtr.spec } (Rewriter.pushResult ctx.spec opPtr.spec type (by grind)) := by
      clear hread hread32 ek heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
      constructor <;> grind [Rewriter.pushResult]
    clear hread hread32 ek heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
    grind [Rewriter.pushResult]
  · -- repr
    clear hread hread32 ek heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
    grind [Rewriter.pushResult, layout_grind]
  · -- in_bounds
    simp only
    intros gptr gptrIb
    clear hread hread32 ek heq; (try clear hslotB hattrB hbsz hmem1 hattr1 htidx heqAttr)
    have := ctx.sim.in_bounds gptr (by grind [Rewriter.pushResult])
    grind [TopLevelPtr, Rewriter.pushResult]
  · -- disjoint_allocs
    simp only
    clear hread hread32 ek heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
    have := ctx.sim.disjoint_allocs
    grind [TopLevelPtr, Rewriter.pushResult]
  · -- encoding_op
    simp only
    intros op opIb
    have hopib : op.InBounds ctx.spec := by clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr); (try clear hro8 hro4); (try clear hslot hnum); grind [Rewriter.pushResult]
    have hoin := ctx.sim.in_bounds (.operation op) (by grind)
    have henc := ctx.sim.encoding_op op (by grind)
    have hd := ctx.sim.disjoint_allocs (.operation op) (.operation opPtr.spec) (by grind) (by grind)
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
    have hareaRESP : Buffed.Operation.Offsets.resultsInt opPtr.spec ctx.spec
        = -(((opPtr.spec.get! ctx.spec).capResults * 40 : Nat) : Int) := by
      simp only [Buffed.Operation.Offsets.resultsInt, Buffed.Operation.Sizes.resultsNat]
      grind
    have hopM : (UInt64.toNat op.toM : Int) = op.toFlat := by
      simp only [OperationPtr.toM]
      grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', OperationPtr.toFlat, layout_grind]
    have hro8 : ∀ (off : Int64) (n : Nat), off.toInt = n → n + 8 ≤ 72 →
        bufctx.mem.read64! (op.toM + off) = ctx.buf.mem.read64! (op.toM + off) := by
      intro off n hn h72
      apply hread
      have hri1 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr hopib
      have hri2 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr opPtrInBounds.ib
      by_cases hcase : op = opPtr.spec
      · subst hcase
        rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind]
      · have hdd := hd (by simp [hcase])
        simp only [TopLevelPtr.range, hri1, hri2, IsDisjointI, OperationPtr.rangeInt,
          Buffed.Operation.rangeInt, add_nat_range_def] at hdd
        rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind]
    have hro4 : ∀ (off : Int64) (n : Nat), off.toInt = n → n + 4 ≤ 72 →
        bufctx.mem.read32! (op.toM + off) = ctx.buf.mem.read32! (op.toM + off) := by
      intro off n hn h72
      apply hread32
      have hri1 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr hopib
      have hri2 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr opPtrInBounds.ib
      by_cases hcase : op = opPtr.spec
      · subst hcase
        rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind]
      · have hdd := hd (by simp [hcase])
        simp only [TopLevelPtr.range, hri1, hri2, IsDisjointI, OperationPtr.rangeInt,
          Buffed.Operation.rangeInt, add_nat_range_def] at hdd
        rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind]
    constructor
    · constructor
      · have := henc.prev
        simp only [Buffed.OperationMPtr.readPrev!] at this ⊢
        rw [hro8 Buffed.Operation.Offsets.prev 8 (by decide) (by decide)]
        clear hread hread32 ek heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
        grind [layout_grind, Rewriter.pushResult]
      · have := henc.next
        simp only [Buffed.OperationMPtr.readNext!] at this ⊢
        rw [hro8 Buffed.Operation.Offsets.next 16 (by decide) (by decide)]
        clear hread hread32 ek heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
        grind [layout_grind, Rewriter.pushResult]
      · have := henc.parent
        simp only [Buffed.OperationMPtr.readParent!] at this ⊢
        rw [hro8 Buffed.Operation.Offsets.parent 24 (by decide) (by decide)]
        clear hread hread32 ek heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
        grind [layout_grind, Rewriter.pushResult]
      · have := henc.opType
        simp only [Buffed.OperationMPtr.readOpType!] at this ⊢
        rw [hro4 Buffed.Operation.Offsets.opType 32 (by decide) (by decide)]
        clear hread hread32 ek heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
        grind [layout_grind, Rewriter.pushResult]
      · have := henc.attrs
        simp only [Buffed.OperationMPtr.readAttrs!, hattrB] at this ⊢
        rw [hro8 Buffed.Operation.Offsets.attrs 64 (by decide) (by decide)]
        clear hread hread32 ek heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
        grind [layout_grind, Rewriter.pushResult]
    · constructor
      · have := henc.numBlockOperands
        simp only [Buffed.OperationMPtr.readNumBlockOperands!] at this ⊢
        rw [hro8 Buffed.Operation.Offsets.numBlockOperands 40 (by decide) (by decide)]
        clear hread hread32 ek heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
        grind [layout_grind, Rewriter.pushResult]
      · intros bo boIb heq2
        dsimp only at boIb
        have hboib : bo.InBounds ctx.spec := by clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr); (try clear hro8 hro4); (try clear hslot hnum); grind [Rewriter.pushResult]
        have := henc.blockOperands bo (by grind) (by grind)
        have hbomeq : bo.toM (Rewriter.pushResult ctx.spec opPtr.spec type (by grind)) = bo.toM ctx.spec := by
          clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
          simp only [BlockOperandPtr.toM, BlockOperandPtr.toFlat]
          grind [layout_grind, Rewriter.pushResult]
        have hboget : bo.get! (Rewriter.pushResult ctx.spec opPtr.spec type (by grind)) = bo.get! ctx.spec := by
          clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
          grind [Rewriter.pushResult]
        have hboaft := Sim.BlockOperandPtr.after_lt_ctx (ctx := ctx) bo hboib
        have hboM : (UInt64.toNat (bo.toM ctx.spec) : Int) = bo.toFlat ctx.spec := by
          simp only [BlockOperandPtr.toM]
          grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', BlockOperandPtr.toFlat]
        have hboidx : bo.index < (op.get! ctx.spec).capBlockOperands := by clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr); (try clear hro8 hro4); (try clear hslot hnum); grind [Veir.BlockOperandPtr.inBounds_def]
        have hboflat : ((bo.toFlat ctx.spec : Nat) : Int) = op.toFlat + Buffed.Operation.Offsets.blockOperandsInt op ctx.spec + ((bo.index * 32 : Nat) : Int) := by
          rw [BlockOperandPtr.toFlat_ideal ctx.sim.repr bo hboib]
          simp only [BlockOperandPtr.toFlatNat, heq2, show Buffed.BlockOperand.sizeNat = 32 from rfl]
          have h0 : (0:Int) ≤ op.toFlat + Buffed.Operation.Offsets.blockOperandsInt op ctx.spec := by
            rw [hareaBO, hareaOP]
            omega
          omega
        have hbo : ∀ (off : Int64) (n : Nat), off.toInt = n → n + 8 ≤ 32 →
            bufctx.mem.read64! (bo.toM ctx.spec + off) = ctx.buf.mem.read64! (bo.toM ctx.spec + off) := by
          intro off n hn h32
          apply hread
          have hri1 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr hopib
          have hri2 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr opPtrInBounds.ib
          by_cases hcase : op = opPtr.spec
          · subst hcase
            rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind]
          · have hdd := hd (by simp [hcase])
            simp only [TopLevelPtr.range, hri1, hri2, IsDisjointI, OperationPtr.rangeInt,
              Buffed.Operation.rangeInt, add_nat_range_def] at hdd
            rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind]
        constructor
        · have := this.nextUse
          simp only [Buffed.BlockOperandMPtr.readNextUse!, hbomeq, hboget] at this ⊢
          rw [hbo Buffed.BlockOperand.Offsets.nextUse 0 (by decide) (by decide)]
          clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
          grind [layout_grind, Rewriter.pushResult]
        · have := this.back
          simp only [Buffed.BlockOperandMPtr.readBack!, hbomeq, hboget] at this ⊢
          rw [hbo Buffed.BlockOperand.Offsets.back 8 (by decide) (by decide)]
          clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
          grind [layout_grind, Rewriter.pushResult]
        · have := this.owner
          simp only [Buffed.BlockOperandMPtr.readOwner!, hbomeq, hboget] at this ⊢
          rw [hbo Buffed.BlockOperand.Offsets.owner 16 (by decide) (by decide)]
          clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
          grind [layout_grind, Rewriter.pushResult]
        · have := this.value
          simp only [Buffed.BlockOperandMPtr.readValue!, hbomeq, hboget] at this ⊢
          rw [hbo Buffed.BlockOperand.Offsets.value 24 (by decide) (by decide)]
          clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
          grind [layout_grind, Rewriter.pushResult]
    · constructor
      · have := henc.numRegions
        simp only [Buffed.OperationMPtr.readNumRegions!] at this ⊢
        rw [hro8 Buffed.Operation.Offsets.numRegions 48 (by decide) (by decide)]
        clear hread hread32 ek heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
        grind [layout_grind, Rewriter.pushResult]
      · intros ridx ridxIn
        dsimp only at ridxIn
        have hridxOld : ridx < op.getNumRegions! ctx.spec := by
          clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
          (try clear hro8 hro4); (try clear hslot hnum)
          grind [Rewriter.pushResult]
        have := henc.regions ridx (by clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr); (try clear hro8 hro4); (try clear hslot hnum); grind [Rewriter.pushResult])
        have hcapr := ctx.sim.repr.operations_indices op (by grind) |>.capRegions
        have hcro : Buffed.OperationMPtr.computeRegionsOffset! bufctx op.toM
            = Buffed.OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
          simp only [Buffed.OperationMPtr.computeRegionsOffset!, Buffed.OperationMPtr.computeBlockOperandsOffset!,
            Buffed.OperationMPtr.computeOperandsOffset!, Buffed.OperationMPtr.readNumBlockOperands!,
            Buffed.OperationMPtr.readNumOperands!, Buffed.OperationMPtr.readOpType!]
          rw [hro8 Buffed.Operation.Offsets.numBlockOperands 40 (by decide) (by decide),
            hro8 Buffed.Operation.Offsets.numOperands 56 (by decide) (by decide),
            hro4 Buffed.Operation.Offsets.opType 32 (by decide) (by decide)]
        have hcri := Veir.OperationPtr.computeRegionsOffset!_ideal ctx ⟨op.toM, op⟩ (by grind) (by grind) (by
          clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
          (try clear hro8 hro4); (try clear hslot hnum)
          have h5 : op.toFlat = op.id := rfl
          have h6 : Buffed.Operation.sizeBaseNat = 72 := rfl
          simp only [Buffed.IRBufContext.size_def]
          omega)
        have hnth : Buffed.OperationMPtr.readNthRegion! bufctx op.toM ridx.toUInt64
            = Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM ridx.toUInt64 := by
          simp only [Buffed.OperationMPtr.readNthRegion!, Buffed.OperationMPtr.computeRegionOffset!, hcro]
          apply hread
          have hri1 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr hopib
          have hri2 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr opPtrInBounds.ib
          by_cases hcase : op = opPtr.spec
          · subst hcase
            clear hread32 ek heq hcro this; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
            rw [UInt64.uint64_add_int64_toNat_lt] <;>
              grind [layout_grind, UInt64.toNat_mul]
          · have hdd := hd (by simp [hcase])
            have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op ridx.toUInt64
              (by clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt hcro this hdd heq;
                  (try clear hro8 hro4); (try clear hslot); grind) hopib
            simp only [OperationPtr.rangeInt, Buffed.Operation.rangeInt, OperationPtr.toFlat,
              add_nat_range_def, IsIncludedI] at hincl2
            have hraddr : ((op.toM + (Buffed.OperationMPtr.computeRegionsOffset! ctx.buf op.toM + Buffed.ptrSize * ridx.toUInt64)).toNat : Int)
                = op.toM.toNat + (Buffed.Operation.Offsets.regionsInt op ctx.spec + Buffed.ptrSizeNat * ridx.toUInt64.toNat) := by
              clear hread hread32 ek hslotaddr husz hincl hcro this hdd hincl2 heq
              (try clear hro8 hro4); (try clear hslot)
              rw [UInt64.uint64_add_int64_toNat_lt] <;>
                grind [OperationPtr.toM, OperationPtr.toFlat,
                  OperationPtr.computeRegionsOffet!_plus_offset_eq_regionsInt]
            simp only [TopLevelPtr.range, hri1, hri2, IsDisjointI, OperationPtr.rangeInt,
              Buffed.Operation.rangeInt, add_nat_range_def] at hdd
            clear hread32 ek heq hcro this; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
            rw [UInt64.uint64_add_int64_toNat_lt] <;>
              grind [layout_grind, UInt64.toNat_mul]
        rw [Sim.RegionPtr.Sim] at this ⊢
        simp only [hnth]
        clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt hcro hnth heq
        grind [layout_grind, Rewriter.pushResult]
    · constructor
      · have := henc.numOperands
        simp only [Buffed.OperationMPtr.readNumOperands!] at this ⊢
        rw [hro8 Buffed.Operation.Offsets.numOperands 56 (by decide) (by decide)]
        clear hread hread32 ek heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
        grind [layout_grind, Rewriter.pushResult]
      · intros oper operIb heq2
        dsimp only at operIb
        have hoperib : oper.InBounds ctx.spec := by clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr); (try clear hro8 hro4); (try clear hslot hnum); grind [Rewriter.pushResult]
        have := henc.operands oper (by grind) (by grind)
        have hopermeq : oper.toM (Rewriter.pushResult ctx.spec opPtr.spec type (by grind)) = oper.toM ctx.spec := by
          clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
          simp only [OpOperandPtr.toM, OpOperandPtr.toFlat]
          grind [layout_grind, Rewriter.pushResult]
        have hoperget : oper.get! (Rewriter.pushResult ctx.spec opPtr.spec type (by grind)) = oper.get! ctx.spec := by
          clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
          grind [Rewriter.pushResult]
        have hoperaft := Sim.OpOperandPtr.after_lt_ctx (ctx := ctx) oper hoperib
        have hoperM : (UInt64.toNat (oper.toM ctx.spec) : Int) = oper.toFlat ctx.spec := by
          simp only [OpOperandPtr.toM]
          grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', OpOperandPtr.toFlat]
        have hoperidx : oper.index < (op.get! ctx.spec).capOperands := by clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr); (try clear hro8 hro4); (try clear hslot hnum); grind [Veir.OpOperandPtr.inBounds_def]
        have hoperflat : ((oper.toFlat ctx.spec : Nat) : Int) = op.toFlat + Buffed.Operation.Offsets.operandsInt op ctx.spec + ((oper.index * 32 : Nat) : Int) := by
          rw [OpOperandPtr.toFlat_ideal ctx.sim.repr oper hoperib]
          simp only [OpOperandPtr.toFlatNat, heq2, show Buffed.OpOperand.sizeNat = 32 from rfl]
          have h0 : (0:Int) ≤ op.toFlat + Buffed.Operation.Offsets.operandsInt op ctx.spec := by
            rw [hareaOP]
            omega
          omega
        have hop : ∀ (off : Int64) (n : Nat), off.toInt = n → n + 8 ≤ 32 →
            bufctx.mem.read64! (oper.toM ctx.spec + off) = ctx.buf.mem.read64! (oper.toM ctx.spec + off) := by
          intro off n hn h32
          apply hread
          have hri1 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr hopib
          have hri2 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr opPtrInBounds.ib
          by_cases hcase : op = opPtr.spec
          · subst hcase
            rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind]
          · have hdd := hd (by simp [hcase])
            simp only [TopLevelPtr.range, hri1, hri2, IsDisjointI, OperationPtr.rangeInt,
              Buffed.Operation.rangeInt, add_nat_range_def] at hdd
            rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind]
        constructor
        · have := this.nextUse
          simp only [Buffed.OpOperandMPtr.readNextUse!, hopermeq, hoperget] at this ⊢
          rw [hop Buffed.OpOperand.Offsets.nextUse 0 (by decide) (by decide)]
          clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
          grind [layout_grind, Rewriter.pushResult]
        · have := this.back
          simp only [Buffed.OpOperandMPtr.readBack!, hopermeq, hoperget] at this ⊢
          rw [hop Buffed.OpOperand.Offsets.back 8 (by decide) (by decide)]
          clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
          grind [layout_grind, Rewriter.pushResult]
        · have := this.owner
          simp only [Buffed.OpOperandMPtr.readOwner!, hopermeq, hoperget] at this ⊢
          rw [hop Buffed.OpOperand.Offsets.owner 16 (by decide) (by decide)]
          clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
          grind [layout_grind, Rewriter.pushResult]
        · have := this.value
          simp only [Buffed.OpOperandMPtr.readValue!, hopermeq, hoperget] at this ⊢
          rw [hop Buffed.OpOperand.Offsets.value 24 (by decide) (by decide)]
          clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
          grind [layout_grind, Rewriter.pushResult]
    · constructor
      · have := henc.numResults
        simp only [Buffed.OperationMPtr.readNumResults!] at this ⊢
        rw [hro8 Buffed.Operation.Offsets.numResults 0 (by decide) (by decide)]
        clear hread hread32 ek heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
        grind [layout_grind, Rewriter.pushResult]
      · intros res resIb heq2
        dsimp only at resIb
        by_cases hnewres : res = opPtr.spec.nextResult ctx.spec
        · -- the freshly pushed result: reads land on the five writes just made
          have hopeq : op = opPtr.spec := by
            clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
            (try clear hro8 hro4); (try clear hslot hnum)
            grind
          subst hopeq
          subst hnewres
          have hnidx : (opPtr.spec.nextResult ctx.spec).index = idx.toNat := by
            clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
            (try clear hro8 hro4); (try clear hslot hnum)
            grind
          have hnop : (opPtr.spec.nextResult ctx.spec).op = opPtr.spec := by
            clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
            (try clear hro8 hro4); (try clear hslot hnum)
            grind
          have hreprN : (Rewriter.pushResult ctx.spec opPtr.spec type (by grind)).IsRepr := by
            clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
            (try clear hro8 hro4); (try clear hslot hnum)
            grind [Rewriter.pushResult, layout_grind]
          have hnget : (opPtr.spec.nextResult ctx.spec).get! (Rewriter.pushResult ctx.spec opPtr.spec type (by grind))
              = { type := type, firstUse := none, index := opPtr.spec.getNumResults! ctx.spec,
                  owner := opPtr.spec } := by
            clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
            (try clear hro8 hro4); (try clear hslot hnum)
            grind [Rewriter.pushResult]
          have hopsame : Buffed.Operation.Offsets.resultsInt opPtr.spec (Rewriter.pushResult ctx.spec opPtr.spec type (by grind))
              = Buffed.Operation.Offsets.resultsInt opPtr.spec ctx.spec := by
            clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
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
            clear hread hread32 ek heq hoff hincl husz hmul
            (try clear hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr hslotB)
            (try clear hro8 hro4)
            (try clear hnget hreprN hopsame)
            clear henc hd haft hri hareaOP hareaBO hareaRG hareaAFT hareaRES hareaRESP hoin hin
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
            clear hread hread32 ek heq
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
            rfl
          · -- index
            simp only [Buffed.OpResultMPtr.readIndex!, hnMeq, hnget]
            rw [← heq]
            simp only [Buffed.OpResultMPtr.writeOwner, Buffed.OpResultMPtr.writeIndex,
              Buffed.OpResultMPtr.writeFirstUse, Buffed.OpResultMPtr.writeType, Buffed.ValueImplMPtr.writeKind]
            rw [ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have h1 := ek Buffed.OpResult.Offsets.owner 32 (by decide) (by decide); have h2 := ek Buffed.OpResult.Offsets.index 24 (by decide) (by decide); omega),
              ExArray.read64!_blit64_self]
            clear hread hread32 ek heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
            grind
          · -- owner
            simp only [Buffed.OpResultMPtr.readOwner!, hnMeq, hnget]
            rw [← heq]
            simp only [Buffed.OpResultMPtr.writeOwner, Buffed.OpResultMPtr.writeIndex,
              Buffed.OpResultMPtr.writeFirstUse, Buffed.OpResultMPtr.writeType, Buffed.ValueImplMPtr.writeKind]
            rw [ExArray.read64!_blit64_self]
            have := opPtrInBounds.sim
            clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
            (try clear hro8 hro4); (try clear hslot hnum)
            grind [Rewriter.pushResult]
        · -- pre-existing result: reads are disjoint from the written slot
          have hresib : res.InBounds ctx.spec := by clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr); (try clear hro8 hro4); (try clear hslot hnum); grind [Rewriter.pushResult]
          have := henc.results res (by grind) (by grind)
          have hresmeq : res.toM (Rewriter.pushResult ctx.spec opPtr.spec type (by grind)) = res.toM ctx.spec := by
            clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
            simp only [OpResultPtr.toM, OpResultPtr.toFlat]
            grind [layout_grind, Rewriter.pushResult]
          have hresget : res.get! (Rewriter.pushResult ctx.spec opPtr.spec type (by grind)) = res.get! ctx.spec := by
            clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
            grind [Rewriter.pushResult]
          have hresaft := Sim.OpResultPtr.after_lt_ctx (ctx := ctx) res hresib
          have hresM : (UInt64.toNat (res.toM ctx.spec) : Int) = res.toFlat ctx.spec := by
            simp only [OpResultPtr.toM]
            grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', OpResultPtr.toFlat]
          have hresidx : res.index < (op.get! ctx.spec).capResults := by clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr); (try clear hro8 hro4); (try clear hslot hnum); grind [Veir.OpResultPtr.inBounds_def]
          have hoplow : (0:Int) ≤ op.toFlat + Buffed.Operation.Offsets.resultsInt op ctx.spec := by
            have hio := hoin
            have hr := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr hopib
            simp only [TopLevelPtr.range, hr, OperationPtr.rangeInt, Buffed.Operation.rangeInt,
              add_nat_range_def, IsIncludedIN] at hio
            grind [ExArray.range_lower, ExArray.range_upper]
          have hresflat : ((res.toFlat ctx.spec : Nat) : Int) = op.toFlat + Buffed.Operation.Offsets.resultsInt op ctx.spec + ((res.index * 40 : Nat) : Int) := by
            rw [OpResultPtr.toFlat_ideal ctx.sim.repr res hresib]
            simp only [OpResultPtr.toFlatNat, heq2, show Buffed.OpResult.sizeNat = 40 from rfl]
            omega
          have hres : ∀ (off : Int64) (n : Nat), off.toInt = n → n + 8 ≤ 40 →
              bufctx.mem.read64! (res.toM ctx.spec + off) = ctx.buf.mem.read64! (res.toM ctx.spec + off) := by
            intro off n hn h40
            apply hread
            have hri1 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr hopib
            have hri2 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr opPtrInBounds.ib
            by_cases hcase : op = opPtr.spec
            · subst hcase
              have h1 : res.index < opPtr.spec.getNumResults! ctx.spec := by
                clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
                (try clear hro8 hro4); (try clear hslot hnum)
                grind [Veir.OpResultPtr.inBounds_def]
              have h2 : Buffed.OpResult.Offsets.afterInt = 40 := rfl
              have h3 : Int64.maxValue.toInt = 9223372036854775807 := rfl
              (try simp only [Buffed.IRBufContext.size_def] at hresaft)
              simp only [show Buffed.OpResult.sizeNat = 40 from rfl] at hslotaddr hincl
              rw [UInt64.uint64_add_int64_toNat_lt] <;> omega
            · have hdd := hd (by simp [hcase])
              simp only [TopLevelPtr.range, hri1, hri2, IsDisjointI, OperationPtr.rangeInt,
                Buffed.Operation.rangeInt, add_nat_range_def] at hdd
              clear hread32 ek heq this; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
              rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind, Veir.OpResultPtr.inBounds_def]
          have hres0 : bufctx.mem.read64! (res.toM ctx.spec) = ctx.buf.mem.read64! (res.toM ctx.spec) := by
            apply hread
            have hri1 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr hopib
            have hri2 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr opPtrInBounds.ib
            by_cases hcase : op = opPtr.spec
            · subst hcase
              have h1 : res.index < opPtr.spec.getNumResults! ctx.spec := by
                clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
                (try clear hro8 hro4); (try clear hslot hnum)
                grind [Veir.OpResultPtr.inBounds_def]
              have h2 : Buffed.OpResult.Offsets.afterInt = 40 := rfl
              have h3 : Int64.maxValue.toInt = 9223372036854775807 := rfl
              (try simp only [Buffed.IRBufContext.size_def] at hresaft)
              simp only [show Buffed.OpResult.sizeNat = 40 from rfl] at hslotaddr hincl
              omega
            · have hdd := hd (by simp [hcase])
              simp only [TopLevelPtr.range, hri1, hri2, IsDisjointI, OperationPtr.rangeInt,
                Buffed.Operation.rangeInt, add_nat_range_def] at hdd
              clear hread32 ek heq this; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
              grind [layout_grind]
          constructor
          · have := this.kind
            simp only [Buffed.OpResultMPtr.readKind!, hresmeq] at this ⊢
            rw [hres0]
            clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
            grind [layout_grind, Rewriter.pushResult]
          · have := this.typee
            simp only [Buffed.OpResultMPtr.readType!, hattrB, hresmeq] at this ⊢
            rw [hres Buffed.ValueImpl.Offsets.type 8 (by decide) (by decide)]
            clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
            grind [layout_grind, Rewriter.pushResult]
          · have := this.firstUse
            simp only [Buffed.OpResultMPtr.readFirstUse!, hresmeq, hresget] at this ⊢
            rw [hres Buffed.ValueImpl.Offsets.firstUse 16 (by decide) (by decide)]
            clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
            grind [layout_grind, Rewriter.pushResult]
          · have := this.index
            simp only [Buffed.OpResultMPtr.readIndex!, hresmeq, hresget] at this ⊢
            rw [hres Buffed.OpResult.Offsets.index 24 (by decide) (by decide)]
            clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
            grind [layout_grind, Rewriter.pushResult]
          · have := this.owner
            simp only [Buffed.OpResultMPtr.readOwner!, hresmeq, hresget] at this ⊢
            rw [hres Buffed.OpResult.Offsets.owner 32 (by decide) (by decide)]
            clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
            grind [layout_grind, Rewriter.pushResult]
  · -- encoding_block
    simp only
    intros blk blkIb
    have hblkib : blk.InBounds ctx.spec := by
      clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr); (try clear hslot hnum)
      grind [Rewriter.pushResult]
    have hbin := ctx.sim.in_bounds (.block blk) (by grind)
    have henc := ctx.sim.encoding_block blk (by grind)
    have hdd := ctx.sim.disjoint_allocs (.block blk) (.operation opPtr.spec) (by grind) (by grind) (by simp)
    have hbri := ctx.sim.repr.blocks_indices blk (by grind)
    have hareaBLK : Buffed.Block.Offsets.afterInt blk ctx.spec
        = 56 + (((blk.get! ctx.spec).capArguments * 40 : Nat) : Int) := by rfl
    have hblkM : (UInt64.toNat blk.toM : Int) = blk.toFlat := by
      clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr); (try clear hslot hnum)
      simp only [BlockPtr.toM]
      grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', BlockPtr.toFlat, layout_grind]
    have haft := Sim.BlockPtr.after_lt_ctx (ctx := ctx) blk hblkib
    have hbget : blk.get! (Rewriter.pushResult ctx.spec opPtr.spec type (by grind)) = blk.get! ctx.spec := by
      clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr); (try clear hslot hnum)
      grind [Rewriter.pushResult]
    have hb8 : ∀ (off : Int64) (n : Nat), off.toInt = n → (n : Int) + 8 ≤ Buffed.Block.Offsets.afterInt blk ctx.spec →
        bufctx.mem.read64! (blk.toM + off) = ctx.buf.mem.read64! (blk.toM + off) := by
      intro off n hn hbnd
      apply hread
      have hri1 := BlockPtr.range_ideal ctx.sim.repr hblkib
      have hri2 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr opPtrInBounds.ib
      simp only [TopLevelPtr.range, hri1, hri2, IsDisjointI, BlockPtr.rangeInt, Buffed.Block.rangeInt,
        OperationPtr.rangeInt, Buffed.Operation.rangeInt, add_nat_range_def] at hdd
      clear hread32 ek heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
      rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind]
    constructor
    · constructor
      · have := henc.firstUse
        simp only [Buffed.BlockMPtr.readFirstUse!, hbget] at this ⊢
        rw [hb8 Buffed.Block.Offsets.firstUse 0 (by decide) (by simp only [hareaBLK]; omega)]
        clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr); (try clear hslot hnum)
        grind [layout_grind, Rewriter.pushResult]
      · have := henc.prev
        simp only [Buffed.BlockMPtr.readPrev!, hbget] at this ⊢
        rw [hb8 Buffed.Block.Offsets.prev 8 (by decide) (by simp only [hareaBLK]; omega)]
        clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr); (try clear hslot hnum)
        grind [layout_grind, Rewriter.pushResult]
      · have := henc.next
        simp only [Buffed.BlockMPtr.readNext!, hbget] at this ⊢
        rw [hb8 Buffed.Block.Offsets.next 16 (by decide) (by simp only [hareaBLK]; omega)]
        clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr); (try clear hslot hnum)
        grind [layout_grind, Rewriter.pushResult]
      · have := henc.parent
        simp only [Buffed.BlockMPtr.readParent!, hbget] at this ⊢
        rw [hb8 Buffed.Block.Offsets.parent 24 (by decide) (by simp only [hareaBLK]; omega)]
        clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr); (try clear hslot hnum)
        grind [layout_grind, Rewriter.pushResult]
      · have := henc.firstOp
        simp only [Buffed.BlockMPtr.readFirstOp!, hbget] at this ⊢
        rw [hb8 Buffed.Block.Offsets.firstOp 32 (by decide) (by simp only [hareaBLK]; omega)]
        clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr); (try clear hslot hnum)
        grind [layout_grind, Rewriter.pushResult]
      · have := henc.lastOp
        simp only [Buffed.BlockMPtr.readLastOp!, hbget] at this ⊢
        rw [hb8 Buffed.Block.Offsets.lastOp 40 (by decide) (by simp only [hareaBLK]; omega)]
        clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr); (try clear hslot hnum)
        grind [layout_grind, Rewriter.pushResult]
    · constructor
      · have := henc.numArguments
        simp only [Buffed.BlockMPtr.readNumArguments!, hbget] at this ⊢
        rw [hb8 Buffed.Block.Offsets.numArguments 48 (by decide) (by simp only [hareaBLK]; omega)]
        clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr); (try clear hslot hnum)
        grind [layout_grind, Rewriter.pushResult]
      · intros arg argIn heq2
        dsimp only at argIn
        have hargib : arg.InBounds ctx.spec := by
          clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr); (try clear hslot hnum)
          grind [Rewriter.pushResult]
        have := henc.arguments arg (by grind) (by grind)
        have hargget : arg.get! (Rewriter.pushResult ctx.spec opPtr.spec type (by grind)) = arg.get! ctx.spec := by
          clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr); (try clear hslot hnum)
          grind [Rewriter.pushResult]
        have hargidx : arg.index < (blk.get! ctx.spec).capArguments := by
          clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr); (try clear hslot hnum)
          grind [Veir.BlockArgumentPtr.inBounds_def]
        have hargaft := Sim.BlockArgumentPtr.after_lt_ctx (ctx := ctx) arg hargib
        have hargM : (UInt64.toNat arg.toM : Int) = arg.toFlat := by
          simp only [BlockArgumentPtr.toM]
          grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', BlockArgumentPtr.toFlat]
        have hargflat : ((arg.toFlat : Nat) : Int) = blk.toFlat + 56 + ((arg.index * 40 : Nat) : Int) := by
          rw [BlockArgumentPtr.toFlat_ideal]
          simp only [BlockArgumentPtr.toFlatNat, heq2, show Buffed.BlockArgument.sizeNat = 40 from rfl,
            show Buffed.Block.Offsets.argumentsInt = 56 from rfl]
          omega
        have harg : ∀ (off : Int64) (n : Nat), off.toInt = n → n + 8 ≤ 40 →
            bufctx.mem.read64! (arg.toM + off) = ctx.buf.mem.read64! (arg.toM + off) := by
          intro off n hn h40
          apply hread
          have hri1 := BlockPtr.range_ideal ctx.sim.repr hblkib
          have hri2 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr opPtrInBounds.ib
          simp only [TopLevelPtr.range, hri1, hri2, IsDisjointI, BlockPtr.rangeInt, Buffed.Block.rangeInt,
            OperationPtr.rangeInt, Buffed.Operation.rangeInt, add_nat_range_def] at hdd
          clear hread32 ek heq this; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
          rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind]
        have harg0 : bufctx.mem.read64! arg.toM = ctx.buf.mem.read64! arg.toM := by
          apply hread
          have hri1 := BlockPtr.range_ideal ctx.sim.repr hblkib
          have hri2 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr opPtrInBounds.ib
          simp only [TopLevelPtr.range, hri1, hri2, IsDisjointI, BlockPtr.rangeInt, Buffed.Block.rangeInt,
            OperationPtr.rangeInt, Buffed.Operation.rangeInt, add_nat_range_def] at hdd
          clear hread32 ek heq this; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
          grind [layout_grind]
        constructor
        · have := this.kind
          simp only [Buffed.BlockArgumentMPtr.readKind!] at this ⊢
          rw [harg0]
          clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr); (try clear hslot hnum)
          grind [layout_grind, Rewriter.pushResult]
        · have := this.type
          simp only [Buffed.BlockArgumentMPtr.readType!, hattrB, hargget] at this ⊢
          rw [harg Buffed.ValueImpl.Offsets.type 8 (by decide) (by decide)]
          clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr); (try clear hslot hnum)
          grind [layout_grind, Rewriter.pushResult]
        · have := this.firstUse
          simp only [Buffed.BlockArgumentMPtr.readFirstUse!, hargget] at this ⊢
          rw [harg Buffed.ValueImpl.Offsets.firstUse 16 (by decide) (by decide)]
          clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr); (try clear hslot hnum)
          grind [layout_grind, Rewriter.pushResult]
        · have := this.index
          simp only [Buffed.BlockArgumentMPtr.readIndex!, hargget] at this ⊢
          rw [harg Buffed.BlockArgument.Offsets.index 24 (by decide) (by decide)]
          clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr); (try clear hslot hnum)
          grind [layout_grind, Rewriter.pushResult]
        · have := this.owner
          simp only [Buffed.BlockArgumentMPtr.readOwner!, hargget] at this ⊢
          rw [harg Buffed.BlockArgument.Offsets.owner 32 (by decide) (by decide)]
          clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr); (try clear hslot hnum)
          grind [layout_grind, Rewriter.pushResult]
  · -- encoding_region
    simp only
    intros rg rgIb
    have hrgib : rg.InBounds ctx.spec := by
      clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr); (try clear hslot hnum)
      grind [Rewriter.pushResult]
    have hrin := ctx.sim.in_bounds (.region rg) (by grind)
    have henc := ctx.sim.encoding_region rg (by grind)
    have hdd := ctx.sim.disjoint_allocs (.region rg) (.operation opPtr.spec) (by grind) (by grind) (by simp)
    have hrgM : (UInt64.toNat rg.toM : Int) = rg.toFlat := by
      clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr); (try clear hslot hnum)
      simp only [RegionPtr.toM]
      grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', RegionPtr.toFlat, layout_grind]
    have hrgget : rg.get! (Rewriter.pushResult ctx.spec opPtr.spec type (by grind)) = rg.get! ctx.spec := by
      clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr); (try clear hslot hnum)
      grind [Rewriter.pushResult]
    have hrg8 : ∀ (off : Int64) (n : Nat), off.toInt = n → n + 8 ≤ 24 →
        bufctx.mem.read64! (rg.toM + off) = ctx.buf.mem.read64! (rg.toM + off) := by
      intro off n hn h24
      apply hread
      have hri2 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr opPtrInBounds.ib
      simp only [TopLevelPtr.range, RegionPtr.range_ideal, hri2, IsDisjointI, RegionPtr.rangeInt,
        Buffed.Region.rangeInt, OperationPtr.rangeInt, Buffed.Operation.rangeInt, add_nat_range_def] at hdd
      clear hread32 ek heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr)
      rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind]
    constructor
    · have := henc.firstBlock
      simp only [Buffed.RegionMPtr.readFirstBlock!, hrgget] at this ⊢
      rw [hrg8 Buffed.Region.Offsets.firstBlock 0 (by decide) (by decide)]
      clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr); (try clear hslot hnum)
      grind [layout_grind, Rewriter.pushResult]
    · have := henc.lastBlock
      simp only [Buffed.RegionMPtr.readLastBlock!, hrgget] at this ⊢
      rw [hrg8 Buffed.Region.Offsets.lastBlock 8 (by decide) (by decide)]
      clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr); (try clear hslot hnum)
      grind [layout_grind, Rewriter.pushResult]
    · have := henc.parent
      simp only [Buffed.RegionMPtr.readParent!, hrgget] at this ⊢
      rw [hrg8 Buffed.Region.Offsets.parent 16 (by decide) (by decide)]
      clear hread hread32 ek hoff hslotaddr husz hincl hmul hidxlt heq; (try clear hslotB hattrB hbsz hbrange hmem1 hattr1 htidx heqAttr); (try clear hslot hnum)
      grind [layout_grind, Rewriter.pushResult]
  · -- attr_empty: the table only gained a new entry, slot 0 is untouched
    (try dsimp only)
    rw [hattrB]
    have := ctx.sim.attr_empty
    clear hread hread32 ek heq
    grind

end Veir
