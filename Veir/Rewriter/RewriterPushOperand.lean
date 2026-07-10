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

/-! Rewriter simulation proofs -/

public section
namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo] [SerializableOpInfo OpInfo]
variable {ctx : Sim.IRContext OpInfo}

@[inline]
protected def Rewriter.setOperand (opPtr : Buffed.OperationMPtr) (ctx₀ : Buffed.IRBufContext OpInfo) (idx : UInt64)
    (hnum : (opPtr + Buffed.Operation.Offsets.opType).toInt + Buffed.Operation.Sizes.opType.toInt ≤ ctx₀.size)
    (hslot : (opPtr + opPtr.computeOperandOffset ctx₀ idx hnum).toNat + Buffed.OpOperand.size.toNat ≤ ctx₀.size)
    (value : Buffed.ValueImplMPtr) : Buffed.IRBufContext OpInfo :=
  let oper : Buffed.OpOperandMPtr := opPtr + opPtr.computeOperandOffset ctx₀ idx hnum
  let ctx := oper.writeNextUse ctx₀ .none (by prove_setSlotBounds ctx₀)
  -- `back` points at the value's `firstUse` slot, mirroring the spec's `OpOperandPtrPtr.valueFirstUse` (the use-list insertion re-writes it with the same value).
  let ctx := oper.writeBack ctx (value + Buffed.ValueImpl.Offsets.firstUse) (by prove_setSlotBounds ctx₀)
  let ctx := oper.writeOwner ctx opPtr (by prove_setSlotBounds ctx₀)
  let ctx := oper.writeValue ctx value (by prove_setSlotBounds ctx₀)
  ctx

@[irreducible]
protected def Rewriter.pushOperand (ctx : IRContext OpInfo) (opPtr : OperationPtr) (valuePtr : ValuePtr)
    (opPtrInBounds : opPtr.InBounds ctx := by grind) (valueInBounds : valuePtr.InBounds ctx := by grind) : IRContext OpInfo :=
  let op := (opPtr.get ctx (by grind))
  let index := opPtr.getNumOperands ctx (by grind)
  let operand := { value := valuePtr, owner := opPtr, back := OpOperandPtrPtr.valueFirstUse valuePtr, nextUse := none : OpOperand}
  have : operand.FieldsInBounds ctx := by constructor <;> grind
  opPtr.pushOperand ctx operand (by grind)

set_option maxHeartbeats 1000000000 in
/-- The `Sim` relation survives writing a fresh operand into slot `idx` of `opPtr`'s (pre-allocated) operand array while the spec pushes the corresponding `OpOperand`. -/
theorem Rewriter.setOperand_pushOperand_sim (opPtr : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo)
    (idx : UInt64) (valuePtr : Sim.ValuePtr)
    (opPtrInBounds : opPtr.InBounds ctx) (valueInBounds : valuePtr.InBounds ctx)
    (hidx : idx.toNat = opPtr.spec.getNumOperands! ctx.spec)
    (hcap : idx.toNat < (opPtr.spec.get! ctx.spec).capOperands)
    (hnum : (opPtr.impl + Buffed.Operation.Offsets.opType).toInt + Buffed.Operation.Sizes.opType.toInt ≤ ctx.buf.size)
    (hslot : (opPtr.impl + Buffed.OperationMPtr.computeOperandOffset ctx.buf opPtr.impl idx hnum).toNat + Buffed.OpOperand.size.toNat ≤ ctx.buf.size) :
    Veir.Sim ⟨Rewriter.setOperand opPtr.impl ctx.buf idx hnum hslot valuePtr.impl,
              Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind)⟩ := by
  have hin := ctx.sim.in_bounds (.operation opPtr.spec) (by grind)
  have hsz : ctx.buf.mem.size < 2^63 := by grind
  have hincl := OperationPtr.nthOperand_range_included_op_range ctx opPtr.spec idx hcap (by grind)
  have hidxlt : idx.toNat < 4294967296 := by
    have := ctx.isRepr.operations_indices opPtr.spec (by grind) |>.capOperands
    grind
  have hmul : (Buffed.OpOperand.size * idx).toNat = Buffed.OpOperand.sizeNat * idx.toNat := by
    rw [UInt64.toNat_mul]
    grind
  have hoff := OperationPtr.computeOperandsOffset!_ideal ctx opPtr (by grind) (by grind) hnum
  have hopM : (UInt64.toNat opPtr.impl : Int) = opPtr.spec.toFlat := by
    have := opPtrInBounds.sim
    simp only [Sim.OperationPtr.Sim, OperationPtr.toM] at this
    grind [OperationPtr.toFlat, OperationPtr.range]
  have hslotaddr : ((opPtr.impl + Buffed.OperationMPtr.computeOperandOffset ctx.buf opPtr.impl idx hnum).toNat : Int)
      = opPtr.spec.toFlat + (Buffed.Operation.Offsets.operandsInt opPtr.spec ctx.spec + Buffed.OpOperand.sizeNat * idx.toNat) := by
    simp only [Buffed.OperationMPtr.computeOperandOffset,
      Buffed.OperationMPtr.computeOperandsOffset_eq_computeOperandsOffset!]
    grind [Buffed.OperationMPtr.computeOperandOffset, IsIncludedI, IsIncludedIN]
  have husz : (opPtr.impl + Buffed.OperationMPtr.computeOperandOffset ctx.buf opPtr.impl idx hnum).toNat + 32 ≤ ctx.buf.mem.size := by
    grind
  have ek : ∀ (off : Int64) (n : Nat), off.toInt = n → n + 8 ≤ 32 →
      ((opPtr.impl + Buffed.OperationMPtr.computeOperandOffset ctx.buf opPtr.impl idx hnum) + off).toNat
        = (opPtr.impl + Buffed.OperationMPtr.computeOperandOffset ctx.buf opPtr.impl idx hnum).toNat + n := by
    intro off n hn h32
    rw [UInt64.uint64_add_int64_toNat_lt] <;> grind
  have hread : ∀ (a : UInt64),
      (a.toNat + 8 ≤ (opPtr.impl + Buffed.OperationMPtr.computeOperandOffset ctx.buf opPtr.impl idx hnum).toNat
       ∨ (opPtr.impl + Buffed.OperationMPtr.computeOperandOffset ctx.buf opPtr.impl idx hnum).toNat + 32 ≤ a.toNat) →
      (Rewriter.setOperand opPtr.impl ctx.buf idx hnum hslot valuePtr.impl).mem.read64! a = ctx.buf.mem.read64! a := by
    intro a ha
    simp only [Rewriter.setOperand, Buffed.OpOperandMPtr.writeValue, Buffed.OpOperandMPtr.writeOwner,
      Buffed.OpOperandMPtr.writeBack, Buffed.OpOperandMPtr.writeNextUse]
    rw [ExArray.read64!_blit64_disjoint _ _ _ _ _
        (by simp only [IsDisjoint]; have := ek Buffed.OpOperand.Offsets.value 24 (by decide) (by decide); omega),
      ExArray.read64!_blit64_disjoint _ _ _ _ _
        (by simp only [IsDisjoint]; have := ek Buffed.OpOperand.Offsets.owner 16 (by decide) (by decide); omega),
      ExArray.read64!_blit64_disjoint _ _ _ _ _
        (by simp only [IsDisjoint]; have := ek Buffed.OpOperand.Offsets.back 8 (by decide) (by decide); omega),
      ExArray.read64!_blit64_disjoint _ _ _ _ _
        (by simp only [IsDisjoint]; have := ek Buffed.OpOperand.Offsets.nextUse 0 (by decide) (by decide); omega)]
  have hread32 : ∀ (a : UInt64),
      (a.toNat + 4 ≤ (opPtr.impl + Buffed.OperationMPtr.computeOperandOffset ctx.buf opPtr.impl idx hnum).toNat
       ∨ (opPtr.impl + Buffed.OperationMPtr.computeOperandOffset ctx.buf opPtr.impl idx hnum).toNat + 32 ≤ a.toNat) →
      (Rewriter.setOperand opPtr.impl ctx.buf idx hnum hslot valuePtr.impl).mem.read32! a = ctx.buf.mem.read32! a := by
    intro a ha
    simp only [Rewriter.setOperand, Buffed.OpOperandMPtr.writeValue, Buffed.OpOperandMPtr.writeOwner,
      Buffed.OpOperandMPtr.writeBack, Buffed.OpOperandMPtr.writeNextUse]
    rw [ExArray.read32!_blit64_disjoint _ _ _ _ _
        (by simp only [IsDisjoint]; have := ek Buffed.OpOperand.Offsets.value 24 (by decide) (by decide); omega),
      ExArray.read32!_blit64_disjoint _ _ _ _ _
        (by simp only [IsDisjoint]; have := ek Buffed.OpOperand.Offsets.owner 16 (by decide) (by decide); omega),
      ExArray.read32!_blit64_disjoint _ _ _ _ _
        (by simp only [IsDisjoint]; have := ek Buffed.OpOperand.Offsets.back 8 (by decide) (by decide); omega),
      ExArray.read32!_blit64_disjoint _ _ _ _ _
        (by simp only [IsDisjoint]; have := ek Buffed.OpOperand.Offsets.nextUse 0 (by decide) (by decide); omega)]
  have hattr : (Rewriter.setOperand opPtr.impl ctx.buf idx hnum hslot valuePtr.impl).attributes = ctx.buf.attributes := by
    simp only [Rewriter.setOperand, Buffed.OpOperandMPtr.writeValue, Buffed.OpOperandMPtr.writeOwner,
      Buffed.OpOperandMPtr.writeBack, Buffed.OpOperandMPtr.writeNextUse]
  constructor
  · -- fieldsInBounds
    have hofib : OpOperand.FieldsInBounds
        { value := valuePtr.spec, owner := opPtr.spec,
          back := OpOperandPtrPtr.valueFirstUse valuePtr.spec, nextUse := none } ctx.spec := by
      constructor <;> grind
    grind [Rewriter.pushOperand]
  · -- repr
    clear hread hread32 hattr ek
    grind [Rewriter.pushOperand, layout_grind]
  · -- in_bounds
    simp only
    intros gptr gptrIb
    clear hread hread32 hattr ek
    have := ctx.sim.in_bounds gptr (by grind [Rewriter.pushOperand])
    grind [TopLevelPtr, Rewriter.pushOperand, Rewriter.setOperand]
  · -- disjoint_allocs
    simp only
    clear hread hread32 hattr ek
    have := ctx.sim.disjoint_allocs
    grind [TopLevelPtr, Rewriter.pushOperand]
  · -- encoding_op
    simp only
    intros op opIb
    have hopib : op.InBounds ctx.spec := by clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt; (try clear hro8 hro4); (try clear hslot hnum); grind [Rewriter.pushOperand]
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
    have hareaOPP : Buffed.Operation.Offsets.operandsInt opPtr.spec ctx.spec
        = 72 + ((Buffed.Operation.propertySize (opPtr.spec.getOpType! ctx.spec)).toNat : Int) := by rfl
    have hopM : (UInt64.toNat op.toM : Int) = op.toFlat := by
      simp only [OperationPtr.toM]
      grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', OperationPtr.toFlat, layout_grind]
    have hro8 : ∀ (off : Int64) (n : Nat), off.toInt = n → n + 8 ≤ 72 →
        (Rewriter.setOperand opPtr.impl ctx.buf idx hnum hslot valuePtr.impl).mem.read64! (op.toM + off) = ctx.buf.mem.read64! (op.toM + off) := by
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
        (Rewriter.setOperand opPtr.impl ctx.buf idx hnum hslot valuePtr.impl).mem.read32! (op.toM + off) = ctx.buf.mem.read32! (op.toM + off) := by
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
        grind [layout_grind, Rewriter.pushOperand]
      · have := henc.next
        simp only [Buffed.OperationMPtr.readNext!] at this ⊢
        rw [hro8 Buffed.Operation.Offsets.next 16 (by decide) (by decide)]
        grind [layout_grind, Rewriter.pushOperand]
      · have := henc.parent
        simp only [Buffed.OperationMPtr.readParent!] at this ⊢
        rw [hro8 Buffed.Operation.Offsets.parent 24 (by decide) (by decide)]
        grind [layout_grind, Rewriter.pushOperand]
      · have := henc.opType
        simp only [Buffed.OperationMPtr.readOpType!] at this ⊢
        rw [hro4 Buffed.Operation.Offsets.opType 32 (by decide) (by decide)]
        grind [layout_grind, Rewriter.pushOperand]
      · have := henc.attrs
        simp only [Buffed.OperationMPtr.readAttrs!, hattr] at this ⊢
        rw [hro8 Buffed.Operation.Offsets.attrs 64 (by decide) (by decide)]
        grind [layout_grind, Rewriter.pushOperand]
    · constructor
      · have := henc.numBlockOperands
        simp only [Buffed.OperationMPtr.readNumBlockOperands!] at this ⊢
        rw [hro8 Buffed.Operation.Offsets.numBlockOperands 40 (by decide) (by decide)]
        grind [layout_grind, Rewriter.pushOperand]
      · intros bo boIb heq
        dsimp only at boIb
        have hboib : bo.InBounds ctx.spec := by clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt; (try clear hro8 hro4); (try clear hslot hnum); grind [Rewriter.pushOperand]
        have := henc.blockOperands bo (by grind) (by grind)
        have hbomeq : bo.toM (Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind)) = bo.toM ctx.spec := by
          clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
          simp only [BlockOperandPtr.toM, BlockOperandPtr.toFlat]
          grind [layout_grind, Rewriter.pushOperand]
        have hboget : bo.get! (Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind)) = bo.get! ctx.spec := by
          clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
          grind [Rewriter.pushOperand]
        have hboaft := Sim.BlockOperandPtr.after_lt_ctx (ctx := ctx) bo hboib
        have hboM : (UInt64.toNat (bo.toM ctx.spec) : Int) = bo.toFlat ctx.spec := by
          simp only [BlockOperandPtr.toM]
          grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', BlockOperandPtr.toFlat]
        have hboidx : bo.index < (op.get! ctx.spec).capBlockOperands := by clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt; (try clear hro8 hro4); (try clear hslot hnum); grind [Veir.BlockOperandPtr.inBounds_def]
        have hboflat : ((bo.toFlat ctx.spec : Nat) : Int) = op.toFlat + Buffed.Operation.Offsets.blockOperandsInt op ctx.spec + ((bo.index * 32 : Nat) : Int) := by
          rw [BlockOperandPtr.toFlat_ideal ctx.sim.repr bo hboib]
          simp only [BlockOperandPtr.toFlatNat, heq, show Buffed.BlockOperand.sizeNat = 32 from rfl]
          have h0 : (0:Int) ≤ op.toFlat + Buffed.Operation.Offsets.blockOperandsInt op ctx.spec := by
            rw [hareaBO, hareaOP]
            omega
          omega
        have hbo : ∀ (off : Int64) (n : Nat), off.toInt = n → n + 8 ≤ 32 →
            (Rewriter.setOperand opPtr.impl ctx.buf idx hnum hslot valuePtr.impl).mem.read64! (bo.toM ctx.spec + off) = ctx.buf.mem.read64! (bo.toM ctx.spec + off) := by
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
          clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
          grind [layout_grind, Rewriter.pushOperand]
        · have := this.back
          simp only [Buffed.BlockOperandMPtr.readBack!, hbomeq, hboget] at this ⊢
          rw [hbo Buffed.BlockOperand.Offsets.back 8 (by decide) (by decide)]
          clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
          grind [layout_grind, Rewriter.pushOperand]
        · have := this.owner
          simp only [Buffed.BlockOperandMPtr.readOwner!, hbomeq, hboget] at this ⊢
          rw [hbo Buffed.BlockOperand.Offsets.owner 16 (by decide) (by decide)]
          clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
          grind [layout_grind, Rewriter.pushOperand]
        · have := this.value
          simp only [Buffed.BlockOperandMPtr.readValue!, hbomeq, hboget] at this ⊢
          rw [hbo Buffed.BlockOperand.Offsets.value 24 (by decide) (by decide)]
          clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
          grind [layout_grind, Rewriter.pushOperand]
    · constructor
      · have := henc.numRegions
        simp only [Buffed.OperationMPtr.readNumRegions!] at this ⊢
        rw [hro8 Buffed.Operation.Offsets.numRegions 48 (by decide) (by decide)]
        grind [layout_grind, Rewriter.pushOperand]
      · intros ridx ridxIn
        dsimp only at ridxIn
        have hridxOld : ridx < op.getNumRegions! ctx.spec := by
          clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
          (try clear hro8 hro4); (try clear hslot hnum)
          grind [Rewriter.pushOperand]
        have := henc.regions ridx (by clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt; (try clear hro8 hro4); (try clear hslot hnum); grind [Rewriter.pushOperand])
        have hcapr := ctx.sim.repr.operations_indices op (by grind) |>.capRegions
        have hcro : Buffed.OperationMPtr.computeRegionsOffset! (Rewriter.setOperand opPtr.impl ctx.buf idx hnum hslot valuePtr.impl) op.toM
            = Buffed.OperationMPtr.computeRegionsOffset! ctx.buf op.toM := by
          simp only [Buffed.OperationMPtr.computeRegionsOffset!, Buffed.OperationMPtr.computeBlockOperandsOffset!,
            Buffed.OperationMPtr.computeOperandsOffset!, Buffed.OperationMPtr.readNumBlockOperands!,
            Buffed.OperationMPtr.readNumOperands!, Buffed.OperationMPtr.readOpType!]
          rw [hro8 Buffed.Operation.Offsets.numBlockOperands 40 (by decide) (by decide),
            hro8 Buffed.Operation.Offsets.numOperands 56 (by decide) (by decide),
            hro4 Buffed.Operation.Offsets.opType 32 (by decide) (by decide)]
        have hcri := Veir.OperationPtr.computeRegionsOffset!_ideal ctx ⟨op.toM, op⟩ (by grind) (by grind) (by
          clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
          (try clear hro8 hro4); (try clear hslot hnum)
          have h5 : op.toFlat = op.id := rfl
          have h6 : Buffed.Operation.sizeBaseNat = 72 := rfl
          simp only [Buffed.IRBufContext.size_def]
          omega)
        have hnth : Buffed.OperationMPtr.readNthRegion! (Rewriter.setOperand opPtr.impl ctx.buf idx hnum hslot valuePtr.impl) op.toM ridx.toUInt64
            = Buffed.OperationMPtr.readNthRegion! ctx.buf op.toM ridx.toUInt64 := by
          simp only [Buffed.OperationMPtr.readNthRegion!, Buffed.OperationMPtr.computeRegionOffset!, hcro]
          apply hread
          have hri1 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr hopib
          have hri2 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr opPtrInBounds.ib
          by_cases hcase : op = opPtr.spec
          · subst hcase
            rw [UInt64.uint64_add_int64_toNat_lt] <;>
              grind [layout_grind, UInt64.toNat_mul]
          · have hdd := hd (by simp [hcase])
            simp only [TopLevelPtr.range, hri1, hri2, IsDisjointI, OperationPtr.rangeInt,
              Buffed.Operation.rangeInt, add_nat_range_def] at hdd
            rw [UInt64.uint64_add_int64_toNat_lt] <;>
              grind [layout_grind, UInt64.toNat_mul]
        rw [Sim.RegionPtr.Sim] at this ⊢
        simp only [hnth]
        clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt hcro hnth
        grind [layout_grind, Rewriter.pushOperand]
    · constructor
      · have := henc.numOperands
        simp only [Buffed.OperationMPtr.readNumOperands!] at this ⊢
        rw [hro8 Buffed.Operation.Offsets.numOperands 56 (by decide) (by decide)]
        grind [layout_grind, Rewriter.pushOperand]
      · intros oper operIb heq
        dsimp only at operIb
        by_cases hnewop : oper = opPtr.spec.nextOperand ctx.spec
        · -- the freshly pushed operand: reads land on the four writes just made
          have hopeq : op = opPtr.spec := by
            clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
            (try clear hro8 hro4); (try clear hslot hnum)
            grind
          subst hopeq
          subst hnewop
          have hnidx : (opPtr.spec.nextOperand ctx.spec).index = idx.toNat := by
            clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
            (try clear hro8 hro4); (try clear hslot hnum)
            grind
          have hnop : (opPtr.spec.nextOperand ctx.spec).op = opPtr.spec := by
            clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
            (try clear hro8 hro4); (try clear hslot hnum)
            grind
          have hreprN : (Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind)).IsRepr := by
            clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
            (try clear hro8 hro4); (try clear hslot hnum)
            grind [Rewriter.pushOperand, layout_grind]
          have hnget : (opPtr.spec.nextOperand ctx.spec).get! (Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind))
              = { value := valuePtr.spec, owner := opPtr.spec,
                  back := OpOperandPtrPtr.valueFirstUse valuePtr.spec, nextUse := none } := by
            clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
            (try clear hro8 hro4); (try clear hslot hnum)
            grind [Rewriter.pushOperand]
          have hopsame : Buffed.Operation.Offsets.operandsInt opPtr.spec (Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind))
              = Buffed.Operation.Offsets.operandsInt opPtr.spec ctx.spec := by
            clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
            (try clear hro8 hro4); (try clear hslot hnum)
            grind [Rewriter.pushOperand]
          have hnflat : ((((opPtr.spec.nextOperand ctx.spec).toFlat (Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind))) : Nat) : Int)
              = opPtr.spec.toFlat + Buffed.Operation.Offsets.operandsInt opPtr.spec ctx.spec + ((idx.toNat * 32 : Nat) : Int) := by
            rw [OpOperandPtr.toFlat_ideal hreprN _ operIb]
            simp only [OpOperandPtr.toFlatNat, hnop, hnidx, hopsame, show Buffed.OpOperand.sizeNat = 32 from rfl]
            have h0 : (0:Int) ≤ opPtr.spec.toFlat + Buffed.Operation.Offsets.operandsInt opPtr.spec ctx.spec := by
              rw [hareaOP]
              omega
            omega
          have hnMeq : (opPtr.spec.nextOperand ctx.spec).toM (Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind))
              = opPtr.impl + Buffed.OperationMPtr.computeOperandOffset ctx.buf opPtr.impl idx hnum := by
            simp only [OpOperandPtr.toM]
            grind [Nat.toUInt64_eq, UInt64.toNat_ofNat']
          constructor
          · -- nextUse
            simp only [Buffed.OpOperandMPtr.readNextUse!, hnMeq, hnget, Rewriter.setOperand,
              Buffed.OpOperandMPtr.writeValue, Buffed.OpOperandMPtr.writeOwner,
              Buffed.OpOperandMPtr.writeBack, Buffed.OpOperandMPtr.writeNextUse]
            rw [ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have h1 := ek Buffed.OpOperand.Offsets.value 24 (by decide) (by decide); have h2 := ek Buffed.OpOperand.Offsets.nextUse 0 (by decide) (by decide); omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have h1 := ek Buffed.OpOperand.Offsets.owner 16 (by decide) (by decide); have h2 := ek Buffed.OpOperand.Offsets.nextUse 0 (by decide) (by decide); omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have h1 := ek Buffed.OpOperand.Offsets.back 8 (by decide) (by decide); have h2 := ek Buffed.OpOperand.Offsets.nextUse 0 (by decide) (by decide); omega),
              ExArray.read64!_blit64_self]
            rfl
          · -- back
            simp only [Buffed.OpOperandMPtr.readBack!, hnMeq, hnget, Rewriter.setOperand,
              Buffed.OpOperandMPtr.writeValue, Buffed.OpOperandMPtr.writeOwner,
              Buffed.OpOperandMPtr.writeBack, Buffed.OpOperandMPtr.writeNextUse]
            rw [ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have h1 := ek Buffed.OpOperand.Offsets.value 24 (by decide) (by decide); have h2 := ek Buffed.OpOperand.Offsets.back 8 (by decide) (by decide); omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have h1 := ek Buffed.OpOperand.Offsets.owner 16 (by decide) (by decide); have h2 := ek Buffed.OpOperand.Offsets.back 8 (by decide) (by decide); omega),
              ExArray.read64!_blit64_self]
            have hvaft := Sim.ValuePtr.after_lt_ctx (ctx := ctx) valuePtr.spec valueInBounds.ib
            have hvM := valueInBounds.sim
            simp only [Sim.ValuePtr.Sim] at hvM
            have hvflatP : valuePtr.spec.toFlat (Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind)) = valuePtr.spec.toFlat ctx.spec := by
              clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt hro8 hro4
              (try clear hnMeq hnflat); (try clear hslot hnum)
              grind [Veir.ValuePtr.toFlat, Veir.OpResultPtr.toFlat, Veir.BlockArgumentPtr.toFlat,
                Rewriter.pushOperand]
            have hvMnat : (UInt64.toNat valuePtr.impl : Int) = valuePtr.spec.toFlat ctx.spec := by
              rw [← hvM]
              simp only [Veir.ValuePtr.toM]
              clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt hro8 hro4
              (try clear hnMeq hnflat); (try clear hslot hnum)
              grind [Nat.toUInt64_eq, UInt64.toNat_ofNat']
            have hbackM : (OpOperandPtrPtr.valueFirstUse valuePtr.spec).toM (Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind))
                = valuePtr.impl + Buffed.ValueImpl.Offsets.firstUse := by
              simp only [Veir.OpOperandPtrPtr.toM, Veir.OpOperandPtrPtr.toFlat, hvflatP]
              have h2 : (valuePtr.impl + Buffed.ValueImpl.Offsets.firstUse).toNat = UInt64.toNat valuePtr.impl + 16 := by
                rw [UInt64.uint64_add_int64_toNat_lt] <;>
                  (clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt hro8 hro4;
                   (try clear hnMeq hnflat); (try clear hslot hnum);
                   grind [show Buffed.ValueImpl.Offsets.firstUse.toInt = 16 from rfl,
                     show Buffed.ValueImpl.Offsets.afterInt = 24 from rfl])
              clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt hro8 hro4
              (try clear hnMeq hnflat); (try clear hslot hnum)
              grind [Nat.toUInt64_eq, UInt64.toNat_ofNat',
                show Buffed.ValueImpl.Offsets.firstUse.toInt = 16 from rfl,
                show Buffed.ValueImpl.Offsets.afterInt = 24 from rfl]
            simp only [Sim.OpOperandPtrPtr.Sim]
            (try dsimp only)
            exact hbackM
          · -- owner
            simp only [Buffed.OpOperandMPtr.readOwner!, hnMeq, hnget, Rewriter.setOperand,
              Buffed.OpOperandMPtr.writeValue, Buffed.OpOperandMPtr.writeOwner,
              Buffed.OpOperandMPtr.writeBack, Buffed.OpOperandMPtr.writeNextUse]
            rw [ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have h1 := ek Buffed.OpOperand.Offsets.value 24 (by decide) (by decide); have h2 := ek Buffed.OpOperand.Offsets.owner 16 (by decide) (by decide); omega),
              ExArray.read64!_blit64_self]
            have := opPtrInBounds.sim
            clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
            (try clear hro8 hro4); (try clear hslot hnum)
            grind [Rewriter.pushOperand]
          · -- value
            simp only [Buffed.OpOperandMPtr.readValue!, hnMeq, hnget, Rewriter.setOperand,
              Buffed.OpOperandMPtr.writeValue, Buffed.OpOperandMPtr.writeOwner,
              Buffed.OpOperandMPtr.writeBack, Buffed.OpOperandMPtr.writeNextUse]
            rw [ExArray.read64!_blit64_self]
            have hvM := valueInBounds.sim
            have hvaft := Sim.ValuePtr.after_lt_ctx (ctx := ctx) valuePtr.spec valueInBounds.ib
            simp only [Sim.ValuePtr.Sim] at hvM ⊢
            have hvflatP : valuePtr.spec.toFlat (Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind)) = valuePtr.spec.toFlat ctx.spec := by
              clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt hro8 hro4
              (try clear hnMeq hnflat); (try clear hslot hnum)
              grind [Veir.ValuePtr.toFlat, Veir.OpResultPtr.toFlat, Veir.BlockArgumentPtr.toFlat,
                Rewriter.pushOperand]
            (try dsimp only)
            simp only [Veir.ValuePtr.toM, hvflatP]
            rw [← hvM]
            rfl
        · -- pre-existing operand: reads are disjoint from the written slot
          have hoperib : oper.InBounds ctx.spec := by clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt; (try clear hro8 hro4); (try clear hslot hnum); grind [Rewriter.pushOperand]
          have := henc.operands oper (by grind) (by grind)
          have hopermeq : oper.toM (Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind)) = oper.toM ctx.spec := by
            clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
            simp only [OpOperandPtr.toM, OpOperandPtr.toFlat]
            grind [layout_grind, Rewriter.pushOperand]
          have hoperget : oper.get! (Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind)) = oper.get! ctx.spec := by
            clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
            grind [Rewriter.pushOperand]
          have hoperaft := Sim.OpOperandPtr.after_lt_ctx (ctx := ctx) oper hoperib
          have hoperM : (UInt64.toNat (oper.toM ctx.spec) : Int) = oper.toFlat ctx.spec := by
            simp only [OpOperandPtr.toM]
            grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', OpOperandPtr.toFlat]
          have hoperidx : oper.index < (op.get! ctx.spec).capOperands := by clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt; (try clear hro8 hro4); (try clear hslot hnum); grind [Veir.OpOperandPtr.inBounds_def]
          have hoperflat : ((oper.toFlat ctx.spec : Nat) : Int) = op.toFlat + Buffed.Operation.Offsets.operandsInt op ctx.spec + ((oper.index * 32 : Nat) : Int) := by
            rw [OpOperandPtr.toFlat_ideal ctx.sim.repr oper hoperib]
            simp only [OpOperandPtr.toFlatNat, heq, show Buffed.OpOperand.sizeNat = 32 from rfl]
            have h0 : (0:Int) ≤ op.toFlat + Buffed.Operation.Offsets.operandsInt op ctx.spec := by
              rw [hareaOP]
              omega
            omega
          have hop : ∀ (off : Int64) (n : Nat), off.toInt = n → n + 8 ≤ 32 →
              (Rewriter.setOperand opPtr.impl ctx.buf idx hnum hslot valuePtr.impl).mem.read64! (oper.toM ctx.spec + off) = ctx.buf.mem.read64! (oper.toM ctx.spec + off) := by
            intro off n hn h32
            apply hread
            have hri1 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr hopib
            have hri2 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr opPtrInBounds.ib
            by_cases hcase : op = opPtr.spec
            · subst hcase
              have h1 : oper.index < opPtr.spec.getNumOperands! ctx.spec := by
                clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
                (try clear hro8 hro4); (try clear hslot hnum)
                grind [Veir.OpOperandPtr.inBounds_def]
              have h2 : Buffed.OpOperand.Offsets.afterInt = 32 := rfl
              have h3 : Int64.maxValue.toInt = 9223372036854775807 := rfl
              simp only [Buffed.IRBufContext.size_def] at hoperaft
              simp only [show Buffed.OpOperand.sizeNat = 32 from rfl] at hslotaddr hincl
              rw [UInt64.uint64_add_int64_toNat_lt] <;> omega
            · have hdd := hd (by simp [hcase])
              simp only [TopLevelPtr.range, hri1, hri2, IsDisjointI, OperationPtr.rangeInt,
                Buffed.Operation.rangeInt, add_nat_range_def] at hdd
              rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind, Veir.OpOperandPtr.inBounds_def]
          constructor
          · have := this.nextUse
            simp only [Buffed.OpOperandMPtr.readNextUse!, hopermeq, hoperget] at this ⊢
            rw [hop Buffed.OpOperand.Offsets.nextUse 0 (by decide) (by decide)]
            clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
            grind [layout_grind, Rewriter.pushOperand]
          · have := this.back
            simp only [Buffed.OpOperandMPtr.readBack!, hopermeq, hoperget] at this ⊢
            rw [hop Buffed.OpOperand.Offsets.back 8 (by decide) (by decide)]
            clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
            grind [layout_grind, Rewriter.pushOperand]
          · have := this.owner
            simp only [Buffed.OpOperandMPtr.readOwner!, hopermeq, hoperget] at this ⊢
            rw [hop Buffed.OpOperand.Offsets.owner 16 (by decide) (by decide)]
            clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
            grind [layout_grind, Rewriter.pushOperand]
          · have := this.value
            simp only [Buffed.OpOperandMPtr.readValue!, hopermeq, hoperget] at this ⊢
            rw [hop Buffed.OpOperand.Offsets.value 24 (by decide) (by decide)]
            clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
            grind [layout_grind, Rewriter.pushOperand]
    · constructor
      · have := henc.numResults
        simp only [Buffed.OperationMPtr.readNumResults!] at this ⊢
        rw [hro8 Buffed.Operation.Offsets.numResults 0 (by decide) (by decide)]
        grind [layout_grind, Rewriter.pushOperand]
      · intros res resIb heq
        dsimp only at resIb
        have hresib : res.InBounds ctx.spec := by clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt; (try clear hro8 hro4); (try clear hslot hnum); grind [Rewriter.pushOperand]
        have := henc.results res (by grind) (by grind)
        have hresmeq : res.toM (Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind)) = res.toM ctx.spec := by
          clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
          simp only [OpResultPtr.toM, OpResultPtr.toFlat]
          grind [layout_grind, Rewriter.pushOperand]
        have hresget : res.get! (Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind)) = res.get! ctx.spec := by
          clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
          grind [Rewriter.pushOperand]
        have hresaft := Sim.OpResultPtr.after_lt_ctx (ctx := ctx) res hresib
        have hresM : (UInt64.toNat (res.toM ctx.spec) : Int) = res.toFlat ctx.spec := by
          simp only [OpResultPtr.toM]
          grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', OpResultPtr.toFlat]
        have hresidx : res.index < (op.get! ctx.spec).capResults := by clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt; (try clear hro8 hro4); (try clear hslot hnum); grind [Veir.OpResultPtr.inBounds_def]
        have hoplow : (0:Int) ≤ op.toFlat + Buffed.Operation.Offsets.resultsInt op ctx.spec := by
          have hio := hoin
          have hr := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr hopib
          simp only [TopLevelPtr.range, hr, OperationPtr.rangeInt, Buffed.Operation.rangeInt,
            add_nat_range_def, IsIncludedIN] at hio
          grind [ExArray.range_lower, ExArray.range_upper]
        have hresflat : ((res.toFlat ctx.spec : Nat) : Int) = op.toFlat + Buffed.Operation.Offsets.resultsInt op ctx.spec + ((res.index * 40 : Nat) : Int) := by
          rw [OpResultPtr.toFlat_ideal ctx.sim.repr res hresib]
          simp only [OpResultPtr.toFlatNat, heq, show Buffed.OpResult.sizeNat = 40 from rfl]
          omega
        have hres : ∀ (off : Int64) (n : Nat), off.toInt = n → n + 8 ≤ 40 →
            (Rewriter.setOperand opPtr.impl ctx.buf idx hnum hslot valuePtr.impl).mem.read64! (res.toM ctx.spec + off) = ctx.buf.mem.read64! (res.toM ctx.spec + off) := by
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
        have hres0 : (Rewriter.setOperand opPtr.impl ctx.buf idx hnum hslot valuePtr.impl).mem.read64! (res.toM ctx.spec) = ctx.buf.mem.read64! (res.toM ctx.spec) := by
          apply hread
          have hri1 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr hopib
          have hri2 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr opPtrInBounds.ib
          by_cases hcase : op = opPtr.spec
          · subst hcase
            grind [layout_grind]
          · have hdd := hd (by simp [hcase])
            simp only [TopLevelPtr.range, hri1, hri2, IsDisjointI, OperationPtr.rangeInt,
              Buffed.Operation.rangeInt, add_nat_range_def] at hdd
            grind [layout_grind]
        constructor
        · have := this.kind
          simp only [Buffed.OpResultMPtr.readKind!, hresmeq] at this ⊢
          rw [hres0]
          clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
          grind [layout_grind, Rewriter.pushOperand]
        · have := this.typee
          simp only [Buffed.OpResultMPtr.readType!, hattr, hresmeq] at this ⊢
          rw [hres Buffed.ValueImpl.Offsets.type 8 (by decide) (by decide)]
          clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
          grind [layout_grind, Rewriter.pushOperand]
        · have := this.firstUse
          simp only [Buffed.OpResultMPtr.readFirstUse!, hresmeq, hresget] at this ⊢
          rw [hres Buffed.ValueImpl.Offsets.firstUse 16 (by decide) (by decide)]
          clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
          grind [layout_grind, Rewriter.pushOperand]
        · have := this.index
          simp only [Buffed.OpResultMPtr.readIndex!, hresmeq, hresget] at this ⊢
          rw [hres Buffed.OpResult.Offsets.index 24 (by decide) (by decide)]
          clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
          grind [layout_grind, Rewriter.pushOperand]
        · have := this.owner
          simp only [Buffed.OpResultMPtr.readOwner!, hresmeq, hresget] at this ⊢
          rw [hres Buffed.OpResult.Offsets.owner 32 (by decide) (by decide)]
          clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt
          grind [layout_grind, Rewriter.pushOperand]
  · -- encoding_block
    simp only
    intros blk blkIb
    have hblkib : blk.InBounds ctx.spec := by
      clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt; (try clear hslot hnum)
      grind [Rewriter.pushOperand]
    have hbin := ctx.sim.in_bounds (.block blk) (by grind)
    have henc := ctx.sim.encoding_block blk (by grind)
    have hdd := ctx.sim.disjoint_allocs (.block blk) (.operation opPtr.spec) (by grind) (by grind) (by simp)
    have hbri := ctx.sim.repr.blocks_indices blk (by grind)
    have hareaBLK : Buffed.Block.Offsets.afterInt blk ctx.spec
        = 56 + (((blk.get! ctx.spec).capArguments * 40 : Nat) : Int) := by rfl
    have hblkM : (UInt64.toNat blk.toM : Int) = blk.toFlat := by
      simp only [BlockPtr.toM]
      grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', BlockPtr.toFlat, layout_grind]
    have haft := Sim.BlockPtr.after_lt_ctx (ctx := ctx) blk hblkib
    have hbget : blk.get! (Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind)) = blk.get! ctx.spec := by
      clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt; (try clear hslot hnum)
      grind [Rewriter.pushOperand]
    have hb8 : ∀ (off : Int64) (n : Nat), off.toInt = n → (n : Int) + 8 ≤ Buffed.Block.Offsets.afterInt blk ctx.spec →
        (Rewriter.setOperand opPtr.impl ctx.buf idx hnum hslot valuePtr.impl).mem.read64! (blk.toM + off) = ctx.buf.mem.read64! (blk.toM + off) := by
      intro off n hn hbnd
      apply hread
      have hri1 := BlockPtr.range_ideal ctx.sim.repr hblkib
      have hri2 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr opPtrInBounds.ib
      simp only [TopLevelPtr.range, hri1, hri2, IsDisjointI, BlockPtr.rangeInt, Buffed.Block.rangeInt,
        OperationPtr.rangeInt, Buffed.Operation.rangeInt, add_nat_range_def] at hdd
      rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind]
    constructor
    · constructor
      · have := henc.firstUse
        simp only [Buffed.BlockMPtr.readFirstUse!, hbget] at this ⊢
        rw [hb8 Buffed.Block.Offsets.firstUse 0 (by decide) (by simp only [hareaBLK]; omega)]
        clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt; (try clear hslot hnum)
        grind [layout_grind, Rewriter.pushOperand]
      · have := henc.prev
        simp only [Buffed.BlockMPtr.readPrev!, hbget] at this ⊢
        rw [hb8 Buffed.Block.Offsets.prev 8 (by decide) (by simp only [hareaBLK]; omega)]
        clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt; (try clear hslot hnum)
        grind [layout_grind, Rewriter.pushOperand]
      · have := henc.next
        simp only [Buffed.BlockMPtr.readNext!, hbget] at this ⊢
        rw [hb8 Buffed.Block.Offsets.next 16 (by decide) (by simp only [hareaBLK]; omega)]
        clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt; (try clear hslot hnum)
        grind [layout_grind, Rewriter.pushOperand]
      · have := henc.parent
        simp only [Buffed.BlockMPtr.readParent!, hbget] at this ⊢
        rw [hb8 Buffed.Block.Offsets.parent 24 (by decide) (by simp only [hareaBLK]; omega)]
        clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt; (try clear hslot hnum)
        grind [layout_grind, Rewriter.pushOperand]
      · have := henc.firstOp
        simp only [Buffed.BlockMPtr.readFirstOp!, hbget] at this ⊢
        rw [hb8 Buffed.Block.Offsets.firstOp 32 (by decide) (by simp only [hareaBLK]; omega)]
        clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt; (try clear hslot hnum)
        grind [layout_grind, Rewriter.pushOperand]
      · have := henc.lastOp
        simp only [Buffed.BlockMPtr.readLastOp!, hbget] at this ⊢
        rw [hb8 Buffed.Block.Offsets.lastOp 40 (by decide) (by simp only [hareaBLK]; omega)]
        clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt; (try clear hslot hnum)
        grind [layout_grind, Rewriter.pushOperand]
    · constructor
      · have := henc.numArguments
        simp only [Buffed.BlockMPtr.readNumArguments!, hbget] at this ⊢
        rw [hb8 Buffed.Block.Offsets.numArguments 48 (by decide) (by simp only [hareaBLK]; omega)]
        clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt; (try clear hslot hnum)
        grind [layout_grind, Rewriter.pushOperand]
      · intros arg argIn heq
        dsimp only at argIn
        have hargib : arg.InBounds ctx.spec := by
          clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt; (try clear hslot hnum)
          grind [Rewriter.pushOperand]
        have := henc.arguments arg (by grind) (by grind)
        have hargget : arg.get! (Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind)) = arg.get! ctx.spec := by
          clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt; (try clear hslot hnum)
          grind [Rewriter.pushOperand]
        have hargidx : arg.index < (blk.get! ctx.spec).capArguments := by
          clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt; (try clear hslot hnum)
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
            (Rewriter.setOperand opPtr.impl ctx.buf idx hnum hslot valuePtr.impl).mem.read64! (arg.toM + off) = ctx.buf.mem.read64! (arg.toM + off) := by
          intro off n hn h32
          apply hread
          have hri1 := BlockPtr.range_ideal ctx.sim.repr hblkib
          have hri2 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr opPtrInBounds.ib
          simp only [TopLevelPtr.range, hri1, hri2, IsDisjointI, BlockPtr.rangeInt, Buffed.Block.rangeInt,
            OperationPtr.rangeInt, Buffed.Operation.rangeInt, add_nat_range_def] at hdd
          rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind]
        have harg0 : (Rewriter.setOperand opPtr.impl ctx.buf idx hnum hslot valuePtr.impl).mem.read64! arg.toM = ctx.buf.mem.read64! arg.toM := by
          apply hread
          have hri1 := BlockPtr.range_ideal ctx.sim.repr hblkib
          have hri2 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr opPtrInBounds.ib
          simp only [TopLevelPtr.range, hri1, hri2, IsDisjointI, BlockPtr.rangeInt, Buffed.Block.rangeInt,
            OperationPtr.rangeInt, Buffed.Operation.rangeInt, add_nat_range_def] at hdd
          grind [layout_grind]
        constructor
        · have := this.kind
          simp only [Buffed.BlockArgumentMPtr.readKind!] at this ⊢
          rw [harg0]
          clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt; (try clear hslot hnum)
          grind [layout_grind, Rewriter.pushOperand]
        · have := this.type
          simp only [Buffed.BlockArgumentMPtr.readType!, hattr, hargget] at this ⊢
          rw [harg Buffed.ValueImpl.Offsets.type 8 (by decide) (by decide)]
          clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt; (try clear hslot hnum)
          grind [layout_grind, Rewriter.pushOperand]
        · have := this.firstUse
          simp only [Buffed.BlockArgumentMPtr.readFirstUse!, hargget] at this ⊢
          rw [harg Buffed.ValueImpl.Offsets.firstUse 16 (by decide) (by decide)]
          clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt; (try clear hslot hnum)
          grind [layout_grind, Rewriter.pushOperand]
        · have := this.index
          simp only [Buffed.BlockArgumentMPtr.readIndex!, hargget] at this ⊢
          rw [harg Buffed.BlockArgument.Offsets.index 24 (by decide) (by decide)]
          clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt; (try clear hslot hnum)
          grind [layout_grind, Rewriter.pushOperand]
        · have := this.owner
          simp only [Buffed.BlockArgumentMPtr.readOwner!, hargget] at this ⊢
          rw [harg Buffed.BlockArgument.Offsets.owner 32 (by decide) (by decide)]
          clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt; (try clear hslot hnum)
          grind [layout_grind, Rewriter.pushOperand]
  · -- encoding_region
    simp only
    intros rg rgIb
    have hrgib : rg.InBounds ctx.spec := by
      clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt; (try clear hslot hnum)
      grind [Rewriter.pushOperand]
    have hrin := ctx.sim.in_bounds (.region rg) (by grind)
    have henc := ctx.sim.encoding_region rg (by grind)
    have hdd := ctx.sim.disjoint_allocs (.region rg) (.operation opPtr.spec) (by grind) (by grind) (by simp)
    have hrgM : (UInt64.toNat rg.toM : Int) = rg.toFlat := by
      simp only [RegionPtr.toM]
      grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', RegionPtr.toFlat, layout_grind]
    have hrgget : rg.get! (Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind)) = rg.get! ctx.spec := by
      clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt; (try clear hslot hnum)
      grind [Rewriter.pushOperand]
    have hrg8 : ∀ (off : Int64) (n : Nat), off.toInt = n → n + 8 ≤ 24 →
        (Rewriter.setOperand opPtr.impl ctx.buf idx hnum hslot valuePtr.impl).mem.read64! (rg.toM + off) = ctx.buf.mem.read64! (rg.toM + off) := by
      intro off n hn h24
      apply hread
      have hri2 := OperationPtr.range_ideal (ctx := ctx.spec) ctx.sim.repr opPtrInBounds.ib
      simp only [TopLevelPtr.range, RegionPtr.range_ideal, hri2, IsDisjointI, RegionPtr.rangeInt,
        Buffed.Region.rangeInt, OperationPtr.rangeInt, Buffed.Operation.rangeInt, add_nat_range_def] at hdd
      rw [UInt64.uint64_add_int64_toNat_lt] <;> grind [layout_grind]
    constructor
    · have := henc.firstBlock
      simp only [Buffed.RegionMPtr.readFirstBlock!, hrgget] at this ⊢
      rw [hrg8 Buffed.Region.Offsets.firstBlock 0 (by decide) (by decide)]
      clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt; (try clear hslot hnum)
      grind [layout_grind, Rewriter.pushOperand]
    · have := henc.lastBlock
      simp only [Buffed.RegionMPtr.readLastBlock!, hrgget] at this ⊢
      rw [hrg8 Buffed.Region.Offsets.lastBlock 8 (by decide) (by decide)]
      clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt; (try clear hslot hnum)
      grind [layout_grind, Rewriter.pushOperand]
    · have := henc.parent
      simp only [Buffed.RegionMPtr.readParent!, hrgget] at this ⊢
      rw [hrg8 Buffed.Region.Offsets.parent 16 (by decide) (by decide)]
      clear hread hread32 hattr ek hoff hslotaddr husz hincl hmul hidxlt; (try clear hslot hnum)
      grind [layout_grind, Rewriter.pushOperand]
  · -- attr_empty: the slot writes leave the attribute table untouched
    (try dsimp only)
    rw [hattr]
    exact ctx.sim.attr_empty

end Veir
