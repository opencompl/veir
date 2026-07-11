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

/-! Rewriter simulation proofs -/

@[expose] public section
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
    simp only [Sim.OperationPtr.Sim_def, OperationPtr.toM] at this
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
  have hlay : ctx.spec.LayoutPreserved (Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind)) :=
    IRContext.LayoutPreserved.of_layoutUnchanged_ltr (by grind [Rewriter.pushOperand])
  -- The four writes stay inside the fresh 32-byte slot; any window disjoint from it agrees.
  have hagreeD : ∀ lo hi : Nat,
      (hi ≤ (opPtr.impl + Buffed.OperationMPtr.computeOperandOffset ctx.buf opPtr.impl idx hnum).toNat
       ∨ (opPtr.impl + Buffed.OperationMPtr.computeOperandOffset ctx.buf opPtr.impl idx hnum).toNat + 32 ≤ lo) →
      Buffed.AgreesOn (Rewriter.setOperand opPtr.impl ctx.buf idx hnum hslot valuePtr.impl) ctx.buf lo hi :=
    fun lo hi hd => ⟨fun a h1 h2 => hread a (by omega), fun a h1 h2 => hread32 a (by omega), fun _ _ h => by simp only [hattr]; exact h⟩
  constructor
  · -- fieldsInBounds
    have hofib : OpOperand.FieldsInBounds
        { value := valuePtr.spec, owner := opPtr.spec,
          back := OpOperandPtrPtr.valueFirstUse valuePtr.spec, nextUse := none } ctx.spec := by
      constructor <;> grind
    clear hread hread32 hattr ek hagreeD
    grind [Rewriter.pushOperand]
  · -- repr
    clear hread hread32 hattr ek hagreeD
    grind [Rewriter.pushOperand, layout_grind]
  · -- in_bounds
    simp only
    intros gptr gptrIb
    clear hread hread32 hattr ek hagreeD
    have := ctx.sim.in_bounds gptr (by grind [Rewriter.pushOperand])
    grind [TopLevelPtr, Rewriter.pushOperand, Rewriter.setOperand]
  · -- disjoint_allocs
    simp only
    clear hread hread32 hattr ek hagreeD
    have := ctx.sim.disjoint_allocs
    grind [TopLevelPtr, Rewriter.pushOperand]
  · -- encoding_op
    simp only
    intros op opIb
    have hopib : op.InBounds ctx.spec := by
      clear hread hread32 hattr ek hagreeD hoff hslotaddr husz hincl hmul hidxlt
      grind [Rewriter.pushOperand]
    have henc := ctx.sim.encoding_op op hopib
    have hrrange := Veir.Sim.OperationPtr.range_linear (ctx := ctx) op hopib
    have hwrange := Veir.Sim.OperationPtr.range_linear (ctx := ctx) opPtr.spec opPtrInBounds.ib
    have hdisj := fun hne : op ≠ opPtr.spec =>
      Veir.Sim.disjoint_operation_operation (ctx := ctx) op opPtr.spec hopib opPtrInBounds.ib hne
    have hareaOP : Buffed.Operation.Offsets.operandsInt op ctx.spec
        = 72 + ((Buffed.Operation.propertySize (op.getOpType! ctx.spec)).toNat : Int) := by rfl
    have hopM : (UInt64.toNat op.toM : Int) = op.toFlat := by
      simp only [OperationPtr.toM]
      grind [Nat.toUInt64_eq, UInt64.toNat_ofNat', OperationPtr.toFlat, layout_grind]
    have hgets : ((op.get! (Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind))).prev = (op.get! ctx.spec).prev
        ∧ (op.get! (Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind))).next = (op.get! ctx.spec).next
        ∧ (op.get! (Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind))).parent = (op.get! ctx.spec).parent
        ∧ (op.get! (Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind))).attrs = (op.get! ctx.spec).attrs
        ∧ op.getOpType! (Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind)) = op.getOpType! ctx.spec
        ∧ (op.get! (Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind))).capBlockOperands = (op.get! ctx.spec).capBlockOperands
        ∧ (op.get! (Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind))).capRegions = (op.get! ctx.spec).capRegions
        ∧ (op.get! (Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind))).capOperands = (op.get! ctx.spec).capOperands
        ∧ (op.get! (Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind))).capResults = (op.get! ctx.spec).capResults) := by
      clear hread hread32 hattr ek hagreeD hoff hslotaddr husz hincl hmul hidxlt
      grind [Rewriter.pushOperand]
    obtain ⟨hgprev, hgnext, hgpar, hgattrs, hgty, hgcB, hgcRg, hgcO, hgcR⟩ := hgets
    constructor
    · -- MatchesBase: framed — the write lands in the operand array, past the 72-byte header.
      refine OperationPtr.matchesBase_frame ctx op hopib henc.toMatchesBase (hagreeD _ _ ?_) hlay
        hgprev hgnext hgpar hgattrs hgty opIb
      clear hread hread32 hattr ek hagreeD hoff husz hmul hidxlt
      grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
        Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
        _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
        _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
    · constructor
      · refine OperationPtr.numBlockOperands_frame ctx op hopib henc.numBlockOperands (hagreeD _ _ ?_) hgcB
        clear hread hread32 hattr ek hagreeD hoff husz hmul hidxlt
        grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
          Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
          _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
          _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
      · intros bo boIb heq
        dsimp only at boIb
        have hboib : bo.InBounds ctx.spec := by
          clear hread hread32 hattr ek hagreeD hoff hslotaddr husz hincl hmul hidxlt
          grind [Rewriter.pushOperand]
        have hbincl := Veir.Sim.BlockOperandPtr.slot_included (ctx := ctx) bo hboib
        have hboget : bo.get! (Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind)) = bo.get! ctx.spec := by
          clear hread hread32 hattr ek hagreeD hoff hslotaddr husz hincl hmul hidxlt
          grind [Rewriter.pushOperand]
        refine BlockOperandPtr.matches_frame ctx bo hboib (henc.blockOperands bo hboib heq)
          (hagreeD _ _ ?_) hlay hboget boIb
        clear hread hread32 hattr ek hagreeD hoff husz hmul hidxlt
        grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
          Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
          _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
          _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
    · constructor
      · refine OperationPtr.numRegions_frame ctx op hopib henc.numRegions (hagreeD _ _ ?_) hgcRg
        clear hread hread32 hattr ek hagreeD hoff husz hmul hidxlt
        grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
          Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
          _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
          _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
      · intros ridx ridxIn
        dsimp only at ridxIn
        have hnr : ridx < op.getNumRegions! ctx.spec := by
          clear hread hread32 hattr ek hagreeD hoff hslotaddr husz hincl hmul hidxlt
          grind [Rewriter.pushOperand]
        have hcapr := ctx.sim.repr.operations_indices op hopib |>.capRegions
        refine OperationPtr.nthRegion_frame ctx op hopib ridx hnr (henc.regions ridx hnr)
          (hagreeD _ _ ?_) ?_
          (by clear hread hread32 hattr ek hagreeD hoff hslotaddr husz hincl hmul hidxlt
              grind [Rewriter.pushOperand])
        · clear hread hread32 hattr ek hagreeD hoff husz hmul hidxlt
          grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
        · have hidxc : ridx < (op.get! ctx.spec).capRegions := by
            clear hread hread32 hattr ek hagreeD
            grind
          have haddrR : ((op.toM.toNat : Nat) : Int) = op.id := by
            grind [Veir.OperationPtr.toM, _root_.Veir.OperationPtr.toFlat]
          have hcntr := ctx.sim.repr.operations_indices op hopib |>.regions
          have hincl2 := OperationPtr.nthRegion_range_included_op_range ctx op ridx.toUInt64
            (by clear hread hread32 hattr ek hagreeD hoff husz hmul hidxlt
                grind [UInt64.toNat_ofNat']) hopib
          refine hagreeD _ _ ?_
          clear hread hread32 hattr ek hagreeD hoff husz hmul hidxlt
          grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
              Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
              _root_.Veir.OperationPtr.toFlat, UInt64.toNat_ofNat']
    · constructor
      · refine OperationPtr.numOperands_frame ctx op hopib henc.numOperands (hagreeD _ _ ?_) hgcO
        clear hread hread32 hattr ek hagreeD hoff husz hmul hidxlt
        grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
          Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
          _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
          _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
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
            exact (Sim.OptionOpOperandPtr.Sim_def _ _).mpr rfl
          · -- back
            simp only [Buffed.OpOperandMPtr.readBack!, hnMeq, hnget, Rewriter.setOperand,
              Buffed.OpOperandMPtr.writeValue, Buffed.OpOperandMPtr.writeOwner,
              Buffed.OpOperandMPtr.writeBack, Buffed.OpOperandMPtr.writeNextUse]
            rw [ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have h1 := ek Buffed.OpOperand.Offsets.value 24 (by decide) (by decide); have h2 := ek Buffed.OpOperand.Offsets.back 8 (by decide) (by decide); omega),
              ExArray.read64!_blit64_disjoint _ _ _ _ _ (by simp only [IsDisjoint]; have h1 := ek Buffed.OpOperand.Offsets.owner 16 (by decide) (by decide); have h2 := ek Buffed.OpOperand.Offsets.back 8 (by decide) (by decide); omega),
              ExArray.read64!_blit64_self]
            have hvaft := Sim.ValuePtr.after_lt_ctx (ctx := ctx) valuePtr.spec valueInBounds.ib
            have hvM := valueInBounds.sim
            simp only [Sim.ValuePtr.Sim_def] at hvM
            have hvflatP : valuePtr.spec.toFlat (Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind)) = valuePtr.spec.toFlat ctx.spec := by
              clear hread hread32 hattr ek hagreeD hoff hslotaddr husz hincl hmul hidxlt
              (try clear hnMeq hnflat); (try clear hslot hnum)
              grind [Veir.ValuePtr.toFlat, Veir.OpResultPtr.toFlat, Veir.BlockArgumentPtr.toFlat,
                Rewriter.pushOperand]
            have hvMnat : (UInt64.toNat valuePtr.impl : Int) = valuePtr.spec.toFlat ctx.spec := by
              rw [← hvM]
              simp only [Veir.ValuePtr.toM]
              clear hread hread32 hattr ek hagreeD hoff hslotaddr husz hincl hmul hidxlt
              (try clear hnMeq hnflat); (try clear hslot hnum)
              grind [Nat.toUInt64_eq, UInt64.toNat_ofNat']
            have hbackM : (OpOperandPtrPtr.valueFirstUse valuePtr.spec).toM (Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind))
                = valuePtr.impl + Buffed.ValueImpl.Offsets.firstUse := by
              simp only [Veir.OpOperandPtrPtr.toM, Veir.OpOperandPtrPtr.toFlat, hvflatP]
              have h2 : (valuePtr.impl + Buffed.ValueImpl.Offsets.firstUse).toNat = UInt64.toNat valuePtr.impl + 16 := by
                rw [UInt64.uint64_add_int64_toNat_lt] <;>
                  (clear hread hread32 hattr ek hagreeD hoff hslotaddr husz hincl hmul hidxlt;
                   (try clear hnMeq hnflat); (try clear hslot hnum);
                   grind [show Buffed.ValueImpl.Offsets.firstUse.toInt = 16 from rfl,
                     show Buffed.ValueImpl.Offsets.afterInt = 24 from rfl])
              clear hread hread32 hattr ek hagreeD hoff hslotaddr husz hincl hmul hidxlt
              (try clear hnMeq hnflat); (try clear hslot hnum)
              grind [Nat.toUInt64_eq, UInt64.toNat_ofNat',
                show Buffed.ValueImpl.Offsets.firstUse.toInt = 16 from rfl,
                show Buffed.ValueImpl.Offsets.afterInt = 24 from rfl]
            simp only [Sim.OpOperandPtrPtr.Sim_def]
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
            simp only [Sim.ValuePtr.Sim_def] at hvM ⊢
            have hvflatP : valuePtr.spec.toFlat (Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind)) = valuePtr.spec.toFlat ctx.spec := by
              clear hread hread32 hattr ek hagreeD hoff hslotaddr husz hincl hmul hidxlt
              (try clear hnMeq hnflat); (try clear hslot hnum)
              grind [Veir.ValuePtr.toFlat, Veir.OpResultPtr.toFlat, Veir.BlockArgumentPtr.toFlat,
                Rewriter.pushOperand]
            (try dsimp only)
            simp only [Veir.ValuePtr.toM, hvflatP]
            rw [← hvM]
            rfl
        · -- pre-existing operand: framed — its slot sits strictly below the written one.
          have hoperib : oper.InBounds ctx.spec := by
            clear hread hread32 hattr ek hagreeD hoff hslotaddr husz hincl hmul hidxlt
            grind [Rewriter.pushOperand]
          have hoincl := Veir.Sim.OpOperandPtr.slot_included (ctx := ctx) oper hoperib
          have hoidx : op = opPtr.spec → oper.index < idx.toNat := by
            clear hread hread32 hattr ek hagreeD hoff hslotaddr husz hincl hmul hidxlt
            intro hop
            grind [Veir.OpOperandPtr.inBounds_def]
          have hoperflat : ((oper.toFlatNat ctx.spec : Nat) : Int)
              = op.toFlat + Buffed.Operation.Offsets.operandsInt op ctx.spec + ((oper.index * 32 : Nat) : Int) := by
            simp only [OpOperandPtr.toFlatNat, heq, show Buffed.OpOperand.sizeNat = 32 from rfl]
            have h0 : (0:Int) ≤ op.toFlat + Buffed.Operation.Offsets.operandsInt op ctx.spec := by
              rw [hareaOP]
              omega
            omega
          have hoperget : oper.get! (Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind)) = oper.get! ctx.spec := by
            clear hread hread32 hattr ek hagreeD hoff hslotaddr husz hincl hmul hidxlt
            grind [Rewriter.pushOperand]
          refine OpOperandPtr.matches_frame ctx oper hoperib (henc.operands oper hoperib heq)
            (hagreeD _ _ ?_) hlay hoperget operIb
          clear hread hread32 hattr ek hagreeD hoff husz hmul hidxlt
          grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
            Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
            _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
            _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
    · constructor
      · refine OperationPtr.numResults_frame ctx op hopib henc.numResults (hagreeD _ _ ?_) hgcR
        clear hread hread32 hattr ek hagreeD hoff husz hmul hidxlt
        grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
          Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
          _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
          _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
      · intros res resIb heq
        dsimp only at resIb
        have hresib : res.InBounds ctx.spec := by
          clear hread hread32 hattr ek hagreeD hoff hslotaddr husz hincl hmul hidxlt
          grind [Rewriter.pushOperand]
        have hrincl := Veir.Sim.OpResultPtr.slot_included (ctx := ctx) res hresib
        have hresget : res.get! (Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind)) = res.get! ctx.spec := by
          clear hread hread32 hattr ek hagreeD hoff hslotaddr husz hincl hmul hidxlt
          grind [Rewriter.pushOperand]
        refine OpResultPtr.matches_frame ctx res hresib (henc.results res hresib heq)
          (hagreeD _ _ ?_) hlay hresget resIb
        clear hread hread32 hattr ek hagreeD hoff husz hmul hidxlt
        grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
          Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
          _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
          _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
  · -- encoding_block
    simp only
    intros blk blkIb
    have hblkib : blk.InBounds ctx.spec := by
      clear hread hread32 hattr ek hagreeD hoff hslotaddr husz hincl hmul hidxlt
      grind [Rewriter.pushOperand]
    have henc := ctx.sim.encoding_block blk hblkib
    have hbrange := Veir.Sim.BlockPtr.range_linear (ctx := ctx) blk hblkib
    have hwrange := Veir.Sim.OperationPtr.range_linear (ctx := ctx) opPtr.spec opPtrInBounds.ib
    have hdisjB := Veir.Sim.disjoint_block_operation (ctx := ctx) blk opPtr.spec hblkib opPtrInBounds.ib
    have hbget : blk.get! (Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind)) = blk.get! ctx.spec := by
      clear hread hread32 hattr ek hagreeD hoff hslotaddr husz hincl hmul hidxlt
      grind [Rewriter.pushOperand]
    constructor
    · refine BlockPtr.matchesBase_frame ctx blk hblkib henc.toMatchesBase (hagreeD _ _ ?_) hlay
        (by rw [hbget]) (by rw [hbget]) (by rw [hbget]) (by rw [hbget]) (by rw [hbget]) (by rw [hbget]) blkIb
      clear hread hread32 hattr ek hagreeD hoff husz hmul hidxlt
      grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
        Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
        _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
        _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
    · constructor
      · refine BlockPtr.numArguments_frame ctx blk hblkib henc.numArguments (hagreeD _ _ ?_) (by rw [hbget])
        clear hread hread32 hattr ek hagreeD hoff husz hmul hidxlt
        grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
          Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
          _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
          _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
      · intros arg argIn heq
        dsimp only at argIn
        have hargib : arg.InBounds ctx.spec := by
          clear hread hread32 hattr ek hagreeD hoff hslotaddr husz hincl hmul hidxlt
          grind [Rewriter.pushOperand]
        have haincl := Veir.Sim.BlockArgumentPtr.slot_included (ctx := ctx) arg hargib
        have hargget : arg.get! (Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind)) = arg.get! ctx.spec := by
          clear hread hread32 hattr ek hagreeD hoff hslotaddr husz hincl hmul hidxlt
          grind [Rewriter.pushOperand]
        refine BlockArgumentPtr.matches_frame ctx arg hargib (henc.arguments arg hargib heq)
          (hagreeD _ _ ?_) hlay hargget argIn
        clear hread hread32 hattr ek hagreeD hoff husz hmul hidxlt
        grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
          Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
          _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
          _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
  · -- encoding_region
    simp only
    intros rg rgIb
    have hrgib : rg.InBounds ctx.spec := by
      clear hread hread32 hattr ek hagreeD hoff hslotaddr husz hincl hmul hidxlt
      grind [Rewriter.pushOperand]
    have henc := ctx.sim.encoding_region rg hrgib
    have hrgrange := Veir.Sim.RegionPtr.range_linear (ctx := ctx) rg hrgib
    have hwrange := Veir.Sim.OperationPtr.range_linear (ctx := ctx) opPtr.spec opPtrInBounds.ib
    have hdisjR := Veir.Sim.disjoint_region_operation (ctx := ctx) rg opPtr.spec hrgib opPtrInBounds.ib
    have hrgget : rg.get! (Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind)) = rg.get! ctx.spec := by
      clear hread hread32 hattr ek hagreeD hoff hslotaddr husz hincl hmul hidxlt
      grind [Rewriter.pushOperand]
    refine RegionPtr.matches_frame ctx rg hrgib henc (hagreeD _ _ ?_) hlay hrgget rgIb
    clear hread hread32 hattr ek hagreeD hoff husz hmul hidxlt
    grind (splits := 6) only [isDisjointI_def, IsIncludedI, add_nat_range_def,
      Veir.Buffed.uint64_add_int64_toNat, Veir.Sim.IRContext.inner_def,
      _root_.Veir.OperationPtr.toFlat, _root_.Veir.BlockPtr.toFlat, _root_.Veir.RegionPtr.toFlat,
      _root_.Veir.BlockPtr.rangeInt, _root_.Veir.RegionPtr.rangeInt]
  · -- attr_empty: the slot writes leave the attribute table untouched
    (try dsimp only)
    rw [hattr]
    exact ctx.sim.attr_empty

end Veir


