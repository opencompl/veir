module

public import Veir.IR.Buffed.Basic
public import Veir.IR.Buffed.Frames
import all Veir.IR.Buffed.Basic

@[expose] public section
namespace Veir
open Buffed (countCard)
variable [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo]
set_option maxHeartbeats 1000000

theorem Sim.OperationPtr.allocReserved_sim {ctx : Sim.IRContext OpInfo} {opType : OpInfo}
    {props : HasOpInfo.propertiesOf opType}
    {numResults numOperands numBlockOperands numRegions : UInt64}
    {h₁ : numResults.toNat ≤ countCard} {h₂ : numOperands.toNat ≤ countCard}
    {h₃ : numBlockOperands.toNat ≤ countCard} {h₄ : numRegions.toNat ≤ countCard}
    {ctxBuf : Buffed.IRBufContext} {ptrImpl : Buffed.OperationMPtr}
    {ctxSpec : Veir.IRContext OpInfo} {ptrSpec : Veir.OperationPtr}
    (start : Nat)
    (hptn : ptrImpl.toNat = start + numResults.toNat * 40)
    (hsizele : ctx.buf.mem.size ≤ ctxBuf.mem.size)
    (hsize : start + (Buffed.OperationMPtr.computeOperationSize numResults numOperands
      numBlockOperands numRegions (Buffed.Operation.propertySize opType)).toNat ≤ ctxBuf.mem.size)
    (hattrs : ∀ {i : Nat} {a : Attribute}, ctx.buf.attributes[i]? = some a →
      ctxBuf.attributes[i]? = some a)
    (hagreeAll : ∀ (p : TopLevelPtr) (hp : p.InBounds ctx.spec),
      Buffed.AgreesOn ctxBuf ctx.buf (p.range ctx.spec).lower.toNat (p.range ctx.spec).upper.toNat)
    (hdisj : ∀ (p : TopLevelPtr), p.InBounds ctx.spec →
      (p.range ctx.spec).upper ≤ start ∨
      (start : Int) + (Buffed.OperationMPtr.computeOperationSize numResults numOperands
        numBlockOperands numRegions (Buffed.Operation.propertySize opType)).toNat ≤
        (p.range ctx.spec).lower)
    (hRnr : Buffed.OperationMPtr.readNumResults! ctxBuf ptrImpl = numResults)
    (hRno : Buffed.OperationMPtr.readNumOperands! ctxBuf ptrImpl = numOperands)
    (hRnb : Buffed.OperationMPtr.readNumBlockOperands! ctxBuf ptrImpl = numBlockOperands)
    (hRnrg : Buffed.OperationMPtr.readNumRegions! ctxBuf ptrImpl = numRegions)
    (hRprev : Buffed.OperationMPtr.readPrev! ctxBuf ptrImpl = Buffed.OperationOPtr.none)
    (hRnext : Buffed.OperationMPtr.readNext! ctxBuf ptrImpl = Buffed.OperationOPtr.none)
    (hRpar : Buffed.OperationMPtr.readParent! ctxBuf ptrImpl = Buffed.BlockOPtr.none)
    (hRty : Buffed.OperationMPtr.readOpType! ctxBuf ptrImpl = SerializableOpInfo.encode opType)
    (hRattrs : Buffed.OperationMPtr.readAttrs! ctxBuf ptrImpl = 0)
    (hrp : HasBuffedProperties.readPropertyAt opType
      (ptrImpl + Buffed.Operation.Offsets.properties) ctxBuf = some props)
    (hfreeValid : ctxBuf.freeList.Valid ctxBuf.mem.size)
    (hfreeOld : ∀ (s a : UInt64), a ∈ ctxBuf.freeList.bucket s →
      ∀ (p : TopLevelPtr), p.InBounds ctx.spec →
        (p.range ctx.spec).upper ≤ a.toNat ∨
          (a.toNat : Int) + s.toNat ≤ (p.range ctx.spec).lower)
    (hfreeNew : ∀ (s a : UInt64), a ∈ ctxBuf.freeList.bucket s →
      a.toNat + s.toNat ≤ start ∨
        start + (Buffed.OperationMPtr.computeOperationSize numResults numOperands
          numBlockOperands numRegions (Buffed.Operation.propertySize opType)).toNat ≤ a.toNat)
    (heqSpec : Veir.OperationPtr.allocEmptyAt ctx.spec opType props numResults.toNat
      numBlockOperands.toNat numRegions.toNat numOperands.toNat ptrImpl.toNat
      = some (ctxSpec, ptrSpec)) :
    Veir.Sim (OpInfo := OpInfo) ⟨ctxBuf, ctxSpec⟩ := by
  have hp : (Buffed.Operation.propertySize opType).toNat ≤ countCard :=
    Nat.le_of_lt HasDialectOpInfo.propertySize_small
  have hps : Buffed.Operation.propertySize opType = HasDialectOpInfo.propertySize opType := rfl
  have hnew : ptrSpec = ⟨ptrImpl.toNat⟩ := Veir.OperationPtr.allocEmptyAt_ptr_eq heqSpec
  subst hnew
  have hnewIb : (⟨ptrImpl.toNat⟩ : Veir.OperationPtr).InBounds ctxSpec :=
    Veir.OperationPtr.allocEmptyAt_new_inBounds heqSpec
  have hget : (⟨ptrImpl.toNat⟩ : Veir.OperationPtr).get! ctxSpec = Veir.Operation.empty opType props
      numResults.toNat numBlockOperands.toNat numRegions.toNat numOperands.toNat := by
    simpa using Veir.OperationPtr.get!_OperationPtr_allocEmptyAt
      (operation := (⟨ptrImpl.toNat⟩ : Veir.OperationPtr)) heqSpec
  have hgetTy : (⟨ptrImpl.toNat⟩ : Veir.OperationPtr).getOpType! ctxSpec = opType := by
    simpa using Veir.OperationPtr.getOpType!_OperationPtr_allocEmptyAt
      (operation := (⟨ptrImpl.toNat⟩ : Veir.OperationPtr)) heqSpec
  have hcapR : ((⟨ptrImpl.toNat⟩ : Veir.OperationPtr).get! ctxSpec).capResults = numResults.toNat := by
    rw [hget]; rfl
  have hcapO : ((⟨ptrImpl.toNat⟩ : Veir.OperationPtr).get! ctxSpec).capOperands = numOperands.toNat := by
    rw [hget]; rfl
  have hcapB : ((⟨ptrImpl.toNat⟩ : Veir.OperationPtr).get! ctxSpec).capBlockOperands
      = numBlockOperands.toNat := by rw [hget]; rfl
  have hcapRg : ((⟨ptrImpl.toNat⟩ : Veir.OperationPtr).get! ctxSpec).capRegions
      = numRegions.toNat := by rw [hget]; rfl
  have hlp : ctx.spec.LayoutPreserved ctxSpec := by
    have hni := Veir.OperationPtr.allocEmptyAt_not_inBounds heqSpec
    constructor
    · intro op hib
      have hne : op ≠ (⟨ptrImpl.toNat⟩ : Veir.OperationPtr) := by grind
      constructor <;>
        grind [Veir.OperationPtr.get!_OperationPtr_allocEmptyAt,
          Veir.OperationPtr.getOpType!_OperationPtr_allocEmptyAt]
    · intro blk hib
      grind [Veir.BlockPtr.LayoutPreserved, Veir.BlockPtr.get!_OperationPtr_allocEmptyAt]
  have hrgOld : ∀ (q : TopLevelPtr), q.InBounds ctx.spec → q.range ctxSpec = q.range ctx.spec := by
    intro q hq
    have hni := Veir.OperationPtr.allocEmptyAt_not_inBounds heqSpec
    cases q with
    | operation op =>
      have hne : op ≠ (⟨ptrImpl.toNat⟩ : Veir.OperationPtr) := by grind
      simpa [TopLevelPtr.range] using Veir.OperationPtr.range_OperationPtr_allocEmptyAt heqSpec hne
    | block bl =>
      simpa [TopLevelPtr.range] using
        Veir.BlockPtr.range_OperationPtr_allocEmptyAt (bl := bl) heqSpec
    | region rg => rfl
  have hfits := ctxBuf.mem.fits_in_memory
  have hfits₀ := ctx.buf.mem.fits_in_memory
  have hszdec := Buffed.OperationMPtr.computeOperationSize_toNat numResults numOperands
    numBlockOperands numRegions (Buffed.Operation.propertySize opType) h₁ h₂ h₃ h₄ hp
  simp only [show Buffed.OpResult.size.toNat = 40 from rfl,
    show Buffed.ptrSize.toNat = 8 from rfl,
    show Buffed.Operation.sizeBase.toNat = 72 from rfl,
    Int64.maxNatValue] at hszdec hsize hptn hfits hfits₀
  have hfib' := IRContext.fieldsInBounds_OperationPtr_allocEmptyAt heqSpec ctx.sim.fieldsInBounds
  have hrepr' := IRContext.isRepr_OperationPtr_allocEmptyAt heqSpec ctx.sim.repr
    (by simp only [Int64.maxNatValue]; omega) h₁ h₂ h₃ h₄
  constructor
  · exact hfib'
  · exact hrepr'
  · -- `in_bounds`
    intro ptr ib
    rcases (Veir.OperationPtr.allocEmptyAt_topLevelPtr_iff ptr heqSpec).mp ib with hold | rfl
    · have hin := ctx.sim.in_bounds ptr hold
      cases ptr with
      | operation op =>
        have hne : op ≠ (⟨ptrImpl.toNat⟩ : Veir.OperationPtr) := by
          have := Veir.OperationPtr.allocEmptyAt_not_inBounds heqSpec
          grind
        have hrg := Veir.OperationPtr.range_OperationPtr_allocEmptyAt heqSpec hne
        simp only [TopLevelPtr.range] at hin ⊢
        rw [hrg]
        grind [IsIncludedIN, ExArray.range_def]
      | block bl =>
        have hrg := Veir.BlockPtr.range_OperationPtr_allocEmptyAt (bl := bl) heqSpec
        simp only [TopLevelPtr.range] at hin ⊢
        rw [hrg]
        grind [IsIncludedIN, ExArray.range_def]
      | region rg =>
        simp only [TopLevelPtr.range] at hin ⊢
        grind [IsIncludedIN, ExArray.range_def]
    · -- the freshly allocated operation: its range is exactly the block just appended
      clear hRnr hRno hRnb hRnrg hRprev hRnext hRpar hRty hRattrs
      simp only [TopLevelPtr.range, Veir.OperationPtr.range_ideal hrepr' hnewIb,
        Veir.OperationPtr.rangeInt, Buffed.Operation.rangeInt, add_nat_range_def,
        Veir.OperationPtr.toFlat, IsIncludedIN, ExArray.range_def]
      grind
  · -- `disjoint_allocs`
    clear hRnr hRno hRnb hRnrg hRprev hRnext hRpar hRty hRattrs
    have hnewRange : ∀ (q : TopLevelPtr), q.InBounds ctx.spec →
        IsDisjointI (q.range ctxSpec)
          ((TopLevelPtr.operation (⟨ptrImpl.toNat⟩ : Veir.OperationPtr)).range ctxSpec) := by
      intro q hq
      have hd := hdisj q hq
      rw [hrgOld q hq]
      simp only [TopLevelPtr.range, Veir.OperationPtr.range_ideal hrepr' hnewIb,
        Veir.OperationPtr.rangeInt, Buffed.Operation.rangeInt, add_nat_range_def,
        Veir.OperationPtr.toFlat, IsDisjointI]
      grind
    intro q₁ q₂ ib₁ ib₂ hne
    rcases (Veir.OperationPtr.allocEmptyAt_topLevelPtr_iff q₁ heqSpec).mp ib₁ with h₁old | rfl <;>
      rcases (Veir.OperationPtr.allocEmptyAt_topLevelPtr_iff q₂ heqSpec).mp ib₂ with h₂old | rfl
    · have := ctx.sim.disjoint_allocs q₁ q₂ h₁old h₂old hne
      rw [hrgOld q₁ h₁old, hrgOld q₂ h₂old]
      exact this
    · exact hnewRange q₁ h₁old
    · have := hnewRange q₂ h₂old
      grind [IsDisjointI]
    · exact absurd rfl hne
  · -- `encoding_op`
    intro op ib
    rcases (Veir.OperationPtr.allocEmptyAt_operationPtr_iff op heqSpec).mp ib with hold | rfl
    · -- existing operation: frame each record over the untouched prefix
      have hni := Veir.OperationPtr.allocEmptyAt_not_inBounds heqSpec
      have hne : op ≠ (⟨ptrImpl.toNat⟩ : Veir.OperationPtr) := by grind
      have hagree := hagreeAll (.operation op) hold
      have henc := ctx.sim.encoding_op op hold
      have hrange := Veir.Sim.OperationPtr.range_linear (ctx := ctx) op hold
      have hget2 : Veir.OperationPtr.get! op ctxSpec = Veir.OperationPtr.get! op ctx.spec := by
        grind [Veir.OperationPtr.get!_OperationPtr_allocEmptyAt]
      constructor
      · refine OperationPtr.matchesBase_frame ctx op hold henc.toMatchesBase
          (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat])) hlp (by rw [hget2]) (by rw [hget2])
          (by rw [hget2]) (by rw [hget2])
          (by grind [Veir.OperationPtr.getOpType!_OperationPtr_allocEmptyAt])
          (Veir.OperationPtr.getProperties!_eq_of_OperationPtr_get!_eq hget2) ib
      · constructor
        · exact OperationPtr.numBlockOperands_frame ctx op hold henc.numBlockOperands
            (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat])) (by rw [hget2])
        · intro bo boIb heq
          have hboIb : bo.InBounds ctx.spec := by grind [Veir.BlockOperandPtr.inBounds_def]
          have hincl := Veir.Sim.BlockOperandPtr.slot_included (ctx := ctx) bo hboIb
          have hpib := Veir.Sim.BlockOperandPtr.op_inBounds hboIb
          have hprangeS := Veir.Sim.OperationPtr.range_linear (ctx := ctx) bo.op hpib
          refine BlockOperandPtr.matches_frame ctx bo hboIb (henc.blockOperands bo hboIb heq)
            (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat])) hlp (by grind [layout_grind]) boIb
      · constructor
        · exact OperationPtr.numRegions_frame ctx op hold henc.numRegions
            (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat])) (by rw [hget2])
        · intro idx idxIn
          have hnr : idx < op.getNumRegions! ctx.spec := by
            grind [Veir.OperationPtr.getNumRegions!_OperationPtr_allocEmptyAt]
          have hcap := ctx.sim.repr.operations_indices op hold |>.capRegions
          refine OperationPtr.nthRegion_frame ctx op hold idx hnr (henc.regions idx hnr)
            (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat])) ?_ (by grind [layout_grind])
          have hidxc : idx < (op.get! ctx.spec).capRegions := by grind
          have haddrR : (op.toM.toNat : Int) = op.id := by
            grind [Veir.OperationPtr.toM, Veir.OperationPtr.toFlat]
          have hincl := OperationPtr.nthRegion_range_included_op_range ctx op idx.toUInt64 (by grind) hold
          exact hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, UInt64.toNat_ofNat'])
      · constructor
        · exact OperationPtr.numOperands_frame ctx op hold henc.numOperands
            (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat])) (by rw [hget2])
        · intro oper operIb heq
          have hooIb : oper.InBounds ctx.spec := by grind [Veir.OpOperandPtr.inBounds_def]
          have hincl := Veir.Sim.OpOperandPtr.slot_included (ctx := ctx) oper hooIb
          have hpib := Veir.Sim.OpOperandPtr.op_inBounds hooIb
          have hprangeS := Veir.Sim.OperationPtr.range_linear (ctx := ctx) oper.op hpib
          refine OpOperandPtr.matches_frame ctx oper hooIb (henc.operands oper hooIb heq)
            (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat])) hlp (by grind [layout_grind]) operIb
      · constructor
        · exact OperationPtr.numResults_frame ctx op hold henc.numResults
            (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat])) (by rw [hget2])
        · intro res resIb heq
          have hresIb : res.InBounds ctx.spec := by grind [Veir.OpResultPtr.inBounds_def]
          have hincl := Veir.Sim.OpResultPtr.slot_included (ctx := ctx) res hresIb
          have hpib := Veir.Sim.OpResultPtr.op_inBounds hresIb
          have hprangeS := Veir.Sim.OperationPtr.range_linear (ctx := ctx) res.op hpib
          refine OpResultPtr.matches_frame ctx res hresIb (henc.results res hresIb heq)
            (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat])) hlp (by grind [layout_grind]) resIb
    · -- the freshly allocated operation: every field reads back what `allocEmptyImpl` wrote
      have hnewToM : (⟨ptrImpl.toNat⟩ : Veir.OperationPtr).toM = ptrImpl := by
        simp [Veir.OperationPtr.toM, Veir.OperationPtr.toFlat]
      constructor
      · constructor
        · grind [Buffed.OperationMPtr.readPrev!, Veir.Operation.empty,
            Veir.OperationPtr.toO]
        · grind [Buffed.OperationMPtr.readNext!, Veir.Operation.empty,
            Veir.OperationPtr.toO]
        · grind [Buffed.OperationMPtr.readParent!, Veir.Operation.empty,
            Veir.BlockPtr.toO]
        · grind [SerializableOpInfo.decode_encode]
        · -- `attrs`: the zero-initialized index denotes the canonical empty dictionary
          have hae := ctx.sim.attr_empty
          rw [hnewToM, hRattrs, hget]
          exact hattrs (by simpa [Veir.Operation.empty] using hae)
        · -- `props`: the property slot reads back what `writePropertyAt` wrote
          have hgp : (⟨ptrImpl.toNat⟩ : Veir.OperationPtr).getProperties! ctxSpec opType = props := by
            rw [Veir.OperationPtr.getProperties!_OperationPtr_allocEmptyAt heqSpec, if_pos rfl]
          rw [hgetTy, hnewToM, hgp]
          exact hrp
      · constructor
        · grind
        · intro bo boIb heq
          exact absurd boIb (Veir.BlockOperandPtr.allocEmptyAt_no_operands heqSpec heq)
      · constructor
        · grind
        · intro idx idxIn
          grind
      · constructor
        · grind
        · intro oper operIb heq
          exact absurd operIb (Veir.OpOperandPtr.allocEmptyAt_no_operands heqSpec heq)
      · constructor
        · grind
        · intro res resIb heq
          exact absurd resIb (Veir.OpResultPtr.allocEmptyAt_no_results heqSpec heq)
  · -- `encoding_block`: every block is old; frame each record over the untouched prefix.
    intro blk blkIb
    have hold : blk.InBounds ctx.spec := by
      have := (Veir.OperationPtr.allocEmptyAt_topLevelPtr_iff (.block blk) heqSpec).mp (by grind)
      grind
    have hagree := hagreeAll (.block blk) hold
    have hrg := Veir.BlockPtr.range_ideal ctx.sim.repr hold
    have henc := ctx.sim.encoding_block blk hold
    have hrange := Veir.Sim.BlockPtr.range_linear (ctx := ctx) blk hold
    have hget2 : Veir.BlockPtr.get! blk ctxSpec = Veir.BlockPtr.get! blk ctx.spec := by
      grind [Veir.BlockPtr.get!_OperationPtr_allocEmptyAt]
    constructor
    · refine BlockPtr.matchesBase_frame ctx blk hold henc.toMatchesBase
        (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat])) hlp (by rw [hget2]) (by rw [hget2])
        (by rw [hget2]) (by rw [hget2]) (by rw [hget2]) (by rw [hget2]) blkIb
    · constructor
      · exact BlockPtr.numArguments_frame ctx blk hold henc.numArguments
          (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat])) (by rw [hget2])
      · intro arg argIn heq
        have hargIb : arg.InBounds ctx.spec := by grind [Veir.BlockArgumentPtr.inBounds_def]
        have hincl := Veir.Sim.BlockArgumentPtr.slot_included (ctx := ctx) arg hargIb
        have hpib := Veir.Sim.BlockArgumentPtr.block_inBounds hargIb
        have hprangeS := Veir.Sim.BlockPtr.range_linear (ctx := ctx) arg.block hpib
        refine BlockArgumentPtr.matches_frame ctx arg hargIb (henc.arguments arg hargIb heq)
          (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat])) hlp (by grind [layout_grind]) argIn
  · -- `encoding_region`: every region is old; frame the 24-byte record.
    intro rg rgIb
    have hold : rg.InBounds ctx.spec := by
      have := (Veir.OperationPtr.allocEmptyAt_topLevelPtr_iff (.region rg) heqSpec).mp (by grind)
      grind
    have hagree := hagreeAll (.region rg) hold
    have hrg := Veir.RegionPtr.range_ideal (rg := rg)
    have henc := ctx.sim.encoding_region rg hold
    have hrange := Veir.Sim.RegionPtr.range_linear (ctx := ctx) rg hold
    refine RegionPtr.matches_frame ctx rg hold henc
      (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat])) hlp (by grind [layout_grind]) rgIb
  · -- `attr_empty`
    exact hattrs ctx.sim.attr_empty

  · exact hfreeValid
  · intro size address hm p hp
    rcases (Veir.OperationPtr.allocEmptyAt_topLevelPtr_iff p heqSpec).mp hp with hold | rfl
    · rw [hrgOld p hold]
      exact hfreeOld size address hm p hold
    · have hd := hfreeNew size address hm
      simp only [TopLevelPtr.range, Veir.OperationPtr.range_ideal hrepr' hnewIb,
        Veir.OperationPtr.rangeInt, Buffed.Operation.rangeInt, add_nat_range_def,
        Veir.OperationPtr.toFlat]
      grind

end Veir
