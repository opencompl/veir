module

public import Veir.IR.Buffed.Frames
public import Veir.IR.Buffed.Basic
import all Veir.IR.Buffed.Basic

@[expose] public section
namespace Veir
variable [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo]
set_option maxHeartbeats 1000000

theorem Sim.RegionPtr.allocReserved_sim (ctx : Sim.IRContext OpInfo)
    {ctxBuf : Buffed.IRBufContext} {ptrImpl : Buffed.RegionMPtr}
    (hsizele : ctx.buf.mem.size ≤ ctxBuf.mem.size)
    (hsize : ptrImpl.toNat + 24 ≤ ctxBuf.mem.size)
    (hattr : ctxBuf.attributes = ctx.buf.attributes)
    (hagreeAll : ∀ (p : TopLevelPtr), p.InBounds ctx.spec →
      Buffed.AgreesOn ctxBuf ctx.buf (p.range ctx.spec).lower.toNat (p.range ctx.spec).upper.toNat)
    (hdisj : ∀ (p : TopLevelPtr), p.InBounds ctx.spec →
      (p.range ctx.spec).upper ≤ ptrImpl.toNat ∨
        (ptrImpl.toNat : Int) + 24 ≤ (p.range ctx.spec).lower)
    (hfirst : Buffed.RegionMPtr.readFirstBlock! ctxBuf ptrImpl = Buffed.BlockOPtr.none)
    (hlast : Buffed.RegionMPtr.readLastBlock! ctxBuf ptrImpl = Buffed.BlockOPtr.none)
    (hparent : Buffed.RegionMPtr.readParent! ctxBuf ptrImpl = Buffed.OperationOPtr.none)
    (hfreeValid : ctxBuf.freeList.Valid ctxBuf.mem.size)
    (hfreeOld : ∀ (s a : UInt64), a ∈ ctxBuf.freeList.bucket s →
      ∀ (p : TopLevelPtr), p.InBounds ctx.spec →
        (p.range ctx.spec).upper ≤ a.toNat ∨
          (a.toNat : Int) + s.toNat ≤ (p.range ctx.spec).lower)
    (hfreeNew : ∀ (s a : UInt64), a ∈ ctxBuf.freeList.bucket s →
      a.toNat + s.toNat ≤ ptrImpl.toNat ∨ ptrImpl.toNat + 24 ≤ a.toNat)
    {ctxSpec : Veir.IRContext OpInfo} {ptrSpec : Veir.RegionPtr}
    (hspec : Veir.RegionPtr.allocEmptyAt ctx.spec ptrImpl.toNat = some (ctxSpec, ptrSpec)) :
    Veir.Sim (OpInfo := OpInfo) ⟨ctxBuf, ctxSpec⟩ := by
  have hptr := Veir.RegionPtr.allocEmptyAt_ptr hspec
  have hlay := (Veir.RegionPtr.allocEmptyAt_preservesLayout hspec).preserves
  have hfits := ctxBuf.mem.fits_in_memory
  have hrange : ∀ (p : TopLevelPtr), p.InBounds ctx.spec →
      p.range ctxSpec = p.range ctx.spec := by
    intro p hp
    cases p with
    | operation op => exact LayoutPreserved.same_operationPtr_range op (by simpa using hp) hlay |>.symm
    | block bl => exact LayoutPreserved.same_blockPtr_range bl (by simpa using hp) hlay |>.symm
    | region rg => rfl
  have hmem : ∀ (p : TopLevelPtr), p.InBounds ctxSpec →
      p.InBounds ctx.spec ∨ p = .region ptrSpec := by
    intro p hp
    cases p with
    | operation op =>
      have := (RegionPtr.allocEmptyAt_genericPtr_iff (.operation op) hspec).mp (by simpa using hp)
      rcases this with h | h
      · exact Or.inl (by simpa using h)
      · exact absurd h (by simp)
    | block bl =>
      have := (RegionPtr.allocEmptyAt_genericPtr_iff (.block bl) hspec).mp (by simpa using hp)
      rcases this with h | h
      · exact Or.inl (by simpa using h)
      · exact absurd h (by simp)
    | region rg =>
      have := (RegionPtr.allocEmptyAt_genericPtr_iff (.region rg) hspec).mp (by simpa using hp)
      rcases this with h | h
      · exact Or.inl (by simpa using h)
      · exact Or.inr (by simp only [GenericPtr.region.injEq] at h; grind)
  have hnewrange : (ptrSpec.range).lower = (ptrImpl.toNat : Int) ∧
      (ptrSpec.range).upper = (ptrImpl.toNat : Int) + 24 := by
    simp only [RegionPtr.range, RegionPtr.toFlat, hptr]
    exact ⟨rfl, rfl⟩
  constructor
  · exact Veir.RegionPtr.allocEmptyAt_fieldsInBounds hspec ctx.sim.fieldsInBounds
  · have hrepr := ctx.sim.repr
    constructor <;> grind
  · intro p hp
    rcases hmem p hp with hold | rfl
    · have hin := ctx.sim.in_bounds p hold
      rw [hrange p hold]
      simp only [IsIncludedIN, ExArray.range_def] at hin ⊢
      omega
    · simp only [TopLevelPtr.range, IsIncludedIN, ExArray.range_def]
      rw [hnewrange.1, hnewrange.2]
      omega
  · intro p q hp hq hne
    rcases hmem p hp with holdp | rfl <;> rcases hmem q hq with holdq | rfl
    · rw [hrange p holdp, hrange q holdq]
      exact ctx.sim.disjoint_allocs p q holdp holdq hne
    · have hd := hdisj p holdp
      rw [hrange p holdp]
      simpa only [IsDisjointI, TopLevelPtr.range, hnewrange.1, hnewrange.2] using hd
    · have hd := hdisj q holdq
      rw [hrange q holdq]
      simp only [IsDisjointI, TopLevelPtr.range, hnewrange.1, hnewrange.2] at hd ⊢
      omega
    · exact absurd rfl hne
  · -- encoding_op: every op is old; frame each record over the untouched prefix.
    intro op opIb
    have holdib : op.InBounds ctx.spec := by
      have := (RegionPtr.allocEmptyAt_genericPtr_iff (.operation op) hspec).mp (by simpa using opIb)
      grind
    have hagree := hagreeAll (.operation op) holdib
    have henc := ctx.sim.encoding_op op holdib
    have hrange := Veir.Sim.OperationPtr.range_linear (ctx := ctx) op holdib
    have hget : Veir.OperationPtr.get! op ctxSpec = Veir.OperationPtr.get! op ctx.spec := by grind
    constructor
    · refine OperationPtr.matchesBase_frame ctx op holdib henc.toMatchesBase
        (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat])) hlay (by rw [hget]) (by rw [hget])
        (by rw [hget]) (by rw [hget]) (by grind [layout_grind]) (Veir.OperationPtr.getProperties!_eq_of_OperationPtr_get!_eq hget) opIb
    · constructor
      · exact OperationPtr.numBlockOperands_frame ctx op holdib henc.numBlockOperands
          (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat])) (by rw [hget])
      · intro bo boIb heq
        have hboIb : bo.InBounds ctx.spec := by
          have := (RegionPtr.allocEmptyAt_genericPtr_iff (.blockOperand bo) hspec).mp (by simpa using boIb)
          grind
        have hincl := Veir.Sim.BlockOperandPtr.slot_included (ctx := ctx) bo hboIb
        have hpib := Veir.Sim.BlockOperandPtr.op_inBounds hboIb
        have hprangeS := Veir.Sim.OperationPtr.range_linear (ctx := ctx) bo.op hpib
        refine BlockOperandPtr.matches_frame ctx bo hboIb (henc.blockOperands bo hboIb heq)
          (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat])) hlay (by grind) boIb
    · constructor
      · exact OperationPtr.numRegions_frame ctx op holdib henc.numRegions
          (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat])) (by rw [hget])
      · intro idx idxIn
        have hnr : idx < op.getNumRegions! ctx.spec := by grind
        have hcap := ctx.sim.repr.operations_indices op holdib |>.capRegions
        refine OperationPtr.nthRegion_frame ctx op holdib idx hnr (henc.regions idx hnr)
          (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat])) ?_ (by grind)
        have hidxc : idx < (op.get! ctx.spec).capRegions := by grind
        have haddrR : (op.toM.toNat : Int) = op.id := by
          grind [Veir.OperationPtr.toM, Veir.OperationPtr.toFlat]
        have hincl := OperationPtr.nthRegion_range_included_op_range ctx op idx.toUInt64 (by grind) holdib
        exact hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat, UInt64.toNat_ofNat'])
    · constructor
      · exact OperationPtr.numOperands_frame ctx op holdib henc.numOperands
          (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat])) (by rw [hget])
      · intro oper operIb heq
        have hooIb : oper.InBounds ctx.spec := by
          have := (RegionPtr.allocEmptyAt_genericPtr_iff (.opOperand oper) hspec).mp (by simpa using operIb)
          grind
        have hincl := Veir.Sim.OpOperandPtr.slot_included (ctx := ctx) oper hooIb
        have hpib := Veir.Sim.OpOperandPtr.op_inBounds hooIb
        have hprangeS := Veir.Sim.OperationPtr.range_linear (ctx := ctx) oper.op hpib
        refine OpOperandPtr.matches_frame ctx oper hooIb (henc.operands oper hooIb heq)
          (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat])) hlay (by grind) operIb
    · constructor
      · exact OperationPtr.numResults_frame ctx op holdib henc.numResults
          (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat])) (by rw [hget])
      · intro res resIb heq
        have hresIb : res.InBounds ctx.spec := by
          have := (RegionPtr.allocEmptyAt_genericPtr_iff (.opResult res) hspec).mp (by simpa using resIb)
          grind
        have hincl := Veir.Sim.OpResultPtr.slot_included (ctx := ctx) res hresIb
        have hpib := Veir.Sim.OpResultPtr.op_inBounds hresIb
        have hprangeS := Veir.Sim.OperationPtr.range_linear (ctx := ctx) res.op hpib
        refine OpResultPtr.matches_frame ctx res hresIb (henc.results res hresIb heq)
          (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat])) hlay (by grind) resIb
  · -- encoding_block: every block is old; frame each record over the untouched prefix.
    intro blk blkIb
    have holdib : blk.InBounds ctx.spec := by
      have := (RegionPtr.allocEmptyAt_genericPtr_iff (.block blk) hspec).mp (by simpa using blkIb)
      grind
    have hagree := hagreeAll (.block blk) holdib
    have hrg := Veir.BlockPtr.range_ideal ctx.sim.repr holdib
    have henc := ctx.sim.encoding_block blk holdib
    have hrange := Veir.Sim.BlockPtr.range_linear (ctx := ctx) blk holdib
    have hget : Veir.BlockPtr.get! blk ctxSpec = Veir.BlockPtr.get! blk ctx.spec := by grind
    constructor
    · refine BlockPtr.matchesBase_frame ctx blk holdib henc.toMatchesBase
        (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat])) hlay (by rw [hget]) (by rw [hget])
        (by rw [hget]) (by rw [hget]) (by rw [hget]) (by rw [hget]) blkIb
    · constructor
      · exact BlockPtr.numArguments_frame ctx blk holdib henc.numArguments
          (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat])) (by rw [hget])
      · intro arg argIn heq
        have hargIb : arg.InBounds ctx.spec := by
          have := (RegionPtr.allocEmptyAt_genericPtr_iff (.blockArgument arg) hspec).mp (by simpa using argIn)
          grind
        have hincl := Veir.Sim.BlockArgumentPtr.slot_included (ctx := ctx) arg hargIb
        have hpib := Veir.Sim.BlockArgumentPtr.block_inBounds hargIb
        have hprangeS := Veir.Sim.BlockPtr.range_linear (ctx := ctx) arg.block hpib
        refine BlockArgumentPtr.matches_frame ctx arg hargIb (henc.arguments arg hargIb heq)
          (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat])) hlay (by grind) argIn
  · -- encoding_region
    intro rg rgIb
    rcases (RegionPtr.allocEmptyAt_genericPtr_iff (.region rg) hspec).mp (by simpa using rgIb)
      with hold | hnew
    · -- Old region: frame the 24-byte record.
      have holdib : rg.InBounds ctx.spec := by simpa using hold
      have hagree := hagreeAll (.region rg) holdib
      have hrg := Veir.RegionPtr.range_ideal (rg := rg)
      have henc := ctx.sim.encoding_region rg holdib
      have hrange := Veir.Sim.RegionPtr.range_linear (ctx := ctx) rg holdib
      refine RegionPtr.matches_frame ctx rg holdib henc
        (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.BlockPtr.rangeInt, Veir.RegionPtr.rangeInt, Veir.BlockPtr.toFlat, Veir.RegionPtr.toFlat])) hlay (by grind) rgIb
    · simp only [GenericPtr.region.injEq] at hnew
      subst hnew
      have hget : Veir.RegionPtr.get! rg ctxSpec = Region.empty := by grind
      have htoM : rg.toM = ptrImpl := by
        simp only [hptr, RegionPtr.toM, RegionPtr.toFlat]; grind
      constructor
      · simpa [Sim.OptionBlockPtr.Sim_def, hget, Region.empty, htoM, Veir.BlockPtr.toO, Veir.OperationPtr.toO] using hfirst.symm
      · simpa [Sim.OptionBlockPtr.Sim_def, hget, Region.empty, htoM, Veir.BlockPtr.toO, Veir.OperationPtr.toO] using hlast.symm
      · simpa [Sim.OptionOperationPtr.Sim_def, hget, Region.empty, htoM, Veir.BlockPtr.toO, Veir.OperationPtr.toO] using hparent.symm
  · rw [hattr]
    exact ctx.sim.attr_empty
  · exact hfreeValid
  · intro size address hm p hp
    rcases hmem p hp with hold | rfl
    · rw [hrange p hold]
      exact hfreeOld size address hm p hold
    · have hd := hfreeNew size address hm
      simp only [TopLevelPtr.range]
      rw [hnewrange.1, hnewrange.2]
      omega

end Veir
