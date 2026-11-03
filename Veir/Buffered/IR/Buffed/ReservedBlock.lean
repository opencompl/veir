module

public import Veir.Buffered.IR.Buffed.Frames
public import Veir.Buffered.IR.Buffed.Basic
import all Veir.Buffered.IR.Buffed.Basic

@[expose] public section
namespace Veir.Buffered
variable [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo]
set_option maxHeartbeats 1000000

theorem Sim.BlockPtr.allocReserved_sim (ctx : Sim.IRContext OpInfo) (numArgs : UInt64)
    (hnumArgs : numArgs.toNat ≤ Buffed.countCard)
    {ctxBuf : Buffed.IRBufContext} {ptrImpl : Buffed.BlockMPtr}
    (hsizele : ctx.buf.mem.size ≤ ctxBuf.mem.size)
    (hsize : ptrImpl.toNat + (56 + numArgs.toNat * 40) ≤ ctxBuf.mem.size)
    (hattr : ctxBuf.attributes = ctx.buf.attributes)
    (hagreeAll : ∀ (p : TopLevelPtr), p.InBounds ctx.spec →
      Buffed.AgreesOn ctxBuf ctx.buf (p.range ctx.spec).lower.toNat (p.range ctx.spec).upper.toNat)
    (hdisj : ∀ (p : TopLevelPtr), p.InBounds ctx.spec →
      (p.range ctx.spec).upper ≤ ptrImpl.toNat ∨
        (ptrImpl.toNat : Int) + (56 + numArgs.toNat * 40) ≤ (p.range ctx.spec).lower)
    (hnum : Buffed.BlockMPtr.readNumArguments! ctxBuf ptrImpl = numArgs)
    (huse : Buffed.BlockMPtr.readFirstUse! ctxBuf ptrImpl = Buffed.BlockOperandOPtr.none)
    (hprev : Buffed.BlockMPtr.readPrev! ctxBuf ptrImpl = Buffed.BlockOPtr.none)
    (hnext : Buffed.BlockMPtr.readNext! ctxBuf ptrImpl = Buffed.BlockOPtr.none)
    (hparent : Buffed.BlockMPtr.readParent! ctxBuf ptrImpl = Buffed.RegionOPtr.none)
    (hfirst : Buffed.BlockMPtr.readFirstOp! ctxBuf ptrImpl = Buffed.OperationOPtr.none)
    (hlast : Buffed.BlockMPtr.readLastOp! ctxBuf ptrImpl = Buffed.OperationOPtr.none)
    (hfreeValid : ctxBuf.freeList.Valid ctxBuf.mem.size)
    (hfreeOld : ∀ (s a : UInt64), a ∈ ctxBuf.freeList.bucket s →
      ∀ (p : TopLevelPtr), p.InBounds ctx.spec →
        (p.range ctx.spec).upper ≤ a.toNat ∨
          (a.toNat : Int) + s.toNat ≤ (p.range ctx.spec).lower)
    (hfreeNew : ∀ (s a : UInt64), a ∈ ctxBuf.freeList.bucket s →
      a.toNat + s.toNat ≤ ptrImpl.toNat ∨ ptrImpl.toNat + (56 + numArgs.toNat * 40) ≤ a.toNat)
    {ctxSpec : Veir.Buffered.IRContext OpInfo} {ptrSpec : Veir.Buffered.BlockPtr}
    (hspec : Veir.Buffered.BlockPtr.allocEmptyAtAddress ctx.spec numArgs.toNat ptrImpl.toNat = some (ctxSpec, ptrSpec)) :
    Veir.Buffered.Sim (OpInfo := OpInfo) ⟨ctxBuf, .mk ctxSpec⟩ := by
  have hptr := Veir.Buffered.BlockPtr.allocEmptyAtAddress_ptr hspec
  have hlay := Veir.Buffered.BlockPtr.allocEmptyAtAddress_preservesLayout hspec
  have hfits := ctxBuf.mem.fits_in_memory
  have hptrrepr : ptrSpec.IsRepr := by
    simp only [Veir.Buffered.BlockPtr.IsRepr, Veir.Buffered.BlockPtr.toFlat, hptr, Int64.maxNatValue] at *
    omega
  have hnewrepr := BlockPtr.allocEmptyAtAddress_fieldsIsRepr hspec hnumArgs hptrrepr ctx.sim.repr
  have hrange : ∀ (p : TopLevelPtr), p.InBounds ctx.spec →
      p.range ctxSpec = p.range ctx.spec := by
    intro p hp
    cases p with
    | operation op => exact LayoutPreserved.same_operationPtr_range op (by simpa using hp) hlay |>.symm
    | block bl => exact LayoutPreserved.same_blockPtr_range bl (by simpa using hp) hlay |>.symm
    | region rg => rfl
  have hmem : ∀ (p : TopLevelPtr), p.InBounds ctxSpec →
      p.InBounds ctx.spec ∨ p = .block ptrSpec := by
    intro p hp
    cases p with
    | operation op =>
      rcases (BlockPtr.allocEmptyAtAddress_genericPtr_iff (.operation op) hspec).mp (by simpa using hp)
        with h | h | h
      · exact Or.inl (by simpa using h)
      · exact absurd h (by simp)
      · exact absurd h (by simp)
    | block bl =>
      rcases (BlockPtr.allocEmptyAtAddress_genericPtr_iff (.block bl) hspec).mp (by simpa using hp)
        with h | h | h
      · exact Or.inl (by simpa using h)
      · exact Or.inr (by simp only [GenericPtr.block.injEq] at h; grind)
      · exact absurd h (by simp)
    | region rg =>
      rcases (BlockPtr.allocEmptyAtAddress_genericPtr_iff (.region rg) hspec).mp (by simpa using hp)
        with h | h | h
      · exact Or.inl (by simpa using h)
      · exact absurd h (by simp)
      · exact absurd h (by simp)
  have hnewib : ptrSpec.InBounds ctxSpec := by grind
  have hgetNew : ptrSpec.get! ctxSpec = Block.empty numArgs.toNat := by grind
  have hnewrange : (ptrSpec.range ctxSpec).lower = (ptrImpl.toNat : Int) ∧
      (ptrSpec.range ctxSpec).upper = (ptrImpl.toNat : Int) + (56 + numArgs.toNat * 40) := by
    rw [BlockPtr.range_ideal hnewrepr hnewib]
    simp only [BlockPtr.rangeInt, Buffed.Block.rangeInt, add_nat_range_def,
      Buffed.Block.Offsets.afterInt, Buffed.Block.Sizes.argumentsNat, BlockPtr.toFlat]
    rw [hgetNew]
    simp only [Block.empty, hptr, Buffed.Block.Offsets.argumentsInt, Buffed.BlockArgument.sizeNat]
    constructor <;> omega
  constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
  · exact Veir.Buffered.BlockPtr.allocEmptyAtAddress_fieldsInBounds hspec ctx.sim.fieldsInBounds
  · exact hnewrepr
  · intro p hp
    rcases hmem p hp with hold | rfl
    · have hin := ctx.sim.in_bounds p hold
      rw [hrange p hold]
      simp only [IsIncludedIN, ExArray.range_def, Sim.RawIRContext.spec, Sim.IRContext.spec] at hin ⊢
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
      have := (BlockPtr.allocEmptyAtAddress_genericPtr_iff (.operation op) hspec).mp (by simpa using opIb)
      grind
    have hagree := hagreeAll (.operation op) holdib
    have henc := ctx.sim.encoding_op op holdib
    have hrange := Veir.Buffered.Sim.OperationPtr.range_linear (ctx := ctx) op holdib
    have hget : Veir.Buffered.OperationPtr.get! op ctxSpec = Veir.Buffered.OperationPtr.get! op ctx.spec := by grind
    constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
    · refine OperationPtr.matchesBase_frame ctx op holdib henc.toMatchesBase
        (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.Buffered.BlockPtr.rangeInt, Veir.Buffered.RegionPtr.rangeInt, Veir.Buffered.BlockPtr.toFlat, Veir.Buffered.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.Buffered.BlockPtr.rangeInt, Veir.Buffered.RegionPtr.rangeInt, Veir.Buffered.BlockPtr.toFlat, Veir.Buffered.RegionPtr.toFlat])) hlay (by rw [hget]) (by rw [hget])
        (by rw [hget]) (by rw [hget]) (by grind [layout_grind]) (Veir.Buffered.OperationPtr.getProperties!_eq_of_OperationPtr_get!_eq hget) opIb
    · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
      · exact OperationPtr.numBlockOperands_frame ctx op holdib henc.numBlockOperands
          (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.Buffered.BlockPtr.rangeInt, Veir.Buffered.RegionPtr.rangeInt, Veir.Buffered.BlockPtr.toFlat, Veir.Buffered.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.Buffered.BlockPtr.rangeInt, Veir.Buffered.RegionPtr.rangeInt, Veir.Buffered.BlockPtr.toFlat, Veir.Buffered.RegionPtr.toFlat])) (by rw [hget])
      · intro bo boIb heq
        have hboIb : bo.InBounds ctx.spec := by
          have := (BlockPtr.allocEmptyAtAddress_genericPtr_iff (.blockOperand bo) hspec).mp (by simpa using boIb)
          grind
        have hincl := Veir.Buffered.Sim.BlockOperandPtr.slot_included (ctx := ctx) bo hboIb
        have hpib := Veir.Buffered.Sim.BlockOperandPtr.op_inBounds hboIb
        have hprangeS := Veir.Buffered.Sim.OperationPtr.range_linear (ctx := ctx) bo.op hpib
        refine BlockOperandPtr.matches_frame ctx bo hboIb (henc.blockOperands bo hboIb heq)
          (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.Buffered.BlockPtr.rangeInt, Veir.Buffered.RegionPtr.rangeInt, Veir.Buffered.BlockPtr.toFlat, Veir.Buffered.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.Buffered.BlockPtr.rangeInt, Veir.Buffered.RegionPtr.rangeInt, Veir.Buffered.BlockPtr.toFlat, Veir.Buffered.RegionPtr.toFlat])) hlay (by grind) boIb
    · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
      · exact OperationPtr.numRegions_frame ctx op holdib henc.numRegions
          (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.Buffered.BlockPtr.rangeInt, Veir.Buffered.RegionPtr.rangeInt, Veir.Buffered.BlockPtr.toFlat, Veir.Buffered.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.Buffered.BlockPtr.rangeInt, Veir.Buffered.RegionPtr.rangeInt, Veir.Buffered.BlockPtr.toFlat, Veir.Buffered.RegionPtr.toFlat])) (by rw [hget])
      · intro idx idxIn
        have hnr : idx < op.getNumRegions! ctx.spec := by grind
        have hcap := ctx.sim.repr.operations_indices op holdib |>.capRegions
        refine OperationPtr.nthRegion_frame ctx op holdib idx hnr (henc.regions idx hnr)
          (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.Buffered.BlockPtr.rangeInt, Veir.Buffered.RegionPtr.rangeInt, Veir.Buffered.BlockPtr.toFlat, Veir.Buffered.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.Buffered.BlockPtr.rangeInt, Veir.Buffered.RegionPtr.rangeInt, Veir.Buffered.BlockPtr.toFlat, Veir.Buffered.RegionPtr.toFlat])) ?_ (by grind)
        have hidxc : idx < (op.get! ctx.spec).capRegions := by grind
        have haddrR : (op.toM.toNat : Int) = op.id := by
          grind [Veir.Buffered.OperationPtr.toM, Veir.Buffered.OperationPtr.toFlat]
        have hincl := OperationPtr.nthRegion_range_included_op_range ctx op idx.toUInt64 (by grind) holdib
        exact hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.Buffered.BlockPtr.rangeInt, Veir.Buffered.RegionPtr.rangeInt, Veir.Buffered.BlockPtr.toFlat, Veir.Buffered.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.Buffered.BlockPtr.rangeInt, Veir.Buffered.RegionPtr.rangeInt, Veir.Buffered.BlockPtr.toFlat, Veir.Buffered.RegionPtr.toFlat, UInt64.toNat_ofNat'])
    · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
      · exact OperationPtr.numOperands_frame ctx op holdib henc.numOperands
          (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.Buffered.BlockPtr.rangeInt, Veir.Buffered.RegionPtr.rangeInt, Veir.Buffered.BlockPtr.toFlat, Veir.Buffered.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.Buffered.BlockPtr.rangeInt, Veir.Buffered.RegionPtr.rangeInt, Veir.Buffered.BlockPtr.toFlat, Veir.Buffered.RegionPtr.toFlat])) (by rw [hget])
      · intro oper operIb heq
        have hooIb : oper.InBounds ctx.spec := by
          have := (BlockPtr.allocEmptyAtAddress_genericPtr_iff (.opOperand oper) hspec).mp (by simpa using operIb)
          grind
        have hincl := Veir.Buffered.Sim.OpOperandPtr.slot_included (ctx := ctx) oper hooIb
        have hpib := Veir.Buffered.Sim.OpOperandPtr.op_inBounds hooIb
        have hprangeS := Veir.Buffered.Sim.OperationPtr.range_linear (ctx := ctx) oper.op hpib
        refine OpOperandPtr.matches_frame ctx oper hooIb (henc.operands oper hooIb heq)
          (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.Buffered.BlockPtr.rangeInt, Veir.Buffered.RegionPtr.rangeInt, Veir.Buffered.BlockPtr.toFlat, Veir.Buffered.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.Buffered.BlockPtr.rangeInt, Veir.Buffered.RegionPtr.rangeInt, Veir.Buffered.BlockPtr.toFlat, Veir.Buffered.RegionPtr.toFlat])) hlay (by grind) operIb
    · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
      · exact OperationPtr.numResults_frame ctx op holdib henc.numResults
          (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.Buffered.BlockPtr.rangeInt, Veir.Buffered.RegionPtr.rangeInt, Veir.Buffered.BlockPtr.toFlat, Veir.Buffered.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.Buffered.BlockPtr.rangeInt, Veir.Buffered.RegionPtr.rangeInt, Veir.Buffered.BlockPtr.toFlat, Veir.Buffered.RegionPtr.toFlat])) (by rw [hget])
      · intro res resIb heq
        have hresIb : res.InBounds ctx.spec := by
          have := (BlockPtr.allocEmptyAtAddress_genericPtr_iff (.opResult res) hspec).mp (by simpa using resIb)
          grind
        have hincl := Veir.Buffered.Sim.OpResultPtr.slot_included (ctx := ctx) res hresIb
        have hpib := Veir.Buffered.Sim.OpResultPtr.op_inBounds hresIb
        have hprangeS := Veir.Buffered.Sim.OperationPtr.range_linear (ctx := ctx) res.op hpib
        refine OpResultPtr.matches_frame ctx res hresIb (henc.results res hresIb heq)
          (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.Buffered.BlockPtr.rangeInt, Veir.Buffered.RegionPtr.rangeInt, Veir.Buffered.BlockPtr.toFlat, Veir.Buffered.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.Buffered.BlockPtr.rangeInt, Veir.Buffered.RegionPtr.rangeInt, Veir.Buffered.BlockPtr.toFlat, Veir.Buffered.RegionPtr.toFlat])) hlay (by grind) resIb
  · intro blk blkIb
    rcases (BlockPtr.allocEmptyAtAddress_genericPtr_iff (.block blk) hspec).mp (by simpa using blkIb)
      with hold | hnew | hfu
    · have holdib : blk.InBounds ctx.spec := by simpa using hold
      have hagree := hagreeAll (.block blk) holdib
      have hrg := Veir.Buffered.BlockPtr.range_ideal ctx.sim.repr holdib
      have henc := ctx.sim.encoding_block blk holdib
      have hrange := Veir.Buffered.Sim.BlockPtr.range_linear (ctx := ctx) blk holdib
      have hget : Veir.Buffered.BlockPtr.get! blk ctxSpec = Veir.Buffered.BlockPtr.get! blk ctx.spec := by grind
      constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
      · refine BlockPtr.matchesBase_frame ctx blk holdib henc.toMatchesBase
          (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.Buffered.BlockPtr.rangeInt, Veir.Buffered.RegionPtr.rangeInt, Veir.Buffered.BlockPtr.toFlat, Veir.Buffered.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.Buffered.BlockPtr.rangeInt, Veir.Buffered.RegionPtr.rangeInt, Veir.Buffered.BlockPtr.toFlat, Veir.Buffered.RegionPtr.toFlat])) hlay (by rw [hget]) (by rw [hget])
          (by rw [hget]) (by rw [hget]) (by rw [hget]) (by rw [hget]) blkIb
      · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
        · exact BlockPtr.numArguments_frame ctx blk holdib henc.numArguments
            (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.Buffered.BlockPtr.rangeInt, Veir.Buffered.RegionPtr.rangeInt, Veir.Buffered.BlockPtr.toFlat, Veir.Buffered.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.Buffered.BlockPtr.rangeInt, Veir.Buffered.RegionPtr.rangeInt, Veir.Buffered.BlockPtr.toFlat, Veir.Buffered.RegionPtr.toFlat])) (by rw [hget])
        · intro arg argIn heq
          have hargIb : arg.InBounds ctx.spec := by
            have := (BlockPtr.allocEmptyAtAddress_genericPtr_iff (.blockArgument arg) hspec).mp (by simpa using argIn)
            grind
          have hincl := Veir.Buffered.Sim.BlockArgumentPtr.slot_included (ctx := ctx) arg hargIb
          have hpib := Veir.Buffered.Sim.BlockArgumentPtr.block_inBounds hargIb
          have hprangeS := Veir.Buffered.Sim.BlockPtr.range_linear (ctx := ctx) arg.block hpib
          refine BlockArgumentPtr.matches_frame ctx arg hargIb (henc.arguments arg hargIb heq)
            (hagree.mono (by grind [TopLevelPtr.range, IsIncludedI, Veir.Buffered.BlockPtr.rangeInt, Veir.Buffered.RegionPtr.rangeInt, Veir.Buffered.BlockPtr.toFlat, Veir.Buffered.RegionPtr.toFlat]) (by grind [TopLevelPtr.range, IsIncludedI, Veir.Buffered.BlockPtr.rangeInt, Veir.Buffered.RegionPtr.rangeInt, Veir.Buffered.BlockPtr.toFlat, Veir.Buffered.RegionPtr.toFlat])) hlay (by grind) argIn
    · simp only [GenericPtr.block.injEq] at hnew
      subst blk
      have htoM : ptrSpec.toM = ptrImpl := by simp [BlockPtr.toM, BlockPtr.toFlat, hptr]
      constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
      · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
        · simpa [Sim.OptionBlockOperandPtr.Sim_def, Sim.OptionBlockOperandPtr.spec, hgetNew, Block.empty, htoM, Veir.Buffered.BlockOperandPtr.toO, Veir.Buffered.BlockPtr.toO, Veir.Buffered.OperationPtr.toO, Veir.Buffered.RegionPtr.toO] using huse.symm
        · simpa [Sim.OptionBlockPtr.Sim_def, Sim.OptionBlockPtr.spec, hgetNew, Block.empty, htoM, Veir.Buffered.BlockOperandPtr.toO, Veir.Buffered.BlockPtr.toO, Veir.Buffered.OperationPtr.toO, Veir.Buffered.RegionPtr.toO] using hprev.symm
        · simpa [Sim.OptionBlockPtr.Sim_def, Sim.OptionBlockPtr.spec, hgetNew, Block.empty, htoM, Veir.Buffered.BlockOperandPtr.toO, Veir.Buffered.BlockPtr.toO, Veir.Buffered.OperationPtr.toO, Veir.Buffered.RegionPtr.toO] using hnext.symm
        · simpa [Sim.OptionRegionPtr.Sim_def, Sim.OptionRegionPtr.spec, hgetNew, Block.empty, htoM, Veir.Buffered.BlockOperandPtr.toO, Veir.Buffered.BlockPtr.toO, Veir.Buffered.OperationPtr.toO, Veir.Buffered.RegionPtr.toO] using hparent.symm
        · simpa [Sim.OptionOperationPtr.Sim_def, Sim.OptionOperationPtr.spec, hgetNew, Block.empty, htoM, Veir.Buffered.BlockOperandPtr.toO, Veir.Buffered.BlockPtr.toO, Veir.Buffered.OperationPtr.toO, Veir.Buffered.RegionPtr.toO] using hfirst.symm
        · simpa [Sim.OptionOperationPtr.Sim_def, Sim.OptionOperationPtr.spec, hgetNew, Block.empty, htoM, Veir.Buffered.BlockOperandPtr.toO, Veir.Buffered.BlockPtr.toO, Veir.Buffered.OperationPtr.toO, Veir.Buffered.RegionPtr.toO] using hlast.symm
      · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk]
        · simpa [hgetNew, Block.empty, htoM, Veir.Buffered.BlockOperandPtr.toO, Veir.Buffered.BlockPtr.toO, Veir.Buffered.OperationPtr.toO, Veir.Buffered.RegionPtr.toO] using (congrArg UInt64.toNat hnum).symm
        · intro arg harg heq
          grind [Veir.Buffered.BlockArgumentPtr.InBounds, Veir.Buffered.BlockPtr.getNumArguments!]
    · exact absurd hfu (by simp)
  · intro rg rgIb
    have holdib : rg.InBounds ctx.spec := by
      have := (BlockPtr.allocEmptyAtAddress_genericPtr_iff (.region rg) hspec).mp (by simpa using rgIb)
      grind
    have hagree := hagreeAll (.region rg) holdib
    have hrg := Veir.Buffered.RegionPtr.range_ideal (rg := rg)
    have henc := ctx.sim.encoding_region rg holdib
    have hrange := Veir.Buffered.Sim.RegionPtr.range_linear (ctx := ctx) rg holdib
    refine RegionPtr.matches_frame ctx rg holdib henc
      (hagree.mono (by grind [TopLevelPtr.range, Veir.Buffered.RegionPtr.rangeInt, Veir.Buffered.RegionPtr.toFlat])
        (by grind [TopLevelPtr.range, Veir.Buffered.RegionPtr.rangeInt, Veir.Buffered.RegionPtr.toFlat])) hlay (by grind) rgIb
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

end Veir.Buffered
