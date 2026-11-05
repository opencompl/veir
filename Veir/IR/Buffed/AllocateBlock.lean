module

public import ExArray.CompilerExtras

public import Veir.IR.Buffed.ReservedBlock
public import Veir.IR.Buffed.ContainerInitialization
public import Veir.IR.Buffed.Allocation
public import Veir.IR.Buffed.InBounds
import all Veir.IR.Buffed.Basic

@[expose] public section
namespace Veir
variable [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo]
set_option maxHeartbeats 1000000

@[inline]
def Sim.BlockPtr.allocFreshRaw (ctx : Buffed.IRBufContext) (numArgs : UInt64)
    (hnumArgs : numArgs.toNat ≤ Buffed.countCard) :
    Option (Buffed.IRBufContext × Buffed.BlockMPtr) :=
  match h : ctx.reserve (Buffed.BlockMPtr.computeBlockSize numArgs).toUInt64 with
  | none => none
  | some (b, ptr) =>
    some (Buffed.BlockMPtr.initialize b ptr numArgs (by
      have hb := Buffed.IRBufContext.reserve_bounds h |>.2
      have hs := Buffed.BlockMPtr.computeBlockSize_toNat numArgs hnumArgs
      simp only [Buffed.Block.sizeBaseNat, Buffed.BlockArgument.sizeNat] at hs
      omega), ptr)

theorem Sim.BlockPtr.allocFreshRaw_eq {ctx b' : Buffed.IRBufContext} {ptr : Buffed.BlockMPtr}
    {numArgs : UInt64} {hnumArgs}
    (h : allocFreshRaw ctx numArgs hnumArgs = some (b', ptr)) :
    ∃ b, ctx.reserve (Buffed.BlockMPtr.computeBlockSize numArgs).toUInt64 = some (b, ptr) ∧ ∃ hb, b' = Buffed.BlockMPtr.initialize b ptr numArgs hb := by
  grind [allocFreshRaw]

theorem Sim.BlockPtr.allocFresh_sim {ctx : Sim.IRContext OpInfo}
    {b' : Buffed.IRBufContext} {ptr : Buffed.BlockMPtr}
    {numArgs : UInt64} {hnumArgs}
    {spec : Veir.IRContext OpInfo} {sptr : Veir.BlockPtr}
    (h : allocFreshRaw ctx.buf numArgs hnumArgs = some (b', ptr))
    (hspec : Veir.BlockPtr.allocEmptyAtAddress ctx.spec numArgs.toNat ptr.toNat = some (spec, sptr)) :
    Veir.Sim ⟨b', .mk spec⟩ := by
  obtain ⟨b, hres, hb, rfl⟩ := allocFreshRaw_eq h
  have hbounds := Buffed.IRBufContext.reserve_bounds hres
  have hcompute := Buffed.BlockMPtr.computeBlockSize_toNat numArgs hnumArgs
  simp only [Buffed.Block.sizeBaseNat, Buffed.BlockArgument.sizeNat] at hcompute
  have hsize : (Buffed.BlockMPtr.initialize b ptr numArgs hb).mem.size = b.mem.size :=
    Buffed.BlockMPtr.initialize_size b ptr numArgs hb
  have hattr : (Buffed.BlockMPtr.initialize b ptr numArgs hb).attributes = ctx.buf.attributes := by
    rw [Buffed.BlockMPtr.initialize_attributes, Buffed.IRBufContext.reserve_attributes hres]
  have hdisj := ctx.reservation_disjoint hres
  obtain ⟨hnum, huse, hprev, hnext, hparent, hfirst, hlast⟩ := Buffed.BlockMPtr.initialize_reads b ptr numArgs hb
  apply allocReserved_sim ctx numArgs hnumArgs (by rw [hsize]; exact hbounds.1)
    (by rw [hsize]; rw [hcompute] at hbounds; exact hbounds.2) hattr ?_
    (by simpa [hcompute] using hdisj) hnum huse hprev hnext hparent hfirst hlast hspec
  · intro p hp
    have hd := hdisj p hp
    have hin := ctx.sim.in_bounds p hp
    change IsIncludedIN (p.range ctx.spec) _ at hin
    simp only [IsIncludedIN, ExArray.range_def] at hin
    refine ⟨by rw [hsize]; exact hbounds.1, ?_, ?_⟩
    · intro w n len hn hl
      have hdr : n.toNat + len.toNat ≤ ptr.toNat ∨ ptr.toNat + (56 + numArgs.toNat * 40) ≤ n.toNat := by rw [hcompute] at hd; omega
      rw [Buffed.BlockMPtr.initialize_read_disjoint b ptr numArgs hb w n len (by omega)]
      exact Buffed.IRBufContext.reserve_read hres w n len (by omega)
    · intro i a hi
      simpa only [hattr] using hi
theorem Sim.BlockPtr.allocFreshRaw_fresh {ctx : Sim.IRContext OpInfo}
    {b' : Buffed.IRBufContext} {ptr : Buffed.BlockMPtr}
    {numArgs : UInt64} {hnumArgs}
    (h : allocFreshRaw ctx.buf numArgs hnumArgs = some (b', ptr)) :
    ¬ (⟨ptr.toNat⟩ : Veir.BlockPtr).InBounds ctx.spec := by
  obtain ⟨b, hres, _⟩ := allocFreshRaw_eq h
  intro hp
  have hd := ctx.reservation_disjoint hres (.block ⟨ptr.toNat⟩) hp
  simp only [TopLevelPtr.range, Veir.BlockPtr.range_ideal ctx.sim.repr hp, Veir.BlockPtr.rangeInt,
    Buffed.Block.rangeInt, Veir.BlockPtr.toFlat, add_nat_range_def] at hd
  have hs := Buffed.BlockMPtr.computeBlockSize_toNat numArgs hnumArgs
  grind

/-- Keep reservation control flow out of callers so their ghost specification
arguments can be eliminated before the native allocator call. -/
buffed (inline := false)
def Sim.BlockPtr.allocFreshSim (ctx : Sim.IRContext OpInfo) (numArgs : UInt64) : Option (Sim.BlockPtr × Sim.IRContext OpInfo) :=
  if hnumArgs : numArgs.toNat ≤ Buffed.countCard then
  match h : allocFreshRaw ctx.buf numArgs hnumArgs with
  | none => none
  | some (b, ptr) =>
    have hsome : (Veir.BlockPtr.allocEmptyAtAddress ctx.spec numArgs.toNat ptr.toNat).isSome := by
      simp only [Veir.BlockPtr.allocEmptyAtAddress]
      have hf := allocFreshRaw_fresh h
      grind [Veir.BlockPtr.inBounds_def]
    let specRes := ctx.spec'.map (fun spec =>
      (Veir.BlockPtr.allocEmptyAtAddress spec numArgs.toNat ptr.toNat).get!)
    some (⟨ptr, specRes.map Prod.snd⟩, ⟨b, specRes.map Prod.fst, by
      rw [Erased.map_eq_mk]
      apply allocFresh_sim (sptr := specRes.out.2) h
      simpa only [specRes, Erased.map_out, Sim.IRContext.spec, Option.get!] using
        (Option.some_get! _ hsome).symm⟩)

  else none

theorem Sim.BlockPtr.allocFresh_spec' {ctx : Sim.IRContext OpInfo} (numArgs : UInt64)
    (h : allocFresh ctx numArgs = some (ptr, ctx')) :
    Veir.BlockPtr.allocEmptyAtAddress ctx.spec numArgs.toNat ptr.impl.toNat = some (ctx'.spec, ptr.spec) := by
  simp only [allocFresh.unfold] at h
  split at h
  rotate_left
  · contradiction
  split at h
  · contradiction
  · rename_i b p hi
    have hf := allocFreshRaw_fresh hi
    have hs : (Veir.BlockPtr.allocEmptyAtAddress ctx.spec numArgs.toNat p.toNat).isSome := by
      simp only [Veir.BlockPtr.allocEmptyAtAddress]
      grind [Veir.BlockPtr.inBounds_def]
    simp_all only [Option.some.injEq, Prod.mk.injEq]
    obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := h
    simp only [Sim.IRContext.spec, Sim.BlockPtr.spec, Erased.map_out, Option.get!]
    grind

@[grind! .]
theorem Sim.BlockPtr.allocFresh_spec {ctx : Sim.IRContext OpInfo} (numArgs : UInt64)
    (h : allocFresh ctx numArgs = some (ptr, ctx')) :
    ∃ addr, Veir.BlockPtr.allocEmptyAtAddress ctx.spec numArgs.toNat addr = some (ctx'.spec, ptr.spec) :=
  ⟨ptr.impl.toNat, allocFresh_spec' numArgs h⟩

namespace Sim
variable {ctx ctx' : IRContext OpInfo}
@[grind =>]
theorem BlockPtr.allocFresh_genericPtr_iff (ptr : GenericPtr) (heq : allocFresh ctx numArgs = some (ptr', ctx')) :
    ptr.InBounds ctx' ↔ (ptr.InBounds ctx ∨ ptr = .fromBlock ptr' ∨ ptr = .fromBlockOperandPtr (ptr'.getBlockOperandPtrPtr)) := by
  have hspec := Sim.BlockPtr.allocFresh_spec' numArgs heq
  have hlay := Veir.BlockPtr.allocEmptyAtAddress_preservesLayout hspec
  have hptr := Veir.BlockPtr.allocEmptyAtAddress_ptr hspec
  have hnew : ptr'.InBounds ctx' := by
    have hib := (Veir.BlockPtr.allocEmptyAtAddress_genericPtr_iff (.block ptr'.spec) hspec).mpr
      (.inr (.inl rfl))
    refine ⟨?_, by grind⟩
    grind [Veir.BlockPtr.toM]
  have hslot := Sim.BlockPtr.getOpOperandPtrPtr_sim_of_sim (ctx := ctx') ptr' hnew
  constructor
  · rintro ⟨sim', ib'⟩
    rcases (Veir.BlockPtr.allocEmptyAtAddress_genericPtr_iff ptr.spec hspec).mp ib' with hold | hb | hfu
    · -- Old pointer: the layout is preserved, so the address is unchanged.
      refine .inl ⟨?_, hold⟩
      have := Veir.GenericPtr.layoutPreserved_same_toM hlay hold
      grind
    · -- The freshly allocated block: its impl address is forced by the sim relation.
      refine .inr (.inl ?_)
      obtain ⟨impl, spec⟩ := ptr
      grind [Sim.GenericPtr.fromBlock, Veir.GenericPtr.toM, Veir.BlockPtr.toM]
    · -- The new block's `firstUse` slot: its impl address is forced by the sim relation.
      refine .inr (.inr ?_)
      obtain ⟨impl, spec⟩ := ptr
      grind [Sim.GenericPtr.fromBlockOperandPtr, Veir.GenericPtr.toM,
        Sim.BlockPtr.getBlockOperandPtrPtr]
  · rintro (hold | rfl | rfl)
    · exact ⟨Sim.GenericPtr.sim_layoutPreserved hlay hold,
        (Veir.BlockPtr.allocEmptyAtAddress_genericPtr_iff ptr.spec hspec).mpr (.inl hold.ib)⟩
    · refine ⟨?_, (Veir.BlockPtr.allocEmptyAtAddress_genericPtr_iff _ hspec).mpr
        (.inr (.inl (by grind [Sim.GenericPtr.fromBlock])))⟩
      grind [Sim.GenericPtr.fromBlock, Veir.GenericPtr.toM]
    · refine ⟨?_, (Veir.BlockPtr.allocEmptyAtAddress_genericPtr_iff _ hspec).mpr
        (.inr (.inr (by grind [Sim.GenericPtr.fromBlockOperandPtr, Sim.BlockPtr.getBlockOperandPtrPtr])))⟩
      grind [Sim.GenericPtr.fromBlockOperandPtr, Veir.GenericPtr.toM,
        Sim.BlockPtr.getBlockOperandPtrPtr]

@[grind .]
theorem BlockPtr.allocFresh_genericPtr_mono (ptr : GenericPtr) (heq : allocFresh ctx numArgs = some (ptr', ctx')) :
    ptr.InBounds ctx → ptr.InBounds ctx' := by
  grind

@[grind .]
theorem BlockPtr.allocFresh_genericPtr_veir_mono (ptr : Veir.GenericPtr) (heq : allocFresh ctx numArgs = some (ptr', ctx')) :
    ptr.InBounds ctx.spec → ptr.InBounds ctx'.spec := by
  have hspec := Sim.BlockPtr.allocFresh_spec' numArgs heq
  grind

@[grind .]
theorem BlockPtr.allocFresh_newBlock_inBounds (heq : allocFresh ctx numArgs = some (ptr', ctx')) :
    ptr'.InBounds ctx' := by
  have : (GenericPtr.fromBlock ptr').InBounds ctx' := by grind
  grind [generic_ptr_grind]

end Sim

end Veir
