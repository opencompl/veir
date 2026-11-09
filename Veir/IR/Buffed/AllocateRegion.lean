module


public import Veir.IR.Buffed.ReservedRegion
public import Veir.IR.Buffed.ContainerInitialization
public import Veir.IR.Buffed.Allocation
public import Veir.IR.Buffed.InBounds
import all Veir.IR.Buffed.Basic

@[expose] public section
namespace Veir
variable [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo]
set_option maxHeartbeats 1000000

@[inline]
def Sim.RegionPtr.allocFreshRaw (ctx : Buffed.IRBufContext) :
    Option (Buffed.IRBufContext × Buffed.RegionMPtr) :=
  match h : ctx.reserve 24 with
  | none => none
  | some (b, ptr) =>
    some (Buffed.RegionMPtr.initialize b ptr (Buffed.IRBufContext.reserve_bounds h |>.2), ptr)

theorem Sim.RegionPtr.allocFreshRaw_eq {ctx b' : Buffed.IRBufContext} {ptr : Buffed.RegionMPtr}
    (h : allocFreshRaw ctx = some (b', ptr)) :
    ∃ b, ctx.reserve 24 = some (b, ptr) ∧ ∃ hb, b' = Buffed.RegionMPtr.initialize b ptr hb := by
  unfold allocFreshRaw at h
  split at h
  · contradiction
  · rename_i b p hres
    obtain ⟨rfl, rfl⟩ := Option.some.inj h
    exact ⟨b, hres, _, rfl⟩

theorem Sim.RegionPtr.allocFresh_sim {ctx : Sim.IRContext OpInfo}
    {b' : Buffed.IRBufContext} {ptr : Buffed.RegionMPtr}
    {spec : Veir.IRContext OpInfo} {sptr : Veir.RegionPtr}
    (h : allocFreshRaw ctx.buf = some (b', ptr))
    (hspec : Veir.RegionPtr.allocEmptyAt ctx.spec ptr.toNat = some (spec, sptr)) :
    Veir.Sim ⟨b', .mk spec⟩ := by
  obtain ⟨b, hres, hb, rfl⟩ := allocFreshRaw_eq h
  have hbounds := Buffed.IRBufContext.reserve_bounds hres
  have hsize : (Buffed.RegionMPtr.initialize b ptr hb).mem.size = b.mem.size :=
    Buffed.RegionMPtr.initialize_size b ptr hb
  have hattr : (Buffed.RegionMPtr.initialize b ptr hb).attributes = ctx.buf.attributes := by
    rw [Buffed.RegionMPtr.initialize_attributes, Buffed.IRBufContext.reserve_attributes hres]
  have hdisj := ctx.reservation_disjoint hres
  obtain ⟨hparent, hfirst, hlast⟩ := Buffed.RegionMPtr.initialize_reads b ptr hb
  apply allocReserved_sim ctx (by rw [hsize]; exact hbounds.1)
    (by rw [hsize]; exact hbounds.2) hattr ?_ hdisj hfirst hlast hparent hspec
  · intro p hp
    have hd := hdisj p hp
    simp only [show (24 : UInt64).toNat = 24 from rfl] at hd
    have hin := ctx.sim.in_bounds p hp
    change IsIncludedIN (p.range ctx.spec) _ at hin
    simp only [IsIncludedIN, ExArray.range_def] at hin
    refine ⟨by rw [hsize]; exact hbounds.1, ?_, ?_⟩
    · intro w n len hn hl
      have hdr : n.toNat + len.toNat ≤ ptr.toNat ∨ ptr.toNat + 24 ≤ n.toNat := by omega
      rw [Buffed.RegionMPtr.initialize_read_disjoint b ptr hb w n len hdr]
      exact Buffed.IRBufContext.reserve_read hres w n len (by omega)
    · intro i a hi
      simpa only [hattr] using hi
theorem Sim.RegionPtr.allocFreshRaw_fresh {ctx : Sim.IRContext OpInfo}
    {b' : Buffed.IRBufContext} {ptr : Buffed.RegionMPtr}
    (h : allocFreshRaw ctx.buf = some (b', ptr)) :
    ¬ (⟨ptr.toNat⟩ : Veir.RegionPtr).InBounds ctx.spec := by
  obtain ⟨b, hres, _⟩ := allocFreshRaw_eq h
  intro hp
  have hd := ctx.reservation_disjoint hres (.region ⟨ptr.toNat⟩) hp
  simp only [TopLevelPtr.range, Veir.RegionPtr.range, Veir.RegionPtr.toFlat, add_nat_range_def] at hd
  grind

/-- Keep reservation control flow out of callers so their ghost specification
arguments can be eliminated before the native allocator call. -/
buffed (inline := false)
def Sim.RegionPtr.allocFreshSim (ctx : Sim.IRContext OpInfo) : Option (Sim.RegionPtr × Sim.IRContext OpInfo) :=
  match h : allocFreshRaw ctx.buf with
  | none => none
  | some (b, ptr) =>
    have hsome : (Veir.RegionPtr.allocEmptyAt ctx.spec ptr.toNat).isSome := by
      simp only [Veir.RegionPtr.allocEmptyAt]
      have hf := allocFreshRaw_fresh h
      grind [Veir.RegionPtr.inBounds_def]
    let specRes := ctx.spec'.map (fun spec => (Veir.RegionPtr.allocEmptyAt spec ptr.toNat).get!)
    some (⟨ptr, specRes.map Prod.snd⟩, ⟨b, specRes.map Prod.fst, by
      rw [Erased.map_eq_mk]
      apply allocFresh_sim (sptr := specRes.out.2) h
      simpa only [specRes, Erased.map_out, Sim.IRContext.spec, Option.get!] using
        (Option.some_get! _ hsome).symm⟩)

theorem Sim.RegionPtr.allocFresh_spec' {ctx : Sim.IRContext OpInfo}
    (h : allocFresh ctx = some (ptr, ctx')) :
    Veir.RegionPtr.allocEmptyAt ctx.spec ptr.impl.toNat = some (ctx'.spec, ptr.spec) := by
  simp only [allocFresh.unfold] at h
  split at h
  · contradiction
  · rename_i b p hi
    have hf := allocFreshRaw_fresh hi
    have hs : (Veir.RegionPtr.allocEmptyAt ctx.spec p.toNat).isSome := by
      simp only [Veir.RegionPtr.allocEmptyAt]
      grind [Veir.RegionPtr.inBounds_def]
    simp_all only [Option.some.injEq, Prod.mk.injEq]
    obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := h
    simp only [Sim.IRContext.spec, Sim.RegionPtr.spec, Erased.map_out, Option.get!]
    grind

@[grind! .]
theorem Sim.RegionPtr.allocFresh_spec {ctx : Sim.IRContext OpInfo}
    (h : allocFresh ctx = some (ptr, ctx')) :
    ∃ addr, Veir.RegionPtr.allocEmptyAt ctx.spec addr = some (ctx'.spec, ptr.spec) :=
  ⟨ptr.impl.toNat, allocFresh_spec' h⟩

namespace Sim
variable {ctx ctx' : IRContext OpInfo}
@[grind =>]
theorem RegionPtr.allocFresh_genericPtr_iff (ptr : GenericPtr) (heq : allocFresh ctx = some (ptr', ctx')) :
    ptr.InBounds ctx' ↔ (ptr.InBounds ctx ∨ ptr = .fromRegion ptr') := by
  have hspec := Sim.RegionPtr.allocFresh_spec' heq
  have hlay := (Veir.RegionPtr.allocEmptyAt_preservesLayout hspec).preserves
  have hptr := Veir.RegionPtr.allocEmptyAt_ptr hspec
  constructor
  · rintro ⟨sim', ib'⟩
    rcases (Veir.RegionPtr.allocEmptyAt_genericPtr_iff ptr.spec hspec).mp ib' with hold | hnew
    · -- Old pointer: the layout is preserved, so the address is unchanged.
      refine .inl ⟨?_, hold⟩
      have := Veir.GenericPtr.layoutPreserved_same_toM hlay hold
      grind
    · -- The freshly allocated region: its impl address is forced by the sim relation.
      refine .inr ?_
      obtain ⟨impl, spec⟩ := ptr
      grind [Sim.GenericPtr.fromRegion, Veir.GenericPtr.toM,
        Veir.RegionPtr.toM]
  · rintro (hold | rfl)
    · exact ⟨Sim.GenericPtr.sim_layoutPreserved hlay hold,
        (Veir.RegionPtr.allocEmptyAt_genericPtr_iff ptr.spec hspec).mpr (.inl hold.ib)⟩
    · refine ⟨?_, (Veir.RegionPtr.allocEmptyAt_genericPtr_iff _ hspec).mpr
        (.inr (by grind [Sim.GenericPtr.fromRegion]))⟩
      grind [Sim.GenericPtr.fromRegion, Veir.GenericPtr.toM,
        Veir.RegionPtr.toM]

@[grind .]
theorem RegionPtr.allocFresh_newBlock_inBounds (heq : allocFresh ctx = some (ptr, ctx')) :
    ptr.InBounds ctx' :=
  (Sim.GenericPtr.iff_region ptr).mp
    ((RegionPtr.allocFresh_genericPtr_iff (.fromRegion ptr) heq).mpr (.inr rfl))

@[grind .]
theorem RegionPtr.allocFresh_genericPtr_mono (ptr : GenericPtr) (heq : allocFresh ctx = some (ptr', ctx')) :
    ptr.InBounds ctx → ptr.InBounds ctx' := by
  grind

@[grind .]
theorem RegionPtr.allocFresh_genericPtr_veir_mono (ptr : Veir.GenericPtr) (heq : allocFresh ctx = some (ptr', ctx')) :
    ptr.InBounds ctx.spec → ptr.InBounds ctx'.spec := by
  have hspec := Sim.RegionPtr.allocFresh_spec' heq
  grind

@[grind .]
theorem RegionPtr.allocFresh_not_inBounds (heq : allocFresh ctx = some (ptr', ctx')) :
    ¬ ptr'.spec.InBounds ctx.spec :=
  Veir.RegionPtr.allocEmptyAt_newBlock_not_inBounds (Sim.RegionPtr.allocFresh_spec' heq)
end Sim

end Veir
