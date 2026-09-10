module

public import ExArray.CompilerExtras

public import Veir.IR.Buffed.Recycling
public import Veir.IR.Buffed.InBounds
import all Veir.IR.Buffed.Basic

@[expose] public section
namespace Veir
open Buffed (countCard)
variable [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo]
set_option maxHeartbeats 1000000
@[noinline, nospecialize]
def Sim.OperationPtr.allocationSpec (ctx : Veir.IRContext OpInfo) (addr : Nat) (opType : OpInfo)
    (properties : HasOpInfo.propertiesOf opType) (cr cb cg co : Nat) :
    Option (Veir.IRContext OpInfo × Veir.OperationPtr) :=
  Veir.OperationPtr.allocEmptyAt ctx opType properties cr cb cg co addr

theorem Sim.OperationPtr.reserved_header_bounds
    {b₀ b : Buffed.IRBufContext} {address nr no nb ng : UInt64} {op : OpInfo}
    (hr : nr.toNat ≤ countCard) (ho : no.toNat ≤ countCard)
    (hbo : nb.toNat ≤ countCard) (hg : ng.toNat ≤ countCard)
    (hres : b₀.reserve (Buffed.OperationMPtr.computeOperationSize nr no nb ng
      (Buffed.Operation.propertySize op)) = some (b, address)) :
    (address + 40 * nr).toNat = address.toNat + nr.toNat * 40 ∧
    (address + 40 * nr).toNat + 72 + (Buffed.Operation.propertySize op).toNat ≤ b.mem.size := by
  have hs := Buffed.IRBufContext.reserve_bounds hres |>.2
  have hc := Buffed.OperationMPtr.computeOperationSize_toNat nr no nb ng
    (Buffed.Operation.propertySize op) hr ho hbo hg (Nat.le_of_lt HasDialectOpInfo.propertySize_small)
  have hf := b.mem.fits_in_memory
  simp only [show Buffed.OpResult.size.toNat = 40 from rfl,
    show Buffed.Operation.sizeBase.toNat = 72 from rfl, Int64.maxNatValue] at *
  have hptr : (address + 40 * nr).toNat = address.toNat + nr.toNat * 40 := by
    rw [UInt64.toNat_add, UInt64.toNat_mul]
    simp only [show (40 : UInt64).toNat = 40 from rfl]
    omega
  exact ⟨hptr, by omega⟩

@[inline]
def Sim.OperationPtr.allocRecycledRaw (ctx : Buffed.IRBufContext) (op : OpInfo)
    (props : HasOpInfo.propertiesOf op) (nr no nb ng : UInt64)
    (hr : nr.toNat ≤ countCard) (ho : no.toNat ≤ countCard)
    (hbo : nb.toNat ≤ countCard) (hg : ng.toNat ≤ countCard) :
    Option (Buffed.IRBufContext × Buffed.OperationMPtr) :=
  if ha : ctx.attributes.size < 2^63 then
    match hres : ctx.reserve (Buffed.OperationMPtr.computeOperationSize nr no nb ng
        (Buffed.Operation.propertySize op)) with
    | none => none
    | some (b, address) =>
      let ptr := address + 40 * nr
      some (Buffed.OperationMPtr.initializeOp b ptr nr no nb ng op props
        (reserved_header_bounds hr ho hbo hg hres |>.2)
        (by rw [Buffed.IRBufContext.reserve_attributes hres]; exact ha), ptr)
  else none

theorem Sim.OperationPtr.allocRecycledRaw_eq
    {ctx b' : Buffed.IRBufContext} {op : OpInfo} {props : HasOpInfo.propertiesOf op}
    {nr no nb ng : UInt64} {hr ho hbo hg} {ptr : Buffed.OperationMPtr}
    (h : allocRecycledRaw ctx op props nr no nb ng hr ho hbo hg = some (b', ptr)) :
    ∃ b address,
      ctx.reserve (Buffed.OperationMPtr.computeOperationSize nr no nb ng
        (Buffed.Operation.propertySize op)) = some (b, address) ∧
      ptr = address + 40 * nr ∧
      ∃ hb ha, b' = Buffed.OperationMPtr.initializeOp b ptr nr no nb ng op props hb ha := by
  unfold allocRecycledRaw at h
  split at h
  · split at h
    · contradiction
    · rename_i b address hres
      obtain ⟨rfl, rfl⟩ := Option.some.inj h
      exact ⟨b, address, hres, rfl, _, _, rfl⟩
  · contradiction


theorem Sim.OperationPtr.allocRecycled_sim
    {ctx : Sim.IRContext OpInfo} {op : OpInfo} {props : HasOpInfo.propertiesOf op}
    {nr no nb ng : UInt64} {hr ho hbo hg} {b' : Buffed.IRBufContext} {ptr : Buffed.OperationMPtr}
    {spec : Veir.IRContext OpInfo} {sptr : Veir.OperationPtr}
    (h : allocRecycledRaw ctx.buf op props nr no nb ng hr ho hbo hg = some (b', ptr))
    (hspec : Veir.OperationPtr.allocEmptyAt ctx.spec op props nr.toNat nb.toNat ng.toNat no.toNat
      ptr.toNat = some (spec, sptr)) : Veir.Sim ⟨b', spec⟩ := by
  obtain ⟨b, address, hres, rfl, hb, ha, rfl⟩ := allocRecycledRaw_eq h
  let ptr := address + 40 * nr
  have hptr := reserved_header_bounds hr ho hbo hg hres |>.1
  have hbounds := Buffed.IRBufContext.reserve_bounds hres
  have hcompute := Buffed.OperationMPtr.computeOperationSize_toNat nr no nb ng
    (Buffed.Operation.propertySize op) hr ho hbo hg (Nat.le_of_lt HasDialectOpInfo.propertySize_small)
  have hattrs := Buffed.IRBufContext.reserve_attributes hres
  have hdisj := ctx.reservation_disjoint hres
  have hsize := Buffed.OperationMPtr.initializeOp_size b ptr nr no nb ng op props hb ha
  have hfree := Buffed.OperationMPtr.initializeOp_freeList b ptr nr no nb ng op props hb ha
  obtain ⟨hno, hnr, hnb, hng, hpar, hnext, hprev, hty, hattr⟩ :=
    Buffed.OperationMPtr.initializeOp_reads b ptr nr no nb ng op props hb ha
  apply allocReserved_sim (h₁ := hr) (h₂ := ho) (h₃ := hbo) (h₄ := hg)
    (start := address.toNat) hptr (by rw [hsize]; exact hbounds.1)
    (by rw [hsize]; exact hbounds.2) ?_ ?_ hdisj
    hnr hno hnb hng hprev hnext hpar hty hattr
    (Buffed.OperationMPtr.initializeOp_property b ptr nr no nb ng op props hb ha)
    ?_ ?_ ?_ hspec
  · intro i a hi
    apply Buffed.OperationMPtr.initializeOp_attributes
    rwa [hattrs]
  · intro p hp
    have hd := hdisj p hp
    have hin := ctx.sim.in_bounds p hp
    simp only [IsIncludedIN, ExArray.range_def] at hin
    refine ⟨by rw [hsize]; exact hbounds.1, ?_, ?_⟩
    · intro w n len hn hl
      have hold : n.toNat + len.toNat ≤ ctx.buf.mem.size := by omega
      have hdr : n.toNat + len.toNat ≤ address.toNat ∨
          address.toNat + (Buffed.OperationMPtr.computeOperationSize nr no nb ng
            (Buffed.Operation.propertySize op)).toNat ≤ n.toNat := by omega
      rw [Buffed.OperationMPtr.initializeOp_read_disjoint b ptr nr no nb ng op props hb ha
        w n len (by
          simp only [ptr] at *
          simp only [show Buffed.OpResult.size.toNat = 40 from rfl,
            show Buffed.Operation.sizeBase.toNat = 72 from rfl] at hcompute
          omega)]
      exact Buffed.IRBufContext.reserve_read_disjoint hres w n len hold hdr
    · intro i a hi
      apply Buffed.OperationMPtr.initializeOp_attributes
      rwa [hattrs]
  · rw [hfree, hsize]
    exact Buffed.IRBufContext.reserve_free_valid ctx.sim.free_valid hres
  · intro s a hm p hp
    rw [hfree] at hm
    exact ctx.sim.free_disjoint s a (Buffed.IRBufContext.reserve_free_subset hres s a hm) p hp
  · intro s a hm
    rw [hfree] at hm
    exact Buffed.IRBufContext.reserve_free_disjoint ctx.sim.free_valid hres s a hm


theorem Sim.OperationPtr.allocRecycledRaw_fresh
    {ctx : Sim.IRContext OpInfo} {op : OpInfo} {props : HasOpInfo.propertiesOf op}
    {nr no nb ng : UInt64} {hr ho hbo hg} {b' : Buffed.IRBufContext} {ptr : Buffed.OperationMPtr}
    (h : allocRecycledRaw ctx.buf op props nr no nb ng hr ho hbo hg = some (b', ptr)) :
    ¬ (⟨ptr.toNat⟩ : Veir.OperationPtr).InBounds ctx.spec := by
  obtain ⟨b, address, hres, rfl, hb, ha, _⟩ := allocRecycledRaw_eq h
  have hptr := reserved_header_bounds hr ho hbo hg hres |>.1
  have hc := Buffed.OperationMPtr.computeOperationSize_toNat nr no nb ng
    (Buffed.Operation.propertySize op) hr ho hbo hg (Nat.le_of_lt HasDialectOpInfo.propertySize_small)
  apply reservation_fresh ctx hres (by omega)
  simp only [show Buffed.OpResult.size.toNat = 40 from rfl,
    show Buffed.Operation.sizeBase.toNat = 72 from rfl] at hc
  omega

/-- Keep reservation control flow out of callers so their ghost specification
arguments can be eliminated before the native allocator call. -/
buffed (inline := false)
def Sim.OperationPtr.allocRecycledSim (ctx : Sim.IRContext OpInfo) (op : OpInfo)
    (props : HasOpInfo.propertiesOf op) (nr no nb ng : UInt64)
    (hr : nr.toNat ≤ countCard) (ho : no.toNat ≤ countCard)
    (hbo : nb.toNat ≤ countCard) (hg : ng.toNat ≤ countCard) :
    Option (Sim.OperationPtr × Sim.IRContext OpInfo) :=
  match h : allocRecycledRaw ctx.buf op props nr no nb ng hr ho hbo hg with
  | none => none
  | some (b, ptr) =>
    have hsome : (allocationSpec ctx.spec ptr.toNat op props nr.toNat nb.toNat ng.toNat no.toNat).isSome := by
      apply Veir.OperationPtr.allocEmptyAt_isSome_of_not_mem
      exact allocRecycledRaw_fresh h
    let specRes := (allocationSpec ctx.spec ptr.toNat op props nr.toNat nb.toNat ng.toNat no.toNat).specGet!
    some (⟨ptr, specRes.2⟩, ⟨b, specRes.1, by
      apply allocRecycled_sim (sptr := specRes.2) h
      show allocationSpec ctx.spec ptr.toNat op props nr.toNat nb.toNat ng.toNat no.toNat = some specRes
      simp only [specRes, Option.specGet!]
      exact (Option.some_get! _ hsome).symm⟩)

theorem Sim.OperationPtr.allocRecycled_spec' {ctx : Sim.IRContext OpInfo} :
    allocRecycled ctx op props nr no nb ng hr ho hbo hg = some (ptr, ctx') →
    Veir.OperationPtr.allocEmptyAt ctx.spec op props nr.toNat nb.toNat ng.toNat no.toNat
      ptr.impl.toNat = some (ctx'.spec, ptr.spec) := by
  simp only [allocRecycled_def, allocRecycledSim, allocationSpec]
  split
  · simp
  · rename_i b p h
    intro heq
    have hsome := Veir.OperationPtr.allocEmptyAt_isSome_of_not_mem
      (opType := op) (properties := props) (capResults := nr.toNat)
      (capBlockOperands := nb.toNat) (capRegions := ng.toNat) (capOperands := no.toNat)
      (allocRecycledRaw_fresh h)
    simp_all only [Option.some.injEq, Prod.mk.injEq]
    obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := heq
    simp only [Option.specGet!]
    grind

@[grind! .]
theorem Sim.OperationPtr.allocRecycled_spec {ctx : Sim.IRContext OpInfo} :
    allocRecycled ctx op props nr no nb ng hr ho hbo hg = some (ptr, ctx') →
    ∃ addr, Veir.OperationPtr.allocEmptyAt ctx.spec op props nr.toNat nb.toNat ng.toNat no.toNat
      addr = some (ctx'.spec, ptr.spec) := by
  intro h
  exact ⟨ptr.impl.toNat, allocRecycled_spec' h⟩

namespace Sim
variable {ctx ctx' : IRContext OpInfo}
@[grind =>]
theorem OperationPtr.allocRecycled_genericPtr_iff (ptr : GenericPtr)
    (heq : allocRecycled ctx type properties c₁ c₂ c₃ c₄ h₁ h₂ h₃ h₄ = some (ptr', ctx')) :
    ptr.InBounds ctx' ↔ (ptr.InBounds ctx ∨ ptr = .fromOperation ptr') := by
  have hspec := Sim.OperationPtr.allocRecycled_spec' heq
  have hlay := Veir.OperationPtr.allocEmptyAt_preservesLayout hspec
  have hptr := Veir.OperationPtr.allocEmptyAt_ptr_eq hspec
  constructor
  · rintro ⟨sim', ib'⟩
    rcases (Veir.OperationPtr.allocEmptyAt_genericPtr_iff ptr.spec hspec).mp ib' with hold | hnew
    · -- Old pointer: the layout is preserved, so the address is unchanged.
      refine .inl ⟨?_, hold⟩
      have := Veir.GenericPtr.layoutPreserved_same_toM hlay hold
      grind
    · -- The freshly allocated operation: its impl address is forced by the sim relation.
      refine .inr ?_
      obtain ⟨impl, spec⟩ := ptr
      grind [Sim.GenericPtr.fromOperation, Veir.GenericPtr.toM,
        Veir.OperationPtr.toM]
  · rintro (hold | rfl)
    · exact ⟨Sim.GenericPtr.sim_layoutPreserved hlay hold,
        (Veir.OperationPtr.allocEmptyAt_genericPtr_iff ptr.spec hspec).mpr (.inl hold.ib)⟩
    · refine ⟨?_, (Veir.OperationPtr.allocEmptyAt_genericPtr_iff _ hspec).mpr (.inr (by grind [Sim.GenericPtr.fromOperation]))⟩
      grind [Sim.GenericPtr.fromOperation, Veir.GenericPtr.toM, Veir.OperationPtr.toM]

theorem OperationPtr.allocRecycled_operationPtr_iff (ptr : OperationPtr)
    (heq : allocRecycled ctx type properties c₁ c₂ c₃ c₄ h₁ h₂ h₃ h₄ = some (ptr', ctx')) :
    ptr.InBounds ctx' ↔ (ptr.InBounds ctx ∨ ptr =  ptr') := by
  grind [generic_ptr_grind, Sim.OperationPtr]

@[grind . ]
theorem OperationPtr.allocRecycled_genericPtr_mono (ptr : GenericPtr)
    (heq : allocRecycled ctx type properties c₁ c₂ c₃ c₄ h₁ h₂ h₃ h₄ = some (ptr', ctx')) :
    ptr.InBounds ctx → ptr.InBounds ctx' := by
  grind

@[grind .]
theorem OperationPtr.allocRecycled_newBlock_inBounds
    (heq : allocRecycled ctx type properties c₁ c₂ c₃ c₄ h₁ h₂ h₃ h₄ = some (ptr', ctx')) :
    ptr'.InBounds ctx' := by
  have := (OperationPtr.allocRecycled_genericPtr_iff (.fromOperation ptr') heq).mpr (.inr rfl)
  grind [generic_ptr_grind]

@[grind .]
theorem OperationPtr.allocRecycled_newBlock_veir_inBounds {ptr : Veir.GenericPtr}
    (heq : allocRecycled ctx type properties c₁ c₂ c₃ c₄ h₁ h₂ h₃ h₄ = some (ptr', ctx')) :
    ptr.InBounds ctx.spec → ptr.InBounds ctx'.spec := by
  have hspec := Sim.OperationPtr.allocRecycled_spec' heq
  grind

@[grind .]
theorem OperationPtr.allocRecycled_not_inBounds
    (heq : allocRecycled ctx type properties c₁ c₂ c₃ c₄ h₁ h₂ h₃ h₄ = some (ptr', ctx')) :
    ¬ ptr'.spec.InBounds ctx.spec :=
  Veir.OperationPtr.allocEmptyAt_not_inBounds (Sim.OperationPtr.allocRecycled_spec' heq)
end Sim

end Veir
