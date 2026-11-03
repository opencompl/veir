module

public import Veir.Buffered.Parser.Blocks
import all Veir.Buffered.IR.Buffed.Sim
import all Veir.Buffered.IR.Buffed.Basic

@[expose] public section
namespace Veir.Buffered.Parser

def ResultLive (ctx : IR.RawContext) (p : IR.Op) (index : UInt64) : Prop :=
  ∃ v : IR.Value, v.InBounds ctx ∧ v.spec = .opResult ⟨p.spec, index.toNat⟩

theorem ResultLive.inBounds {ctx : IR.RawContext} {p : IR.Op} {index : UInt64}
    (h : ResultLive ctx p index) (hp : p.InBounds ctx) :
    (Sim.ValuePtr.fromOpResultPtr (p.getResultPtr ctx index hp)).InBounds ctx := by
  obtain ⟨v, hv, hs⟩ := h
  have hvib := hv.ib
  have hi : index.toNat < p.spec.getNumResults! ctx.spec := by
    rw [hs] at hvib
    have hres : (OpResultPtr.mk p.spec index.toNat).InBounds ctx.spec := by
      simpa only [ValuePtr.inBounds_opResult] using hvib
    grind [OpResultPtr.inBounds_def]
  grind [generic_ptr_grind]

def ResultLive.value (ctx : IR.RawContext) (p : IR.Op) (index : UInt64)
    (hp : p.InBounds ctx) (h : ResultLive ctx p index) :
    { v : IR.Value // v.InBounds ctx ∧ v.spec = .opResult ⟨p.spec, index.toNat⟩ } :=
  ⟨Sim.ValuePtr.fromOpResultPtr (p.getResultPtr ctx index hp), h.inBounds hp, by
    simp [Sim.ValuePtr.fromOpResultPtr, Sim.ValuePtr.spec, Sim.OperationPtr.getResultPtr.unfold,
      OperationPtr.getResult, Sim.OperationPtr.spec, Erased.map_out]⟩

def ArgumentLive.value (ctx : IR.RawContext) (p : IR.Block) (index : UInt64)
    (hp : p.InBounds ctx) (h : ArgumentLive ctx p index) :
    { v : IR.Value // v.InBounds ctx ∧ v.spec = .blockArgument ⟨p.spec, index.toNat⟩ } :=
  ⟨Sim.ValuePtr.fromBlockArgumentPtr (p.getArgumentPtr ctx index hp), h.inBounds hp, by
    simp [Sim.ValuePtr.fromBlockArgumentPtr, Sim.ValuePtr.spec, Sim.BlockPtr.getArgumentPtr.unfold,
      BlockPtr.getArgument, Sim.BlockPtr.spec, Erased.map_out]⟩

theorem result_stable {d : MlirParserData} {p : IR.Op} {v : IR.Value} {index : Nat}
    (stable : d.StableOp p) (hs : v.spec = .opResult ⟨p.spec, index⟩) : d.StableValue v := by
  intro n i op loc he res hr
  simp only [hs, ValuePtr.opResult.injEq] at hr
  cases hr
  exact stable n i op loc he

structure ConstructedOperation (before : StaticParserState) (count : Nat) extends ParsedOperation before where
  results : ∀ i : Fin count, ResultLive state.ctx.raw pointer i.val.toUInt64
  blocks : state.data.blocks = before.data.blocks
  suspended : state.data.blockScopes = before.data.blockScopes

/-- A detached operation or the end of a known block. No Nat-to-address round-trip test is
needed: the insertion point is constructed from the certified physical pointer. -/
def operationIP (ctx : IR.RawContext) (parent : Option IR.Block) :
    (∀ p ∈ parent, p.InBounds ctx) →
    { ip : Option InsertPoint // ip.maybe InsertPoint.InBounds ctx.spec ∧ ip.maybe₁ InsertPoint.IsRepr } :=
  match parent with
  | none => fun _ => ⟨none, by simp, by simp⟩
  | some p => fun hp =>
    let ip := StaticIR.blockEnd ctx p (hp p (by simp))
    ⟨some ip.val, by simpa using ip.property.1, by simpa using ip.property.2⟩

def StaticParserState.constructOp (s : StaticParserState) (code : OpCode) (types : Array TypeAttr)
    (operands : Array IR.Value) (successors : Array IR.Block) (regions : Array IR.Region)
    (properties : propertiesOf code) (attrs : DictionaryAttr) (parent : Option IR.Block) (loc : Location) :
    (∀ v ∈ operands, v.InBounds s.ctx.raw) →
    (∀ p ∈ successors, p.InBounds s.ctx.raw) →
    (∀ p ∈ regions, p.InBounds s.ctx.raw) →
    (∀ p ∈ parent, p.InBounds s.ctx.raw) →
    Except ParserError (ConstructedOperation s types.size) :=
  s.consume (α := fun s => (∀ v ∈ operands, v.InBounds s.ctx.raw) →
    (∀ p ∈ successors, p.InBounds s.ctx.raw) → (∀ p ∈ regions, p.InBounds s.ctx.raw) →
    (∀ p ∈ parent, p.InBounds s.ctx.raw) → Except ParserError (ConstructedOperation s types.size))
    fun data ctx live ho hb hr hparent => do
      let ip := operationIP ctx.raw parent hparent
      let some allocation := StaticIR.createOp ctx code types operands successors regions properties ip.val
          (by intro i hi; exact ho _ (by grind)) (by intro i hi; exact hb _ (by grind))
          (by intro i hi; exact hr _ (by grind)) ip.property.1 ip.property.2
        | throw (ParserError.mk "internal error: failed to create operation" (some loc) [])
      let op := allocation.pointer
      let base := allocation.ctx
      let updated : StaticIR.Mutation base.raw ←
        if attrs.entries.isEmpty then pure ⟨base, StaticIR.Preserves.refl base.raw⟩
        else match StaticIR.setAttributes base op attrs allocation.inBounds with
          | none => throw (ParserError.mk "internal error: failed to set the operation attributes" (some loc) [])
          | some updated => pure updated
      have mono := allocation.preserves.trans updated.preserves
      let nextData : MlirParserData := { data with opLocations := data.opLocations.insert op.impl loc }
      have hl : nextData.Live updated.ctx.raw := (live.mono mono).sameReferences rfl rfl rfl rfl
      let next : StaticParserState := ⟨nextData, updated.ctx, hl⟩
      have stable : next.data.StableOp op := by
        intro n i p l he hs
        apply allocation.fresh
        rw [hs]
        exact (live.forward n i p l he).1.ib
      return ⟨⟨⟨next, ParserFrame.mono mono rfl rfl rfl⟩, op,
        updated.preserves.operation allocation.inBounds, stable⟩,
        fun i => ⟨(allocation.result i).val, updated.preserves.value (allocation.result i).property.1,
          (allocation.result i).property.2⟩, rfl, rfl⟩

end Veir.Buffered.Parser
