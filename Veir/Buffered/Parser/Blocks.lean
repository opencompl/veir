module

public import Veir.Buffered.Parser.Retire

@[expose] public section
namespace Veir.Buffered.Parser
namespace MlirParserData

@[simp]
theorem forwardBlock_putDefined {d : MlirParserData} {name block loc scope n p l} :
    (d.putBlock name (.Defined block loc)).blockEntry? scope n = some (.ForwardDeclared p l) ↔
      (scope ≠ 0 ∨ n ≠ name) ∧ d.blockEntry? scope n = some (.ForwardDeclared p l) := by
  rw [blockEntry_putBlock]
  simp

/-- Defining the current name may consume that name's placeholder, but cannot introduce
an alias to any other privately owned forward block. -/
theorem Live.putDefinedBlock {d : MlirParserData} {ctx : IR.RawContext} (h : d.Live ctx)
    (name : ByteArray) (block : IR.Block) (loc : Location) (hb : block.InBounds ctx)
    (apart : ∀ scope n p l, d.blockEntry? scope n = some (.ForwardDeclared p l) →
      (scope = 0 ∧ n = name) ∨ block.spec ≠ p.spec) :
    (d.putBlock name (.Defined block loc)).Live ctx := by
  constructor
  · exact h.values
  · intro scope n e he
    rcases blockEntry_putBlock.mp he with ⟨rfl, rfl, rfl⟩ | ⟨_, he⟩
    · exact hb
    · exact h.blocks scope n e he
  · exact h.forward
  · exact h.unique
  · exact h.privateValues
  · intro scope n p l he scope' n' e he' hs
    rw [forwardBlock_putDefined (d := d)] at he
    obtain ⟨outside, he⟩ := he
    rcases (blockEntry_putBlock (d := d)).mp he' with ⟨rfl, rfl, rfl⟩ | ⟨_, he'⟩
    · rcases apart scope n p l he with ⟨rfl, rfl⟩ | hne
      · simp at outside
      · exact False.elim (hne hs.symm)
    · exact h.uniqueBlocks scope n p l he scope' n' e he' hs

end MlirParserData

def ArgumentLive (ctx : IR.RawContext) (p : IR.Block) (index : UInt64) : Prop :=
  ∃ v : IR.Value, v.InBounds ctx ∧ v.spec = .blockArgument ⟨p.spec, index.toNat⟩

theorem ArgumentLive.inBounds {ctx : IR.RawContext} {p : IR.Block} {index : UInt64}
    (h : ArgumentLive ctx p index) (hp : p.InBounds ctx) :
    (Sim.ValuePtr.fromBlockArgumentPtr (p.getArgumentPtr ctx index hp)).InBounds ctx := by
  obtain ⟨v, hv, hs⟩ := h
  have hvib := hv.ib
  have hi : index.toNat < p.spec.getNumArguments! ctx.spec := by
    rw [hs] at hvib
    have harg : (BlockArgumentPtr.mk p.spec index.toNat).InBounds ctx.spec := by
      simpa only [ValuePtr.inBounds_blockArg] using hvib
    grind [BlockArgumentPtr.inBounds_def]
  grind [generic_ptr_grind]

theorem argument_stable {d : MlirParserData} {v : IR.Value} {arg : BlockArgumentPtr}
    (hs : v.spec = .blockArgument arg) : d.StableValue v := by
  intro n i op l he res hr
  rw [hs] at hr
  cases hr

structure DefinedBlock (before : StaticParserState) (count : Nat) extends ParsedBlock before where
  arguments : ∀ i : Fin count, ArgumentLive state.ctx.raw pointer i.val.toUInt64
  suspended : state.data.blockScopes = before.data.blockScopes

/-- Publishing a block definition only removes forward ownership. -/
theorem definedBlock_frame {s : StaticParserState} {ctx : StaticIR.Context}
    (frame : StaticIR.Preserves s.ctx.raw ctx.raw) {name block loc}
    (live : (s.data.putBlock name (.Defined block loc)).Live ctx.raw) :
    ParserFrame s ⟨s.data.putBlock name (.Defined block loc), ctx, live⟩ := by
  constructor
  · intro p hp stable; exact ⟨frame.operation hp, stable⟩
  · intro p hp stable
    exact ⟨frame.block hp, fun scope n q l he =>
      stable scope n q l (MlirParserData.forwardBlock_putDefined.mp he).2⟩
  · intro p hp stable; exact ⟨frame.value hp, stable⟩
  · exact fun _ hp => frame.region hp

def StaticParserState.defineBlock (s : StaticParserState) (name : ByteArray) (types : Array TypeAttr)
    (region : IR.Region) (loc : Location) : region.InBounds s.ctx.raw →
    Except ParserError (DefinedBlock s types.size) :=
  s.consume (α := fun s => region.InBounds s.ctx.raw → Except ParserError (DefinedBlock s types.size))
    fun data ctx live hr => do
      let ip := StaticIR.regionEnd ctx.raw region hr
      match he : data.blocks[name]? with
      | some (.Defined _ previous) =>
        throw ((ParserError.mk s!"block %{String.fromUTF8! name} has already been defined" (some loc) []).addNote
          previous "block previously defined here")
      | none =>
        let some allocated := StaticIR.createBlock ctx types (some ip.val)
            (by simpa using ip.property.1) (by simpa using ip.property.2)
          | throw (ParserError.mk "internal error: failed to create block" (some loc) [])
        have apart : ∀ scope n p l, data.blockEntry? scope n = some (.ForwardDeclared p l) →
            (scope = 0 ∧ n = name) ∨ allocated.pointer.spec ≠ p.spec := by
          intro scope n p l hentry
          right
          intro hs
          apply allocated.fresh
          rw [hs]
          exact (live.blocks scope n (.ForwardDeclared p l) hentry).ib
        have hlive := (live.mono allocated.preserves).putDefinedBlock name allocated.pointer loc allocated.inBounds apart
        let next : StaticParserState := ⟨data.putBlock name (.Defined allocated.pointer loc), allocated.ctx, hlive⟩
        have named : next.data.blockEntry? 0 name = some (.Defined allocated.pointer loc) := by
          simp [next, MlirParserData.blockEntry?, MlirParserData.putBlock]
        return ⟨⟨⟨next, definedBlock_frame allocated.preserves hlive⟩, allocated.pointer,
          allocated.inBounds, hlive.definedBlock_stable named⟩,
          fun i => ⟨(allocated.argument i).val, (allocated.argument i).property⟩, rfl⟩
      | some (.ForwardDeclared old previous) =>
        have hentry : data.blockEntry? 0 name = some (.ForwardDeclared old previous) := he
        have hold := live.blocks 0 name (.ForwardDeclared old previous) hentry
        if hzero : types.size = 0 then
          let some inserted := StaticIR.insertBlock ctx old ip.val hold ip.property.1 ip.property.2
            | throw (ParserError.mk "internal error: failed to insert block" (some loc) [])
          have apart : ∀ scope n p l, data.blockEntry? scope n = some (.ForwardDeclared p l) →
              (scope = 0 ∧ n = name) ∨ old.spec ≠ p.spec := by
            intro scope n p l hp
            by_cases hs : old.spec = p.spec
            · exact Or.inl (live.uniqueBlocks scope n p l hp 0 name (.ForwardDeclared old previous) hentry hs.symm)
            · exact Or.inr hs
          have hb := inserted.preserves.block hold
          have hlive := (live.mono inserted.preserves).putDefinedBlock name old loc hb apart
          let next : StaticParserState := ⟨data.putBlock name (.Defined old loc), inserted.ctx, hlive⟩
          have named : next.data.blockEntry? 0 name = some (.Defined old loc) := by
            simp [next, MlirParserData.blockEntry?, MlirParserData.putBlock]
          return ⟨⟨⟨next, definedBlock_frame inserted.preserves hlive⟩, old, hb,
            hlive.definedBlock_stable named⟩, fun i => False.elim (by have := i.isLt; omega), rfl⟩
        else
          let some allocated := StaticIR.createBlock ctx types (some ip.val)
              (by simpa using ip.property.1) (by simpa using ip.property.2)
            | throw (ParserError.mk "internal error: failed to create block" (some loc) [])
          let block := allocated.pointer
          let some rewired := StaticIR.replaceBlockUses allocated.ctx old block
              (allocated.preserves.block hold) allocated.inBounds
            | throw (ParserError.mk "internal error: failed to redirect successors" (some loc) [])
          have mono := allocated.preserves.trans rewired.preserves
          have hcurrent := live.mono mono
          let taken := data.takeBlockName name
          let some deleted := StaticIR.eraseBlock rewired.ctx old (mono.block hold)
            | throw (ParserError.mk "internal error: forward-declared block is not safe to erase" (some loc) [])
          have htaken := (hcurrent.takeBlockName name).eraseBlock (hcurrent.takeBlockName_canDelete hentry) deleted
          have apart : ∀ scope n p l, taken.blockEntry? scope n = some (.ForwardDeclared p l) →
              (scope = 0 ∧ n = name) ∨ block.spec ≠ p.spec := by
            intro scope n p l hp
            right
            intro hs
            apply allocated.fresh
            rw [hs]
            exact (live.blocks scope n (.ForwardDeclared p l) (MlirParserData.blockEntry_takeBlockName.mp hp).2).ib
          have hn : block.spec ≠ old.spec := by
            intro hs
            apply allocated.fresh
            rw [hs]
            exact hold.ib
          have hb := deleted.blocks block (rewired.preserves.block allocated.inBounds) hn
          have hlive := htaken.putDefinedBlock name block loc hb apart
          let next : StaticParserState := ⟨taken.putBlock name (.Defined block loc), deleted.ctx, hlive⟩
          have named : next.data.blockEntry? 0 name = some (.Defined block loc) := by
            simp [next, MlirParserData.blockEntry?, MlirParserData.putBlock]
          have frame : ParserFrame ⟨data, ctx, live⟩ next := by
            constructor
            · intro p hp stable
              exact ⟨deleted.operations p (mono.operation hp), stable⟩
            · intro p hp stable
              refine ⟨deleted.blocks p (mono.block hp) (stable 0 name old previous hentry), ?_⟩
              intro scope n q l he
              have he' := (MlirParserData.forwardBlock_putDefined.mp he).2
              exact stable scope n q l (MlirParserData.blockEntry_takeBlockName.mp he').2
            · intro p hp stable
              exact ⟨deleted.values p (mono.value hp), stable⟩
            · intro p hp; exact deleted.regions p (mono.region hp)
          return ⟨⟨⟨next, frame⟩, block, hb, hlive.definedBlock_stable named⟩,
            fun i => ⟨(allocated.argument i).val,
              deleted.values _ (rewired.preserves.value (allocated.argument i).property.1),
              (allocated.argument i).property.2⟩, rfl⟩

structure BorrowedBlock (before : StaticParserState) (name : ByteArray) extends ParserStep before where
  pointer : IR.Block
  inBounds : pointer.InBounds state.ctx.raw
  named : ∃ entry, state.data.blockEntry? 0 name = some entry ∧ entry.block = pointer
  preserves : StaticIR.Preserves before.ctx.raw state.ctx.raw
  bindings : ∀ scope n entry, before.data.blockEntry? scope n = some entry →
    state.data.blockEntry? scope n = some entry
  suspended : state.data.blockScopes = before.data.blockScopes

/-- The successor resolver exports both allocation-only and permanent-handle frames. -/
def StaticParserState.borrowBlock (s : StaticParserState) (name : ByteArray) (loc : Location) :
    Except ParserError (BorrowedBlock s name) := do
  let some resolved := s.useBlock name loc
    | throw (ParserError.mk "internal error: failed to create block" (some loc) [])
  have ho : ∀ n i p l, resolved.state.data.ForwardEntry n i p l ↔ s.data.ForwardEntry n i p l := by
    intros
    simp only [MlirParserData.ForwardEntry, resolved.forwardValues]
  have frame : ParserFrame s resolved.state := by
    constructor
    · intro p hp stable
      exact ⟨resolved.preserves.operation hp, fun n i op l he => stable n i op l ((ho ..).mp he)⟩
    · intro p hp stable
      refine ⟨resolved.preserves.block hp, ?_⟩
      intro scope n q l he hs
      rcases resolved.origins scope n q l he with old | fresh
      · exact stable scope n q l old hs
      · exact fresh (hs ▸ hp.ib)
    · intro p hp stable
      exact ⟨resolved.preserves.value hp, fun n i op l he => stable n i op l ((ho ..).mp he)⟩
    · exact fun _ hp => resolved.preserves.region hp
  return ⟨⟨resolved.state, frame⟩, resolved.block, resolved.inBounds, resolved.named,
    resolved.preserves, resolved.bindings, resolved.suspended⟩

end Veir.Buffered.Parser
