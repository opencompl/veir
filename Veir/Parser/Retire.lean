module

public import Veir.Parser.References

@[expose] public section
namespace Veir.Parser

abbrev OwnedPlaceholder := Nat × IR.Op × Location

def AvoidOps (pending : List OwnedPlaceholder) (p : IR.Op) : Prop :=
  ∀ e ∈ pending, p.spec ≠ e.2.1.spec

def AvoidValues (pending : List OwnedPlaceholder) (v : IR.Value) : Prop :=
  ∀ e ∈ pending, ∀ res, v.spec = .opResult res → res.op ≠ e.2.1.spec

structure RetirementFrame (before after : IR.RawContext) (pending : List OwnedPlaceholder) : Prop where
  operations : ∀ p : IR.Op, p.InBounds before → AvoidOps pending p → p.InBounds after
  blocks : ∀ p : IR.Block, p.InBounds before → p.InBounds after
  regions : ∀ p : IR.Region, p.InBounds before → p.InBounds after
  values : ∀ p : IR.Value, p.InBounds before → AvoidValues pending p → p.InBounds after

structure Retired (data : MlirParserData) (before : IR.RawContext) (pending : List OwnedPlaceholder) where
  ctx : StaticIR.Context
  live : data.Live ctx.raw
  frame : RetirementFrame before ctx.raw pending

/-- Consume a privately owned list. Distinctness and the deletion frames protect the tail,
the published name tables, and the real values held by the caller. No address lookup occurs
in this loop. The name has already been removed atomically from the public table. -/
def retirePlaceholders (data : MlirParserData) (ctx : StaticIR.Context) (live : data.Live ctx.raw)
    (name : ByteArray) (loc : Location) (values : Array IR.Value) (pending : List OwnedPlaceholder)
    : (∀ e ∈ pending, e.2.1.InBounds ctx.raw ∧ MlirParserData.FirstResultLive ctx.raw e.2.1) →
    pending.Pairwise (fun a b => a.2.1.spec ≠ b.2.1.spec) →
    (∀ e ∈ pending, data.CanDeleteOp e.2.1) →
    (∀ v ∈ values, v.InBounds ctx.raw ∧ AvoidValues pending v) →
    Except ParserError (Retired data ctx.raw pending) :=
  match pending with
  | [] => fun _ _ _ _ => pure ⟨ctx, live, ⟨fun _ h _ => h, fun _ h => h, fun _ h => h, fun _ h _ => h⟩⟩
  | entry :: rest => fun hp distinct safe hv => do
    let index := entry.1
    let op := entry.2.1
    let useLoc := entry.2.2
    match htarget : values[index]? with
    | none => throw ((ParserError.mk
        s!"definition of value %{String.fromUTF8! name} provides {values.size} results, but result #{index} was used"
        (some loc) []).addNote useLoc "value used here")
    | some target =>
      have hhead := hp entry (by simp)
      have htargetMem : target ∈ values := by grind
      let old := Sim.ValuePtr.fromOpResultPtr (op.getResultPtr ctx.raw 0 hhead.1)
      let usedType := StaticIR.valueType ctx.raw old (hhead.2.inBounds hhead.1)
      let definedType := StaticIR.valueType ctx.raw target (hv target htargetMem).1
      if usedType ≠ definedType then
        throw ((ParserError.mk
          s!"definition of value %{String.fromUTF8! name}#{index} has type {definedType} but was used with type {usedType}"
          (some loc) []).addNote useLoc "value used here")
      let some changed := StaticParserState.rewirePlaceholder ⟨data, ctx, live⟩ op target
          hhead.1 hhead.2 (hv target htargetMem).1 (safe entry (by simp))
        | throw (ParserError.mk "internal error: failed to rewire and erase a forward-reference placeholder" (some loc) [])
      have frame := changed.property.2
      have liveNext : data.Live changed.val.ctx.raw :=
        (congrArg (fun d => d.Live changed.val.ctx.raw) changed.property.1).mp changed.val.live
      have tailLive : ∀ e ∈ rest, e.2.1.InBounds changed.val.ctx.raw ∧
          MlirParserData.FirstResultLive changed.val.ctx.raw e.2.1 := by
        intro e he
        have hb := hp e (by simp [he])
        have hne := ((List.pairwise_cons.mp distinct).1 e he).symm
        refine ⟨frame.operations e.2.1 hb.1 hne, ?_⟩
        obtain ⟨v, hv, hs⟩ := hb.2
        refine ⟨v, frame.values v hv ?_, hs⟩
        intro res hr
        grind
      have tailValues : ∀ v ∈ values, v.InBounds changed.val.ctx.raw ∧ AvoidValues rest v := by
        intro v he
        have h := hv v he
        exact ⟨frame.values v h.1 (h.2 entry (by simp)), fun e he => h.2 e (by simp [he])⟩
      let tail ← retirePlaceholders data changed.val.ctx liveNext name loc values rest tailLive
        (List.pairwise_cons.mp distinct).2 (fun e he => safe e (by simp [he])) tailValues
      return ⟨tail.ctx, tail.live, ⟨
        fun p hp avoid => tail.frame.operations p
          (frame.operations p hp (avoid entry (by simp))) (fun e he => avoid e (by simp [he])),
        fun p hp => tail.frame.blocks p (frame.blocks p hp),
        fun p hp => tail.frame.regions p (frame.regions p hp),
        fun p hp avoid => tail.frame.values p
          (frame.values p hp (avoid entry (by simp))) (fun e he => avoid e (by simp [he]))⟩⟩
termination_by pending.length

structure RegisteredValues (before : StaticParserState) extends ParserStep before where
  blocks : state.data.blocks = before.data.blocks
  suspended : state.data.blockScopes = before.data.blockScopes

/-- Consume the data record before updating the innermost definition set. Otherwise the
old record retains that set across `insert`, forcing a hash-table copy for every SSA name. -/
@[noinline]
def MlirParserData.recordDefinition (data : MlirParserData) (name : ByteArray) : MlirParserData :=
  let ⟨values, scopes, forward, blocks, saved, allow, aliases, locations⟩ := data
  let scopes := scopes.modify (scopes.size - 1) (·.insert name)
  ⟨values, scopes, forward, blocks, saved, allow, aliases, locations⟩

def StaticParserState.publishValues (s : StaticParserState) (name : ByteArray) (loc : Location)
    (values : Array IR.Value) :
    (∀ v ∈ values, v.InBounds s.ctx.raw ∧ s.data.StableValue v) →
    Except ParserError (RegisteredValues s) :=
  s.consume (α := fun s => (∀ v ∈ values, v.InBounds s.ctx.raw ∧ s.data.StableValue v) →
    Except ParserError (RegisteredValues s)) fun data ctx live hv => do
    if let some (_, existing) := data.values[name]? then
      throw ((ParserError.mk s!"value %{String.fromUTF8! name} has already been defined" (some loc) []).addNote
        existing "previously defined here")
    let published := data.putValues name values loc
    let next := published.recordDefinition name
    have hl := live.putValues name values loc (fun v he => (hv v he).1) (fun v he => (hv v he).2)
    have hn : next.Live ctx.raw := hl.sameReferences rfl rfl rfl rfl
    return ⟨⟨⟨next, ctx, hn⟩, ParserFrame.mono (StaticIR.Preserves.refl ctx.raw) rfl rfl rfl⟩, rfl, rfl⟩

/-- Resolve the owned group, then publish the permanent values. The list traversal uses its
static distinctness proof; it does not look up each pointer or recheck name membership. -/
def StaticParserState.registerValues (s : StaticParserState) (name : ByteArray) (loc : Location)
    (values : Array IR.Value) :
    (∀ v ∈ values, v.InBounds s.ctx.raw ∧ s.data.StableValue v) →
    Except ParserError (RegisteredValues s) :=
  s.consume (α := fun s => (∀ v ∈ values, v.InBounds s.ctx.raw ∧ s.data.StableValue v) →
    Except ParserError (RegisteredValues s)) fun data ctx live hv => do
    match hf : data.forwardValues[name]? with
    | none => StaticParserState.publishValues ⟨data, ctx, live⟩ name loc values hv
    | some fwd =>
      let pending := fwd.placeholders.toList
      have owned : ∀ e ∈ pending, data.ForwardEntry name e.1 e.2.1 e.2.2 := by
        intro e he
        exact ⟨fwd, hf, Std.HashMap.mem_toList_iff_getElem?_eq_some.mp he⟩
      have distinct : pending.Pairwise (fun a b => a.2.1.spec ≠ b.2.1.spec) := by
        apply List.Pairwise.imp_of_mem ?_ (Std.HashMap.distinct_keys_toList (m := fwd.placeholders))
        intro a b ha hb hne he
        have hi := (live.unique name a.1 a.2.1 a.2.2 name b.1 b.2.1 b.2.2 (owned a ha) (owned b hb) he).2
        simp [hi] at hne
      let taken := data.takeForwardName name
      let retired ← retirePlaceholders taken ctx (live.takeForwardName name) name loc values pending
        (fun e he => live.forward name e.1 e.2.1 e.2.2 (owned e he)) distinct
        (fun e he => live.takeForwardName_canDelete (owned e he))
        (fun v he => ⟨(hv v he).1, fun e he => (hv v ‹v ∈ values›).2 name e.1 e.2.1 e.2.2 (owned e he)⟩)
      let after : StaticParserState := ⟨taken, retired.ctx, retired.live⟩
      have frame : ParserFrame ⟨data, ctx, live⟩ after := by
        constructor
        · intro p hp stable
          refine ⟨retired.frame.operations p hp (fun e he => stable name e.1 e.2.1 e.2.2 (owned e he)), ?_⟩
          intro n i op l he
          exact stable n i op l (MlirParserData.forwardEntry_takeForwardName.mp he).2
        · intro p hp stable
          exact ⟨retired.frame.blocks p hp, stable⟩
        · intro p hp stable
          refine ⟨retired.frame.values p hp (fun e he => stable name e.1 e.2.1 e.2.2 (owned e he)), ?_⟩
          intro n i op l he
          exact stable n i op l (MlirParserData.forwardEntry_takeForwardName.mp he).2
        · exact retired.frame.regions
      let published ← after.publishValues name loc values
        (fun v he => frame.values v (hv v he).1 (hv v he).2)
      return ⟨⟨published.state, frame.trans published.frame⟩, published.blocks, published.suspended⟩

end Veir.Parser
