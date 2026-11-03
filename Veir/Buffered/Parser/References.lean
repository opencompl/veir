module

public import Veir.Buffered.Parser.Transitions
public import Veir.Buffered.Parser.ParserError

@[expose] public section
namespace Veir.Buffered.Parser
namespace MlirParserData

def putPlaceholder (d : MlirParserData) (name : ByteArray) (index : Nat)
    (op : IR.Op) (loc : Location) : MlirParserData :=
  let previous := d.forwardValues[name]?.getD { placeholders := {}, loc }
  let replacement := { previous with placeholders := previous.placeholders.insert index (op, loc) }
  { d with forwardValues := d.forwardValues.insert name replacement }

@[simp]
theorem forwardEntry_putPlaceholder {d : MlirParserData} {name index op loc n i p l} :
    (d.putPlaceholder name index op loc).ForwardEntry n i p l ↔
      (n = name ∧ i = index ∧ p = op ∧ l = loc) ∨
      ((n ≠ name ∨ i ≠ index) ∧ d.ForwardEntry n i p l) := by
  by_cases hn : name = n <;> by_cases hi : index = i <;>
    cases hf : d.forwardValues[name]? <;>
    simp_all [putPlaceholder, ForwardEntry, Std.HashMap.getElem?_insert] <;> grind only

/-- Publishing a fresh placeholder cannot alias an existing owner or published SSA value. -/
theorem Live.putPlaceholder {d : MlirParserData} {before after : IR.RawContext}
    (h : d.Live before) (frame : StaticIR.Preserves before after)
    (name : ByteArray) (index : Nat) (op : IR.Op) (loc : Location)
    (hop : op.InBounds after) (slot : FirstResultLive after op)
    (fresh : ¬ op.spec.InBounds before.spec) : (d.putPlaceholder name index op loc).Live after := by
  have hmono := h.mono frame
  constructor
  · exact hmono.values
  · exact hmono.blocks
  · intro n i p l he
    rcases forwardEntry_putPlaceholder.mp he with ⟨rfl, rfl, rfl, rfl⟩ | ⟨_, he⟩
    · exact ⟨hop, slot⟩
    · exact hmono.forward n i p l he
  · intro n i p l n' i' p' l' he he' hs
    rw [forwardEntry_putPlaceholder (d := d)] at he he'
    rcases he with ⟨rfl, rfl, rfl, rfl⟩ | ⟨_, he⟩
    · rcases he' with ⟨rfl, rfl, rfl, rfl⟩ | ⟨_, he'⟩
      · exact ⟨rfl, rfl⟩
      · exact False.elim (fresh (hs ▸ (h.forward n' i' p' l' he').1.ib))
    · rcases he' with ⟨rfl, rfl, rfl, rfl⟩ | ⟨_, he'⟩
      · exact False.elim (fresh (hs ▸ (h.forward n i p l he).1.ib))
      · exact h.unique n i p l n' i' p' l' he he' hs
  · intro v hv n i p l he res hr hs
    rcases forwardEntry_putPlaceholder.mp he with ⟨rfl, rfl, rfl, rfl⟩ | ⟨_, he⟩
    · have hvib := (h.values v hv).ib
      apply fresh
      grind [ValuePtr.InBounds, OpResultPtr.inBounds_def]
    · exact h.privateValues v hv n i p l he res hr hs
  · exact hmono.uniqueBlocks

/-- Fresh placeholders cannot turn a caller's permanent handles into temporary ones. -/
theorem putPlaceholder_frame {s : StaticParserState} {ctx : StaticIR.Context}
    (frame : StaticIR.Preserves s.ctx.raw ctx.raw) {name index op loc}
    (fresh : ¬ op.spec.InBounds s.ctx.raw.spec)
    (live : (s.data.putPlaceholder name index op loc).Live ctx.raw) :
    ParserFrame s ⟨s.data.putPlaceholder name index op loc, ctx, live⟩ := by
  constructor
  · intro p hp stable
    refine ⟨frame.operation hp, ?_⟩
    intro n i q l he hs
    rcases (forwardEntry_putPlaceholder (d := s.data)).mp he with ⟨rfl, rfl, rfl, rfl⟩ | ⟨_, he⟩
    · exact fresh (hs ▸ hp.ib)
    · exact stable n i q l he hs
  · intro p hp stable
    exact ⟨frame.block hp, stable⟩
  · intro p hp stable
    refine ⟨frame.value hp, ?_⟩
    intro n i q l he res hr hs
    rcases (forwardEntry_putPlaceholder (d := s.data)).mp he with ⟨rfl, rfl, rfl, rfl⟩ | ⟨_, he⟩
    · have hpib := hp.ib
      apply fresh
      grind [ValuePtr.InBounds, OpResultPtr.inBounds_def]
    · exact stable n i q l he res hr hs
  · exact fun _ hp => frame.region hp

end MlirParserData

def BorrowedValue.pure (s : StaticParserState) (p : IR.Value) (hp : p.InBounds s.ctx.raw) :
    BorrowedValue s :=
  ⟨⟨s, ParserFrame.refl s⟩, p, hp, StaticIR.Preserves.refl s.ctx.raw, rfl, rfl⟩

/-- Allocate and publish a placeholder using only erased allocation and ownership proofs. -/
def StaticParserState.addPlaceholder (s : StaticParserState) (name : ByteArray) (index : Nat)
    (ty : TypeAttr) (loc : Location) : Except ParserError (BorrowedValue s) :=
  s.consume (α := fun s => Except ParserError (BorrowedValue s)) fun data ctx live => do
    let some allocated := StaticIR.createOp ctx (.builtin .unrealized_conversion_cast)
        #[ty] #[] #[] #[] () none (by simp) (by simp) (by simp) (by simp) (by simp)
      | throw (ParserError.mk "internal error: failed to create forward-reference placeholder" (some loc) [])
    let value := allocated.result ⟨0, by simp⟩
    have slot : MlirParserData.FirstResultLive allocated.ctx.raw allocated.pointer :=
      ⟨value.val, value.property.1, value.property.2⟩
    have nextLive := live.putPlaceholder allocated.preserves name index allocated.pointer loc
      allocated.inBounds slot allocated.fresh
    let next : StaticParserState :=
      ⟨data.putPlaceholder name index allocated.pointer loc, allocated.ctx, nextLive⟩
    return ⟨⟨next, MlirParserData.putPlaceholder_frame allocated.preserves allocated.fresh nextLive⟩,
      value.val, value.property.1, allocated.preserves, rfl, rfl⟩

/-- SSA name resolution: source-language index/type checks remain, but pointer liveness is
obtained from the table invariant rather than an address registry. -/
def StaticParserState.useValue (s : StaticParserState) (name : ByteArray) (index : Option Nat)
    (expected : TypeAttr) (loc : Location) : Except ParserError (BorrowedValue s) :=
  s.consume (α := fun s => Except ParserError (BorrowedValue s)) fun data ctx live => do
    let display := match index with
      | none => s!"%{String.fromUTF8! name}"
      | some i => s!"%{String.fromUTF8! name}#{i}"
    let i := index.getD 0
    match hn : data.values[name]? with
    | some (values, defLoc) =>
      match hv : values[i]? with
      | none => throw ((ParserError.mk s!"invalid result index {i} for %{String.fromUTF8! name}"
          (some loc) []).addNote defLoc "value defined here")
      | some value =>
        have hdefined : data.DefinedValue value := ⟨name, values, defLoc, hn, by grind⟩
        have hp := live.values value hdefined
        let parsedType := StaticIR.valueType ctx.raw value hp
        if parsedType ≠ expected.val then
          throw ((ParserError.mk s!"type mismatch for value {display}: expected {expected}, got {parsedType}"
            (some loc) []).addNote defLoc "value defined here")
        return BorrowedValue.pure ⟨data, ctx, live⟩ value hp
    | none =>
      match hf : data.forwardValues[name]? with
      | none => StaticParserState.addPlaceholder ⟨data, ctx, live⟩ name i expected loc
      | some fwd =>
        match hi : fwd.placeholders[i]? with
        | none => StaticParserState.addPlaceholder ⟨data, ctx, live⟩ name i expected loc
        | some (op, firstLoc) =>
          have he : data.ForwardEntry name i op firstLoc := ⟨fwd, hf, hi⟩
          have hop := (live.forward name i op firstLoc he).1
          have slot := (live.forward name i op firstLoc he).2
          let value := Sim.ValuePtr.fromOpResultPtr (op.getResultPtr ctx.raw 0 hop)
          have hp : value.InBounds ctx.raw := slot.inBounds hop
          let parsedType := StaticIR.valueType ctx.raw value hp
          if parsedType ≠ expected.val then
            throw ((ParserError.mk s!"type mismatch for value {display}: expected {expected}, got {parsedType}"
              (some loc) []).addNote firstLoc "value first used here")
          return BorrowedValue.pure ⟨data, ctx, live⟩ value hp

end Veir.Buffered.Parser
