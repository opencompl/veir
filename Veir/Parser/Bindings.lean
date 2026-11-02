module

public import Veir.Parser.Operations

@[expose] public section
namespace Veir.Parser

abbrev ResultGroup := ByteArray × Nat × Location
abbrev BlockArgumentName := ByteArray × TypeAttr × Location

def groupCount (groups : List ResultGroup) : Nat :=
  match groups with
  | [] => 0
  | g :: rest => g.2.1 + groupCount rest

/-- Read each group's result pointers from the *current* context. Keeping an allocation-time
buffer snapshot across placeholder reclamation would cause copy-on-write. Only its erased
slot witnesses are transported. -/
def registerResultGroups {before : StaticParserState} {count : Nat}
    (built : ConstructedOperation before count) (offset : Nat) (groups : List ResultGroup) :
    offset + groupCount groups = count → Except ParserError (ConstructedOperation before count) :=
  match groups with
  | [] => fun _ => pure built
  | g :: rest => fun hcount => do
    let ⟨⟨⟨state, frame⟩, op, hop, stable⟩, slots, hblocks, hscopes⟩ := built
    have hi : ∀ i : Fin g.2.1, offset + i.val < count := by
      intro i
      simp only [groupCount] at hcount
      have := i.isLt
      omega
    let getValue := fun i : Fin g.2.1 => ResultLive.value state.ctx.raw op (offset + i.val).toUInt64 hop
      (slots ⟨offset + i.val, hi i⟩)
    let values := Array.ofFn (fun i => (getValue i).val)
    have hv : ∀ v ∈ values, v.InBounds state.ctx.raw ∧ state.data.StableValue v := by
      intro v he
      obtain ⟨i, rfl⟩ := Array.mem_ofFn.mp he
      exact ⟨(getValue i).property.1, result_stable stable (getValue i).property.2⟩
    let published ← state.registerValues g.1 g.2.2 values hv
    have hop' := published.frame.operations op hop stable
    have slots' : ∀ i : Fin count, ResultLive published.state.ctx.raw op i.val.toUInt64 := by
      intro i
      obtain ⟨v, hv, hs⟩ := slots i
      exact ⟨v, (published.frame.values v hv (result_stable stable hs)).1, hs⟩
    let next : ConstructedOperation before count :=
      ⟨⟨⟨published.state, frame.trans published.frame⟩, op, hop'.1, hop'.2⟩,
        slots', published.blocks.trans hblocks, published.suspended.trans hscopes⟩
    registerResultGroups next (offset + g.2.1) rest (by simp only [groupCount] at hcount; omega)
termination_by groups.length

def registerBlockArguments {before : StaticParserState} {count : Nat}
    (built : DefinedBlock before count) (offset : Nat) (args : List BlockArgumentName) :
    offset + args.length = count → Except ParserError (DefinedBlock before count) :=
  match args with
  | [] => fun _ => pure built
  | arg :: rest => fun hcount => do
    let ⟨⟨⟨state, frame⟩, block, hb, stable⟩, slots, hscopes⟩ := built
    have hi : offset < count := by simp only [List.length_cons] at hcount; omega
    let value := ArgumentLive.value state.ctx.raw block offset.toUInt64 hb (slots ⟨offset, hi⟩)
    let published ← state.registerValues arg.1 arg.2.2 #[value.val] (by
      intro v he
      have hv : v = value.val := by simpa using he
      subst v
      exact ⟨value.property.1, argument_stable value.property.2⟩)
    have hb' := published.frame.blocks block hb stable
    have slots' : ∀ i : Fin count, ArgumentLive published.state.ctx.raw block i.val.toUInt64 := by
      intro i
      obtain ⟨v, hv, hs⟩ := slots i
      exact ⟨v, (published.frame.values v hv (argument_stable hs)).1, hs⟩
    let next : DefinedBlock before count :=
      ⟨⟨⟨published.state, frame.trans published.frame⟩, block, hb'.1, hb'.2⟩,
        slots', published.suspended.trans hscopes⟩
    registerBlockArguments next (offset + 1) rest (by simp only [List.length_cons] at hcount; omega)
termination_by args.length

end Veir.Parser
