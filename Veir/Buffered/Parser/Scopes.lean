module

public import Veir.Buffered.Parser.Bindings

@[expose] public section
namespace Veir.Buffered.Parser

structure EnteredScope (before : StaticParserState) extends ParserStep before where
  stored : state.data.blockScopes = before.data.blockScopes.push before.data.blocks

def StaticParserState.enterScope (s : StaticParserState) : EnteredScope s :=
  s.consume (α := EnteredScope) fun data ctx live =>
    let blocks := data.enterBlockScope
    let defs := blocks.definitionsPerScope.push (.emptyWithCapacity 128)
    let nextData : MlirParserData := { blocks with definitionsPerScope := defs }
    have hl : nextData.Live ctx.raw := live.enterBlockScope.sameReferences rfl rfl rfl rfl
    let next : StaticParserState := ⟨nextData, ctx, hl⟩
    have frame : ParserFrame ⟨data, ctx, live⟩ next := by
      constructor
      · intro p hp stable; exact ⟨hp, stable⟩
      · intro p hp stable
        refine ⟨hp, ?_⟩
        intro scope name block loc he
        obtain ⟨oldScope, he⟩ := MlirParserData.blockEntry_enter_origin he
        exact stable oldScope name block loc he
      · intro p hp stable; exact ⟨hp, stable⟩
      · exact fun _ hp => hp
    ⟨⟨next, frame⟩, rfl⟩

structure ForgottenNames (before : MlirParserData) (ctx : IR.RawContext) where
  data : MlirParserData
  live : data.Live ctx
  forward : data.forwardValues = before.forwardValues
  blocks : data.blocks = before.blocks
  scopes : data.blockScopes = before.blockScopes

def forgetNames (data : MlirParserData) (ctx : IR.RawContext) (live : data.Live ctx)
    (names : List ByteArray) : ForgottenNames data ctx :=
  match names with
  | [] => ⟨data, live, rfl, rfl, rfl⟩
  | name :: rest =>
    let next := forgetNames (data.forgetValueName name) ctx (live.forgetValueName name) rest
    ⟨next.data, next.live, next.forward, next.blocks, next.scopes⟩

structure RestoredScope (before : StaticParserState) (outer : BlockTable) (saved : Array BlockTable)
    extends ParserStep before where
  blocks : state.data.blocks = outer
  scopes : state.data.blockScopes = saved

/-- The successful recursive parser provides the saved-scope equality. Restoring visibility
and dropping inner SSA bindings are ordinary lexical operations, not pointer validation. -/
def StaticParserState.restoreScope (s : StaticParserState) (outer : BlockTable) (saved : Array BlockTable) :
    s.data.blockScopes = saved.push outer → RestoredScope s outer saved :=
  s.consume (α := fun s => s.data.blockScopes = saved.push outer → RestoredScope s outer saved)
    fun data ctx live hs =>
      let restored : MlirParserData := { data with blocks := outer, blockScopes := saved }
      have hl : restored.Live ctx.raw := live.restoreBlockScope hs
      let forgotten := forgetNames restored ctx.raw hl data.definitionsPerScope.back!.toList
      let nextData : MlirParserData := { forgotten.data with definitionsPerScope := data.definitionsPerScope.pop }
      have hn : nextData.Live ctx.raw := forgotten.live.sameReferences rfl rfl rfl rfl
      let next : StaticParserState := ⟨nextData, ctx, hn⟩
      have frame : ParserFrame ⟨data, ctx, live⟩ next := by
        have ho : ∀ n i op l, nextData.ForwardEntry n i op l ↔ data.ForwardEntry n i op l := by
          intros
          simp only [MlirParserData.ForwardEntry, nextData, forgotten.forward, restored]
        constructor
        · intro p hp stable
          exact ⟨hp, fun n i op l he => stable n i op l ((ho ..).mp he)⟩
        · intro p hp stable
          refine ⟨hp, ?_⟩
          intro scope n block loc he
          have he' : restored.blockEntry? scope n = some (.ForwardDeclared block loc) := by
            cases scope <;> simpa only [MlirParserData.blockEntry?, next, nextData, forgotten.blocks, forgotten.scopes] using he
          obtain ⟨oldScope, he'⟩ := MlirParserData.blockEntry_restore_origin hs he'
          exact stable oldScope n block loc he'
        · intro p hp stable
          exact ⟨hp, fun n i op l he => stable n i op l ((ho ..).mp he)⟩
        · exact fun _ hp => hp
      ⟨⟨next, frame⟩, forgotten.blocks, forgotten.scopes⟩

end Veir.Buffered.Parser
