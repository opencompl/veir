module

public import Veir.Parser.Liveness

/-!
Frames for recursive parser actions. Unlike allocation-only frames, these allow privately
owned placeholders to be reclaimed. A caller may retain a permanent handle, but not borrow
a placeholder across an action which can resolve its name. The distinction is erased.
-/
@[expose] public section
namespace Veir.Parser
namespace MlirParserData

def StableOp (d : MlirParserData) (p : IR.Op) : Prop :=
  ∀ n i op loc, d.ForwardEntry n i op loc → p.spec ≠ op.spec

def StableBlock (d : MlirParserData) (p : IR.Block) : Prop :=
  ∀ scope n block loc, d.blockEntry? scope n = some (.ForwardDeclared block loc) →
    p.spec ≠ block.spec

def StableValue (d : MlirParserData) (p : IR.Value) : Prop :=
  ∀ n i op loc, d.ForwardEntry n i op loc →
    ∀ res, p.spec = .opResult res → res.op ≠ op.spec

theorem Live.definedValue_stable {d : MlirParserData} {ctx : IR.RawContext}
    (h : d.Live ctx) {v : IR.Value} (hv : d.DefinedValue v) : d.StableValue v :=
  h.privateValues v hv

theorem Live.definedBlock_stable {d : MlirParserData} {ctx : IR.RawContext}
    (h : d.Live ctx) {scope name block loc}
    (he : d.blockEntry? scope name = some (.Defined block loc)) : d.StableBlock block := by
  intro s n p l hp hs
  obtain ⟨hscope, hname⟩ := h.uniqueBlocks s n p l hp scope name (.Defined block loc) he hs.symm
  subst s
  subst n
  rw [he] at hp
  cases hp

end MlirParserData

/-- Consume the runtime state before a dependent transaction. The index is erased; the
continuation receives the data and context separately, preventing buffer retention. -/
@[noinline, nospecialize]
def StaticParserState.consume {α : StaticParserState → Type} (s : StaticParserState)
    (f : (data : MlirParserData) → (ctx : StaticIR.Context) → (live : data.Live ctx.raw) →
      α ⟨data, ctx, live⟩) : α s :=
  f s.data s.ctx s.live

/-- Liveness of caller-local handles through a parser action, including ownership status
needed to retain them through another action. These fields never execute. -/
structure ParserFrame (before after : StaticParserState) : Prop where
  operations : ∀ p : IR.Op, p.InBounds before.ctx.raw → before.data.StableOp p →
    p.InBounds after.ctx.raw ∧ after.data.StableOp p
  blocks : ∀ p : IR.Block, p.InBounds before.ctx.raw → before.data.StableBlock p →
    p.InBounds after.ctx.raw ∧ after.data.StableBlock p
  values : ∀ p : IR.Value, p.InBounds before.ctx.raw → before.data.StableValue p →
    p.InBounds after.ctx.raw ∧ after.data.StableValue p
  regions : ∀ p : IR.Region, p.InBounds before.ctx.raw → p.InBounds after.ctx.raw

theorem ParserFrame.refl (s : StaticParserState) : ParserFrame s s :=
  ⟨fun _ h hs => ⟨h, hs⟩, fun _ h hs => ⟨h, hs⟩, fun _ h hs => ⟨h, hs⟩, fun _ h => h⟩

theorem ParserFrame.trans {a b c : StaticParserState} (ab : ParserFrame a b) (bc : ParserFrame b c) :
    ParserFrame a c where
  operations p hp hs := let ⟨hp, hs⟩ := ab.operations p hp hs; bc.operations p hp hs
  blocks p hp hs := let ⟨hp, hs⟩ := ab.blocks p hp hs; bc.blocks p hp hs
  values p hp hs := let ⟨hp, hs⟩ := ab.values p hp hs; bc.values p hp hs
  regions p hp := bc.regions p (ab.regions p hp)

/-- Allocation and in-place mutation, without altering reference ownership. -/
theorem ParserFrame.mono {a b : StaticParserState} (frame : StaticIR.Preserves a.ctx.raw b.ctx.raw)
    (hf : b.data.forwardValues = a.data.forwardValues)
    (hb : b.data.blocks = a.data.blocks) (hs : b.data.blockScopes = a.data.blockScopes) :
    ParserFrame a b := by
  have ho : ∀ n i op l, b.data.ForwardEntry n i op l ↔ a.data.ForwardEntry n i op l := by
    intros; simp only [MlirParserData.ForwardEntry, hf]
  have hblock : ∀ scope name, b.data.blockEntry? scope name = a.data.blockEntry? scope name := by
    intro scope name
    cases scope <;> simp only [MlirParserData.blockEntry?, hb, hs]
  constructor
  · intro p hp stable
    exact ⟨frame.operation hp, fun n i op l he => stable n i op l ((ho ..).mp he)⟩
  · intro p hp stable
    refine ⟨frame.block hp, ?_⟩
    intro scope n block l he
    rw [hblock] at he
    exact stable scope n block l he
  · intro p hp stable
    exact ⟨frame.value hp, fun n i op l he => stable n i op l ((ho ..).mp he)⟩
  · exact fun _ hp => frame.region hp

/-- The unchanged parser metadata is retained independently of the buffer. -/
def StaticParserState.withMutation (data : MlirParserData) (ctx : StaticIR.Context)
    (live : data.Live ctx.raw) (mutation : StaticIR.Mutation ctx.raw) : StaticParserState :=
  ⟨data, mutation.ctx, live.mono mutation.preserves⟩

structure ParserStep (before : StaticParserState) where
  state : StaticParserState
  frame : ParserFrame before state

structure ParsedOperation (before : StaticParserState) extends ParserStep before where
  pointer : IR.Op
  inBounds : pointer.InBounds state.ctx.raw
  stable : state.data.StableOp pointer

structure ParsedBlock (before : StaticParserState) extends ParserStep before where
  pointer : IR.Block
  inBounds : pointer.InBounds state.ctx.raw
  stable : state.data.StableBlock pointer

structure ParsedRegion (before : StaticParserState) extends ParserStep before where
  pointer : IR.Region
  inBounds : pointer.InBounds state.ctx.raw
  blocks : state.data.blocks = before.data.blocks
  suspended : state.data.blockScopes = before.data.blockScopes

/-- A lookup/allocation-only action can also return a borrowed placeholder. Such a result
may be consumed by construction, but cannot be kept across an arbitrary parser action. -/
structure BorrowedValue (before : StaticParserState) extends ParserStep before where
  pointer : IR.Value
  inBounds : pointer.InBounds state.ctx.raw
  preserves : StaticIR.Preserves before.ctx.raw state.ctx.raw
  blocks : state.data.blocks = before.data.blocks
  suspended : state.data.blockScopes = before.data.blockScopes

end Veir.Parser
