module

public import Veir.Buffered.Parser.Operands

public section
namespace Veir.Buffered.Parser.Construction
open Veir.Buffered.Parser.Lexer Veir.Buffered.Parser.ParserError
open Syntax

abbrev M := SyntaxM

instance {α : Type} : Nonempty (M α) := ⟨fun _ parser => .error default parser⟩

def liftIR (action : Except ParserError α) : M α :=
  match action with
  | .ok a => pure a
  | .error e => throw e

def ParentValid (s : StaticParserState) (parent : Option IR.Block) : Prop :=
  ∀ p ∈ parent, p.InBounds s.ctx.raw ∧ s.data.StableBlock p

theorem ParentValid.transport {a b : StaticParserState} {parent : Option IR.Block}
    (h : ParentValid a parent) (frame : ParserFrame a b) : ParentValid b parent :=
  fun p hp => frame.blocks p (h p hp).1 (h p hp).2

structure OptionalOperation (before : StaticParserState) extends ParserStep before where
  pointer : Option IR.Op
  live : ∀ p ∈ pointer, p.InBounds state.ctx.raw ∧ state.data.StableOp p
  suspended : state.data.blockScopes = before.data.blockScopes

structure OptionalBlock (before : StaticParserState) extends ParserStep before where
  pointer : Option IR.Block
  live : ∀ p ∈ pointer, p.InBounds state.ctx.raw ∧ state.data.StableBlock p
  suspended : state.data.blockScopes = before.data.blockScopes

structure Body (before : StaticParserState) extends ParserStep before where
  suspended : state.data.blockScopes = before.data.blockScopes

structure Regions (before : StaticParserState) extends ParserStep before where
  regions : Array IR.Region
  live : ∀ p ∈ regions, p.InBounds state.ctx.raw
  blocks : state.data.blocks = before.data.blocks
  suspended : state.data.blockScopes = before.data.blockScopes

def optionalBlockLabel (s : StaticParserState) (region : IR.Region) (hr : region.InBounds s.ctx.raw) :
    M (OptionalBlock s) := do
  let some token ← parseOptionalToken .caretIdent
    | return ⟨⟨s, ParserFrame.refl s⟩, none, by simp, rfl⟩
  let name := { token.slice with start := token.slice.start + 1 }.of (← Syntax.getInput)
  let args ← (·.getD #[]) <$> parseOptionalDelimitedList .paren Syntax.parseTypedValue
  parsePunctuation ":" "':' expected after block label"
  let block ← liftIR (s.defineBlock name (args.map (·.2.1)) region token.slice.start hr)
  let ready ← liftIR (registerBlockArguments block 0 args.toList (by simp))
  return ⟨⟨ready.state, ready.frame⟩, some ready.pointer, by
    intro p hp
    have he : ready.pointer = p := by simpa using hp
    subst p
    exact ⟨ready.inBounds, ready.stable⟩, ready.suspended⟩

mutual

partial def optionalOp (s : StaticParserState) (parent : Option IR.Block) (hparent : ParentValid s parent) :
    M (OptionalOperation s) := do
  let opStart ← getPos
  let groups ← Syntax.parseOpResults
  let nameStart ← getPos
  let some name ← parseOptionalStringLiteral
    | return ⟨⟨s, ParserFrame.refl s⟩, none, by simp, rfl⟩
  let some nameString := String.fromUTF8? name
    | throwAt nameStart s!"op '{escapeStringLiteral (String.fromUTF8! name)}' not a valid UTF8 string."
  let operands ← Syntax.parseOperands
  let successorNames ← Syntax.parseBlockNames
  let ⟨⟨s₁, f₁⟩, successors, mentions, _, _, scopes₁⟩ ←
    liftIR (resolveSuccessorList s successorNames.toList #[] (by simp))
  let code := OpCode.fromName name
  if code = .builtin .unregistered && !(← get).allowUnregisteredDialect then
    throwAt nameStart s!"op '{nameString}' is not registered. Consider using --allow-unregistered-dialect."
  let properties ← Syntax.parseOpProperties code
  let properties := Syntax.optionallySetUnregisteredOpName code properties name
  let ⟨⟨s₂, f₂⟩, regions, hregions, blocks₂, scopes₂⟩ ← opRegions s₁
  let attrs ← Syntax.parseOpAttributes
  let (inputTypes, outputTypes) ← Syntax.parseOperationType
  let count := groupCount groups.toList
  if hcount : outputTypes.size ≠ count then
    throwAt nameStart s!"operation '{nameString}' declares {outputTypes.size} result types, but {count} result values were provided"
  else
    if inputTypes.size ≠ operands.size then
      throwAt nameStart s!"operation '{nameString}' declares {inputTypes.size} operand types, but {operands.size} operands were provided"
    let ⟨⟨s₃, f₃⟩, values, hvalues, mono₃, blocks₃, scopes₃⟩ ←
      liftIR (resolveOperandList s₂ (operands.zip inputTypes).toList #[] (by simp))
    have hsucc : ∀ p ∈ successors, p.InBounds s₃.ctx.raw := by
      intro p hp
      obtain ⟨n, e, he, hptr⟩ := mentions p hp
      have he₂ : s₂.data.blockEntry? 0 n = some e := by
        change s₂.data.blocks[n]? = some e
        rw [blocks₂]
        exact he
      rw [← hptr]
      exact mono₃.block (s₂.live.blocks 0 n e he₂)
    have hpar := hparent.transport (f₁.trans (f₂.trans f₃))
    let built ← liftIR (s₃.constructOp code outputTypes values successors regions properties attrs parent opStart
      hvalues hsucc (fun p hp => mono₃.region (hregions p hp)) (fun p hp => (hpar p hp).1))
    let ready ← liftIR (registerResultGroups built 0 groups.toList (by dsimp [count] at hcount; omega))
    return ⟨⟨ready.state, f₁.trans (f₂.trans (f₃.trans ready.frame))⟩, some ready.pointer, by
      intro p hp
      have he : ready.pointer = p := by simpa using hp
      subst p
      exact ⟨ready.inBounds, ready.stable⟩,
      ready.suspended.trans (scopes₃.trans (scopes₂.trans scopes₁))⟩

partial def blockBody (s : StaticParserState) (block : IR.Block)
    (hb : block.InBounds s.ctx.raw) (stable : s.data.StableBlock block) : M (Body s) := do
  let ⟨⟨next, frame⟩, op, _, scopes⟩ ← optionalOp s (some block) (by
    intro p hp
    have he : block = p := by simpa using hp
    subst p
    exact ⟨hb, stable⟩)
  match op with
  | none => return ⟨⟨next, frame⟩, scopes⟩
  | some _ =>
    have hb' := frame.blocks block hb stable
    let tail ← blockBody next block hb'.1 hb'.2
    return ⟨⟨tail.state, frame.trans tail.frame⟩, tail.suspended.trans scopes⟩

partial def moreBlocks (s : StaticParserState) (region : IR.Region) (hr : region.InBounds s.ctx.raw) :
    M (Body s) := do
  let ⟨⟨next, frame⟩, block, live, scopes⟩ ← optionalBlockLabel s region hr
  match hblock : block with
  | none => return ⟨⟨next, frame⟩, scopes⟩
  | some p =>
    have hp := live p (by simp [hblock])
    let ⟨⟨after, bodyFrame⟩, bodyScopes⟩ ← blockBody next p hp.1 hp.2
    let tail ← moreBlocks after region ((frame.trans bodyFrame).regions region hr)
    return ⟨⟨tail.state, frame.trans (bodyFrame.trans tail.frame)⟩,
      tail.suspended.trans (bodyScopes.trans scopes)⟩

partial def entryBlock (s : StaticParserState) (region : IR.Region) (hr : region.InBounds s.ctx.raw) :
    M (Body s) := do
  let ⟨⟨next, frame⟩, block, live, scopes⟩ ← optionalBlockLabel s region hr
  match hblock : block with
  | some p =>
    have hp := live p (by simp [hblock])
    let body ← blockBody next p hp.1 hp.2
    return ⟨⟨body.state, frame.trans body.frame⟩, body.suspended.trans scopes⟩
  | none =>
    let built ← liftIR (next.defineBlock ByteArray.empty #[] region (← getPos) (frame.regions region hr))
    let body ← blockBody built.state built.pointer built.inBounds built.stable
    return ⟨⟨body.state, frame.trans (built.frame.trans body.frame)⟩,
      body.suspended.trans (built.suspended.trans scopes)⟩

partial def parseRegion (s : StaticParserState) : M (ParsedRegion s) :=
  s.consume (α := fun s => M (ParsedRegion s)) fun data ctx live => do
    let ⟨⟨entered, enterFrame⟩, stored⟩ := StaticParserState.enterScope ⟨data, ctx, live⟩
    parsePunctuation "{"
    let some allocation := StaticIR.createRegion entered.ctx
      | throwAtCurrentPos "internal error: failed to create region"
    let region := allocation.pointer
    let created : StaticParserState := ⟨entered.data, allocation.ctx, entered.live.mono allocation.preserves⟩
    have allocFrame : ParserFrame entered created := ParserFrame.mono allocation.preserves rfl rfl rfl
    let body : Body created ←
      if ← parseOptionalPunctuation "}" then
        pure ⟨⟨created, ParserFrame.refl created⟩, rfl⟩
      else do
        let ⟨⟨afterEntry, firstFrame⟩, firstScopes⟩ ← entryBlock created region allocation.inBounds
        let ⟨⟨after, moreFrame⟩, moreScopes⟩ ← moreBlocks afterEntry region (firstFrame.regions region allocation.inBounds)
        parsePunctuation "}"
        for (name, entry) in after.data.blocks do
          if let .ForwardDeclared _ loc := entry then
            throwAt loc s!"block %{String.fromUTF8! name} was used but never defined"
        pure ⟨⟨after, firstFrame.trans moreFrame⟩, moreScopes.trans firstScopes⟩
    -- Read the saved maps from the returned scope stack, not from the pre-recursion data
    -- record: retaining that record would also retain growing SSA/location hash tables.
    let outer := body.state.data.blockScopes.back!
    let saved := body.state.data.blockScopes.pop
    have hstored := body.suspended.trans stored
    have houter : outer = data.blocks := by simp [outer, hstored]
    have hsaved : saved = data.blockScopes := by simp [saved, hstored]
    let restored := body.state.restoreScope outer saved (by simpa [houter, hsaved] using hstored)
    return ⟨⟨restored.state, enterFrame.trans (allocFrame.trans (body.frame.trans restored.frame))⟩,
      region, restored.frame.regions region (body.frame.regions region allocation.inBounds),
      restored.blocks.trans houter, restored.scopes.trans hsaved⟩

partial def regionList (s : StaticParserState) (acc : Array IR.Region)
    (hacc : ∀ p ∈ acc, p.InBounds s.ctx.raw) : M (Regions s) := do
  let ⟨⟨next, frame⟩, region, hr, blocks, scopes⟩ ← parseRegion s
  let regions := acc.push region
  have hregions : ∀ p ∈ regions, p.InBounds next.ctx.raw := by
    intro p hp
    rcases Array.mem_push.mp hp with hp | rfl
    · exact frame.regions p (hacc p hp)
    · exact hr
  if ← parseOptionalPunctuation "," then
    let tail ← regionList next regions hregions
    return ⟨⟨tail.state, frame.trans tail.frame⟩, tail.regions, tail.live,
      tail.blocks.trans blocks, tail.suspended.trans scopes⟩
  else
    return ⟨⟨next, frame⟩, regions, hregions, blocks, scopes⟩

partial def opRegions (s : StaticParserState) : M (Regions s) := do
  if !(← parseOptionalPunctuation "(") then
    return ⟨⟨s, ParserFrame.refl s⟩, #[], by simp, rfl, rfl⟩
  if ← parseOptionalPunctuation ")" then
    return ⟨⟨s, ParserFrame.refl s⟩, #[], by simp, rfl, rfl⟩
  let result ← regionList s #[] (by simp)
  parsePunctuation ")" "closing delimiter ')' expected"
  return result

end

def topLevel (s : StaticParserState) : M (ParsedOperation s) := do
  Syntax.parseTypeAliasDefs
  let ⟨⟨next, frame⟩, op, live, _⟩ ← optionalOp s none (by simp [ParentValid])
  match hop : op with
  | none => throwAtCurrentPos "operation expected"
  | some pointer =>
    for (name, fwd) in next.data.forwardValues do
      throwAt fwd.loc s!"use of undefined value %{String.fromUTF8! name}"
    have hp := live pointer (by simp [hop])
    return ⟨⟨next, frame⟩, pointer, hp.1, hp.2⟩

end Veir.Buffered.Parser.Construction
