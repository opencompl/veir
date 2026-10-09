module


public import Veir.Parser.AttrParser
public import Veir.Parser.DecidableInBounds
import Veir.Rewriter.WellFormed
import all Veir.IR.Basic
public import Veir.Parser.StructuralBounds
public import Veir.Parser.ValueBounds
public import Veir.Parser.ResultGroups
public import Veir.Rewriter.WfRewriter

public section

open Veir.Parser.Lexer
open Veir.Parser
open Veir.AttrParser

namespace Veir.Parser

open Veir.Parser.ParserError

variable {OpInfo : Type} [HasOpInfo OpInfo] [HasDialect OpInfo Builtin]

/--
  The state of a block encountered during parsing.
  A block is either `Defined` (its label has been parsed) or `ForwardDeclared`
  (it has only been referenced, e.g., as a block operand, but not yet defined).
-/
inductive BlockEntry where
  | Defined (block : BlockPtr) (loc : Location)
  | ForwardDeclared (block : BlockPtr) (loc : Location)
  deriving Inhabited

/-- Get the block pointer of a `BlockEntry`, regardless of its state. -/
def BlockEntry.block : BlockEntry → BlockPtr
  | .Defined block _ => block
  | .ForwardDeclared block _ => block

/--
  Bookkeeping for an SSA value referenced before it is defined (a "forward reference").

  Following MLIR's generic-form parser, the name table is flat across all regions: a forward
  reference is resolved by the first textual definition of the name, wherever it appears. Each
  referenced result index holds a detached single-result placeholder operation standing in for
  the value; when the definition is parsed, all uses of each placeholder are replaced by the
  real value (via `Rewriter.replaceValue`) and the placeholder is erased.

  Whether such a reference is actually legal (dominance, `IsolatedFromAbove`) is a verifier
  concern that MLIR checks after parsing; we likewise leave it to a later verification pass and
  only report values that are never defined anywhere.

  This mirrors MLIR's approach that uses a throwaway operation result as the placeholder
  (specifically `unrealized_conversion_cast`).
-/
structure ForwardValue where
  /-- Placeholder operation per referenced result index, with that index's first-use location. -/
  placeholders : Std.HashMap Nat (OperationPtr × Location)
  /-- Location of the first use, used for error reporting if the value is never defined. -/
  loc : Location
  deriving Inhabited

structure MlirParserData (OpInfo : Type) [HasOpInfo OpInfo] where
  /-- The current IR context. -/
  ctx : WfIRContext OpInfo
  /-- The values that have been defined for a given name at that point in the parser,
      along with the byte offset of where the value name token was parsed. -/
  values : Std.HashMap ByteArray (Array ValuePtr × Location)
  /--
    The values defined in each currently active nested scope.
    Each scope sees all values defined in parent scopes (those that appear earlier in the array).
  -/
  definitionsPerScope : Array (Std.HashSet ByteArray)
  /--
    Values referenced but not yet defined, keyed by name. Following MLIR's generic-form parser,
    this table is flat: a definition resolves the forward reference regardless of which region
    it appears in. Entries remaining when top-level parsing finishes are reported as uses of
    undefined values.
  -/
  forwardValues : Std.HashMap ByteArray ForwardValue
  /--
    The blocks that have been encountered during parsing, along with whether
    they have been defined or only forward declared.
  -/
  blocks : Std.HashMap ByteArray BlockEntry
  /-- Whether to accept ops/types/attrs from unregistered dialects. -/
  allowUnregisteredDialect : Bool := false
  /-- Type aliases defined so far, keyed by name without the `!`. -/
  typeAliases : Std.HashMap ByteArray TypeAttr := {}
  /-- The location of each parsed operation. -/
  opLocations : Std.HashMap OperationPtr Location := {}
  deriving Inhabited

/-- Parser block names carry erased bounds certificates, and values carry an erased
provenance predicate. Real definitions are disjoint from temporary operations used
for forward references. -/
structure MlirParserState (OpInfo : Type) [HasOpInfo OpInfo] extends MlirParserData OpInfo where
  blocksInBounds : ∀ (name : ByteArray) (entry : BlockEntry), blocks[name]? = some entry →
    entry.block.InBounds ctx.raw
  realValues : ValuePtr → Prop
  realInBounds : ∀ value, realValues value → value.InBounds ctx.raw
  valuesReal : ∀ (name : ByteArray) (entry : Array ValuePtr × Location), values[name]? = some entry →
    ∀ value ∈ entry.1, realValues value
  forwardInBounds : ∀ (name : ByteArray) (fwd : ForwardValue), forwardValues[name]? = some fwd →
    ∀ (index : Nat) (op : OperationPtr) (loc : Location), fwd.placeholders[index]? = some (op, loc) →
      (ValuePtr.opResult (op.getResult 0)).InBounds ctx.raw
  realNotPlaceholder : ∀ value, realValues value →
    ∀ (name : ByteArray) (fwd : ForwardValue), forwardValues[name]? = some fwd →
    ∀ (index : Nat) (op : OperationPtr) (loc : Location), fwd.placeholders[index]? = some (op, loc) →
      match value with
      | .opResult result => result.op ≠ op
      | .blockArgument _ => True
  forwardUnique : ∀ (name : ByteArray) (fwd : ForwardValue), forwardValues[name]? = some fwd →
    ∀ (index : Nat) (op : OperationPtr) (loc : Location), fwd.placeholders[index]? = some (op, loc) →
    ∀ (name' : ByteArray) (fwd' : ForwardValue), forwardValues[name']? = some fwd' →
    ∀ (index' : Nat) (loc' : Location), fwd'.placeholders[index']? = some (op, loc') →
      name = name' ∧ index = index'

def MlirParserState.fromContext (ctx : WfIRContext OpInfo)
    (allowUnregisteredDialect : Bool := false) : MlirParserState OpInfo :=
  {
    ctx
    allowUnregisteredDialect
    values := Std.HashMap.emptyWithCapacity 128
    definitionsPerScope := #[Std.HashSet.emptyWithCapacity 2]
    forwardValues := Std.HashMap.emptyWithCapacity 1
    blocks := Std.HashMap.emptyWithCapacity 1
    blocksInBounds := by simp
    realValues := fun _ => False
    realInBounds := by simp
    valuesReal := by simp
    forwardInBounds := by simp
    realNotPlaceholder := by simp
    forwardUnique := by simp
  }

instance : Inhabited (MlirParserState OpInfo) := ⟨.fromContext default⟩

/-- Transport the erased certificates without traversing either name table. -/
@[inline]
def MlirParserState.withContext (s : MlirParserState OpInfo) (ctx : WfIRContext OpInfo)
    (preserves : ∀ (value : ValuePtr), value.InBounds s.ctx.raw → value.InBounds ctx.raw)
    (structurePreserves : StructuralBoundsPreserved s.ctx.raw ctx.raw) :
    MlirParserState OpInfo :=
  { s with
    ctx
    blocksInBounds := fun name entry he => structurePreserves.blocks _ (s.blocksInBounds name entry he)
    realInBounds := fun value h => preserves value (s.realInBounds value h)
    forwardInBounds := fun name fwd hf index op loc hp =>
      preserves _ (s.forwardInBounds name fwd hf index op loc hp)
  }

/-- Byte-array names use structural equality in the parser's hash tables. -/
local instance : LawfulBEq ByteArray where
  rfl := by
    intro a
    change (a.data == a.data) = true
    exact BEq.rfl
  eq_of_beq := by
    intro a b h
    apply ByteArray.ext
    exact eq_of_beq (show (a.data == b.data) = true from h)

/-- Extend the erased set of real definitions. -/
@[inline]
def MlirParserState.addRealValues (s : MlirParserState OpInfo) (values : Array ValuePtr)
    (hBounds : ∀ value ∈ values, value.InBounds s.ctx.raw)
    (hDifferent : ∀ value ∈ values,
      ∀ (name : ByteArray) (fwd : ForwardValue), s.forwardValues[name]? = some fwd →
      ∀ (index : Nat) (op : OperationPtr) (loc : Location),
        fwd.placeholders[index]? = some (op, loc) →
        match value with
        | .opResult result => result.op ≠ op
        | .blockArgument _ => True) : MlirParserState OpInfo :=
  { s with
    realValues := fun value => s.realValues value ∨ value ∈ values
    realInBounds := by
      intro value h
      exact h.elim (s.realInBounds value) (hBounds value)
    valuesReal := by
      intro name entry he value hv
      exact .inl (s.valuesReal name entry he value hv)
    realNotPlaceholder := by
      intro value h name fwd hf index op loc hp
      exact h.elim
        (fun hv => s.realNotPlaceholder value hv name fwd hf index op loc hp)
        (fun hv => hDifferent value hv name fwd hf index op loc hp)
  }

/-- Register a fresh operation as a forward reference placeholder. -/
@[inline]
def MlirParserState.insertForwardPlaceholder (s : MlirParserState OpInfo)
    (name : ByteArray) (index : Nat) (op : OperationPtr) (loc : Location)
    (hBounds : (ValuePtr.opResult (op.getResult 0)).InBounds s.ctx.raw)
    (hReal : ∀ value, s.realValues value → match value with
      | .opResult result => result.op ≠ op
      | .blockArgument _ => True)
    (hOthers : ∀ (name' : ByteArray) (fwd : ForwardValue),
      s.forwardValues[name']? = some fwd →
      ∀ (index' : Nat) (op' : OperationPtr) (loc' : Location),
        fwd.placeholders[index']? = some (op', loc') → op' ≠ op) : MlirParserState OpInfo := by
  let fwd := s.forwardValues[name]?.getD { placeholders := {}, loc }
  let updated := { fwd with placeholders := fwd.placeholders.insert index (op, loc) }
  let table := s.forwardValues.insert name updated
  have lookup : ∀ (name' : ByteArray) (fwd' : ForwardValue), table[name']? = some fwd' →
      ∀ (index' : Nat) (op' : OperationPtr) (loc' : Location),
      fwd'.placeholders[index']? = some (op', loc') →
      (name' = name ∧ index' = index ∧ op' = op ∧ loc' = loc) ∨
      ∃ old : ForwardValue, s.forwardValues[name']? = some old ∧
        old.placeholders[index']? = some (op', loc') := by
    intro name' fwd' hf index' op' loc' hp
    cases ho : s.forwardValues[name]? <;>
      grind
  exact { s with
    forwardValues := table
    forwardInBounds := by
      intro name' fwd' hf index' op' loc' hp
      rcases lookup name' fwd' hf index' op' loc' hp with hn | ⟨old, ho, hp⟩
      · rcases hn with ⟨rfl, rfl, rfl, rfl⟩
        exact hBounds
      · exact s.forwardInBounds name' old ho index' op' loc' hp
    realNotPlaceholder := by
      intro value hv name' fwd' hf index' op' loc' hp
      rcases lookup name' fwd' hf index' op' loc' hp with hn | ⟨old, ho, hp⟩
      · rcases hn with ⟨rfl, rfl, rfl, rfl⟩
        exact hReal value hv
      · exact s.realNotPlaceholder value hv name' old ho index' op' loc' hp
    forwardUnique := by
      intro name' fwd' hf index' op' loc' hp name'' fwd'' hf' index'' loc'' hp'
      have h1 := lookup name' fwd' hf index' op' loc' hp
      have h2 := lookup name'' fwd'' hf' index'' op' loc'' hp'
      rcases h1 with hn1 | ⟨old1, ho1, hp1⟩ <;>
        rcases h2 with hn2 | ⟨old2, ho2, hp2⟩
      · grind
      · have := hOthers name'' old2 ho2 index'' op' loc'' hp2
        grind
      · have := hOthers name' old1 ho1 index' op' loc' hp1
        grind
      · exact s.forwardUnique name' old1 ho1 index' op' loc' hp1
          name'' old2 ho2 index'' loc'' hp2
  }

/-- Remove a resolved placeholder and transport the certificates through its erasure. -/
@[inline]
def MlirParserState.eraseForwardPlaceholder (s : MlirParserState OpInfo)
    (name : ByteArray) (fwd : ForwardValue) (hf : s.forwardValues[name]? = some fwd)
    (index : Nat) (op : OperationPtr) (loc : Location)
    (hp : fwd.placeholders[index]? = some (op, loc)) (ctx' : WfIRContext OpInfo)
    (hBounds : ∀ (value : ValuePtr),
      (match value with
      | .opResult result => result.op ≠ op
      | .blockArgument _ => True) →
      value.InBounds s.ctx.raw → value.InBounds ctx'.raw)
    (structurePreserves : StructuralBoundsPreserved s.ctx.raw ctx'.raw) : MlirParserState OpInfo := by
  let updated := { fwd with placeholders := fwd.placeholders.erase index }
  let table := s.forwardValues.insert name updated
  have lookup : ∀ (name' : ByteArray) (fwd' : ForwardValue), table[name']? = some fwd' →
      ∀ (index' : Nat) (op' : OperationPtr) (loc' : Location),
      fwd'.placeholders[index']? = some (op', loc') →
      ∃ old : ForwardValue, s.forwardValues[name']? = some old ∧
        old.placeholders[index']? = some (op', loc') ∧ (name' = name → index' ≠ index) := by
    intro name' fwd' hf' index' op' loc' hp'
    grind
  exact { s with
    ctx := ctx'
    blocksInBounds := fun name entry he => structurePreserves.blocks _ (s.blocksInBounds name entry he)
    forwardValues := table
    realInBounds := by
      intro value hv
      exact hBounds value (s.realNotPlaceholder value hv name fwd hf index op loc hp)
        (s.realInBounds value hv)
    forwardInBounds := by
      intro name' fwd' hf' index' op' loc' hp'
      obtain ⟨old, ho, hpold, hslot⟩ := lookup name' fwd' hf' index' op' loc' hp'
      have hne : op' ≠ op := by
        intro he
        subst op'
        have hu := s.forwardUnique name fwd hf index op loc hp name' old ho index' loc' hpold
        grind
      have hb := s.forwardInBounds name' old ho index' op' loc' hpold
      have := hBounds (.opResult (op'.getResult 0)) (by simpa using hne) (by simpa using hb)
      simpa using this
    realNotPlaceholder := by
      intro value hv name' fwd' hf' index' op' loc' hp'
      obtain ⟨old, ho, hpold, _⟩ := lookup name' fwd' hf' index' op' loc' hp'
      exact s.realNotPlaceholder value hv name' old ho index' op' loc' hpold
    forwardUnique := by
      intro name' fwd' hf' index' op' loc' hp' name'' fwd'' hf'' index'' loc'' hp''
      obtain ⟨old1, ho1, hp1, _⟩ := lookup name' fwd' hf' index' op' loc' hp'
      obtain ⟨old2, ho2, hp2, _⟩ := lookup name'' fwd'' hf'' index'' op' loc'' hp''
      exact s.forwardUnique name' old1 ho1 index' op' loc' hp1 name'' old2 ho2 index'' loc'' hp2
  }

abbrev MlirParserM (OpInfo : Type) [HasOpInfo OpInfo] :=
  StateT (MlirParserState OpInfo) (EStateM ParserError ParserState)

/--
  Execute the action with the given initial state.
  Returns the result along with the final state, or an error message.
-/
def MlirParserM.run (self : MlirParserM OpInfo α)
  (mlirParserState : MlirParserState OpInfo) (parserState: ParserState) :
    Except ParserError (α × MlirParserState OpInfo × ParserState) :=
  match (StateT.run self mlirParserState).run parserState with
  | .ok (a, mlirParserState) parserState => .ok (a, mlirParserState, parserState)
  | .error err _ => .error err

/--
  Execute the action with the given initial state.
  Returns the result or an error message.
-/
def MlirParserM.run' (self : MlirParserM OpInfo α)
  (mlirParserState : MlirParserState OpInfo) (parserState: ParserState) : Except ParserError α :=
  match self.run mlirParserState parserState with
  | .ok (a, _, _) => .ok a
  | .error err => .error err

/--
  Get the current IR context that is stored in the parser state.
-/
def getContext : MlirParserM OpInfo (WfIRContext OpInfo) := do
  return (← get).ctx

/--
  Get the array of values associated with a previously parsed name.
-/
def getValues? (name : ByteArray) : MlirParserM OpInfo (Option (Array ValuePtr × Location)) := do
  return (← get).values[name]?

/--
  Get the original input that is being parsed.
-/
def getInput : MlirParserM OpInfo ByteArray := do
  return (← getThe ParserState).input

/--
  Run an action within a new nested scope. This scope will be able to see all definitions in
  parent scopes and any definitions it add will only be visible within it and child scopes.
-/
def inChildScope {α : Type} (m : MlirParserM OpInfo α) : MlirParserM OpInfo α := do
  /- Push a new scope. -/
  modify fun s => { s with definitionsPerScope := s.definitionsPerScope.push (.emptyWithCapacity 128) }

  let result ← m

  /- Pop the scope. -/
  modify fun (s : MlirParserState OpInfo) => Id.run do
    let mut values : { table : Std.HashMap ByteArray (Array ValuePtr × Location) //
        ∀ (name : ByteArray) (entry : Array ValuePtr × Location), table[name]? = some entry → ∀ value ∈ entry.1, s.realValues value } :=
      ⟨s.values, s.valuesReal⟩
    /- Erase each variable defined in the last scope. -/
    for name in s.definitionsPerScope.back! do
      values := ⟨values.val.erase name, by
        intro key entry h value hv
        have := values.property
        grind⟩
    { s with
      values := values.val
      definitionsPerScope := s.definitionsPerScope.pop
      valuesReal := values.property }

  return result

/-- Consume the complete state while producing new bounds certificates. -/
private def modifyParserStateM'
    (f : (s : MlirParserState OpInfo) → EStateM ParserError ParserState (α × MlirParserState OpInfo)) :
    MlirParserM OpInfo α := do
  let s ← get
  set (default : MlirParserState OpInfo)
  let (result, s') ← f s
  set s'
  return result

/-- Remove a completed forward-reference name without traversing the table. -/
private def MlirParserState.eraseForwardName (s : MlirParserState OpInfo) (name : ByteArray) :
    MlirParserState OpInfo :=
  { s with
    forwardValues := s.forwardValues.erase name
    forwardInBounds := by
      intro key fwd hf index op loc hp
      exact s.forwardInBounds key fwd (by grind) index op loc hp
    realNotPlaceholder := by
      intro value hv key fwd hf index op loc hp
      exact s.realNotPlaceholder value hv key fwd (by grind) index op loc hp
    forwardUnique := by
      intro key fwd hf index op loc hp key' fwd' hf' index' loc' hp'
      exact s.forwardUnique key fwd (by grind) index op loc hp key' fwd' (by grind) index' loc' hp'
  }

/-- Replace a placeholder using the certificates belonging to its table entry and target. -/
private def rewirePlaceholderState (s : MlirParserState OpInfo)
    (name : ByteArray) (fwd : ForwardValue) (hf : s.forwardValues[name]? = some fwd)
    (index : Nat) (placeholderOp : OperationPtr) (useLoc : Location)
    (hp : fwd.placeholders[index]? = some (placeholderOp, useLoc))
    (target : ValuePtr) (ht : s.realValues target) :
    EStateM ParserError ParserState { s' : MlirParserState OpInfo //
      s'.realValues = s.realValues ∧ StructuralBoundsPreserved s.ctx.raw s'.ctx.raw } := do
  let placeholderValue : ValuePtr := placeholderOp.getResult 0
  let hOld := s.forwardInBounds name fwd hf index placeholderOp useLoc hp
  let hNew := s.realInBounds target ht
  let ⟨hNe⟩ ← checkValuesNe placeholderValue target
  let ctx := WfRewriter.replaceValue s.ctx placeholderValue target hNe hOld hNew
  let hStructure := WfRewriter.replaceValue_structuralBoundsPreserved
    (ctx := s.ctx) (oldValue := placeholderValue) (newValue := target)
    (ne := hNe) (oldIn := hOld) (newIn := hNew)
  let s := s.withContext ctx (fun value h => by
    have := WfRewriter.replaceValue_inBounds (ptr := .value value) (ctx := s.ctx) (oldValue := placeholderValue) (newValue := target) (ne := hNe) (oldIn := hOld) (newIn := hNew)
    grind) hStructure
  let hOpIn := OperationPtr.inBounds_of_result_value_inBounds
    (s.forwardInBounds name fwd hf index placeholderOp useLoc hp)
  let ⟨hNoRegions⟩ ← checkOpNoRegions placeholderOp s.ctx.raw
  let ⟨hNoUses⟩ ← checkOpNoUses placeholderOp s.ctx.raw
  let ctx := WfRewriter.eraseOp s.ctx placeholderOp hNoRegions hNoUses hOpIn
  let s' := s.eraseForwardPlaceholder name fwd hf index placeholderOp useLoc hp ctx
    (fun value hDifferent hBounds =>
      (WfRewriter.eraseOp_valueInBounds_iff (by cases value <;> exact hDifferent)).mpr hBounds)
    WfRewriter.eraseOp_structuralBoundsPreserved
  return ⟨s', rfl, hStructure.trans WfRewriter.eraseOp_structuralBoundsPreserved⟩

/-- Resolve definitions while explicitly transporting their erased provenance. -/
private def registerValueDefsState (s : MlirParserState OpInfo)
    (name : ByteArray) (pos : Location) (values : Array ValuePtr)
    (hValues : ∀ value ∈ values, s.realValues value) :
    EStateM ParserError ParserState { s' : MlirParserState OpInfo //
      s'.realValues = s.realValues ∧ StructuralBoundsPreserved s.ctx.raw s'.ctx.raw } := do
  let mut current : { s' : MlirParserState OpInfo // s'.realValues = s.realValues ∧ StructuralBoundsPreserved s.ctx.raw s'.ctx.raw } := ⟨s, rfl, .refl _⟩
  if let some fwd := s.forwardValues[name]? then
    for (index, _) in fwd.placeholders do
      match hf : current.val.forwardValues[name]? with
      | none => pure ()
      | some liveFwd =>
        match hp : liveFwd.placeholders[index]? with
        | none => pure ()
        | some (placeholderOp, useLoc) =>
          let real ← match hValue : values[index]? with
            | none => throw (({ msg := s!"definition of value %{String.fromUTF8! name} provides {values.size} results, but result #{index} was used", pos := some pos } : ParserError).addNote useLoc "value used here")
            | some value => pure (⟨value, by grind⟩ : { value : ValuePtr // value ∈ values })
          let realValue := real.val
          let hReal : current.val.realValues realValue := by
            rw [current.property.1]
            exact hValues realValue real.property
          let placeholderValue : ValuePtr := placeholderOp.getResult 0
          let usedType := placeholderValue.getType current.val.ctx.raw
            (current.val.forwardInBounds name liveFwd hf index placeholderOp useLoc hp)
          let definedType := realValue.getType current.val.ctx.raw (current.val.realInBounds realValue hReal)
          if usedType ≠ definedType then
            throw (({ msg := s!"definition of value %{String.fromUTF8! name}#{index} has type {definedType} but was used with type {usedType}",
                      pos := some pos } : ParserError).addNote useLoc "value used here")
          let updated ← rewirePlaceholderState current.val name liveFwd hf index placeholderOp useLoc hp realValue hReal
          current := ⟨updated.val, updated.property.1.trans current.property.1, current.property.2.trans updated.property.2⟩
    current := ⟨current.val.eraseForwardName name, current.property⟩
  if let some (_, existingPos) := current.val.values[name]? then
    let error := ParserError.mk s!"value %{String.fromUTF8! name} has already been defined" pos []
    throw (error.addNote existingPos "previously defined here")
  let currentState := current.val
  let result : MlirParserState OpInfo :=
    { currentState with
      values := currentState.values.insert name (values, pos)
      definitionsPerScope := currentState.definitionsPerScope.modify
        (currentState.definitionsPerScope.size - 1) (·.insert name)
      valuesReal := by
        intro key entry h value hv
        have hOld := currentState.valuesReal
        have hNew : ∀ value ∈ values, currentState.realValues value := by
          intro value hv
          rw [current.property.1]
          exact hValues value hv
        grind
    }
  return ⟨result, current.property⟩

/--
  Parse an operation result and the number of values it defines.
  This corresponds to the syntax `%name` and `%name:numberOfResults`.
-/
def parseOpResult : MlirParserM OpInfo (ByteArray × Nat × Location) := do
  let nameToken ← parseToken .percentIdent "operation result expected"
  let tokenPos := nameToken.slice.start
  let slice := { nameToken.slice with start := nameToken.slice.start + 1 } -- skip % character
  let name := slice.of (← getInput)

  /- If the next token is ':', we parse the expected result count, otherwise we return the name. -/
  if !(← parseOptionalToken .colon).isSome then
    return (name, 1, tokenPos)

  let count := (← parseInteger false false).toNat
  if count ≤ 1 then
    throwAt tokenPos "expected named operation to have at least 1 result"

  return (name, count, tokenPos)

/--
  Parse the results before an operation definition,
  either as a list of values followed by '=', or nothing.
-/
def parseOpResults : MlirParserM OpInfo (Array (ByteArray × Nat × Location)) := do
  let .percentIdent := (← peekToken).kind | return #[]
  let results ← parseList parseOpResult
  parsePunctuation "=" "'=' expected after operation results"
  return results

/--
  An operand whose type has not yet been resolved.
  This is used during parsing to allow parsing operands before their types.
  Once the operation type is known, operand resolution produces an SSA value with its
  bounds certificate and checks that its type matches previous uses.

  `index` is used for the `%name#index` syntax to refer to an indexed result
  when multiple are defined for the same value.
-/
structure UnresolvedOperand where
  name : ByteArray
  index : Option Nat
  pos : Location

/--
  Get the name of an UnresolvedOperand as a String.
-/
def UnresolvedOperand.nameString (operand : UnresolvedOperand) : String :=
  String.fromUTF8! operand.name

/--
  Get the result index of an UnresolvedOperand. If one was not specified explicitly, this
  defaults to 0.
-/
def UnresolvedOperand.indexD (operand : UnresolvedOperand) : Nat :=
  operand.index.getD 0

instance : ToString UnresolvedOperand where
  toString operand :=
    match operand.index with
    | none => s!"%{operand.nameString}"
    | some n => s!"%{operand.nameString}#{n}"

/--
  Parse an operation operand.
  This has the syntax `%name` or `%name#resultCount`.
-/
def parseOperand : MlirParserM OpInfo UnresolvedOperand := do
  let nameToken ← parseToken .percentIdent "operand expected"
  let tokenPos := nameToken.slice.start
  let name : ByteArray := { nameToken.slice with start := nameToken.slice.start + 1 }.of (← getInput)

  /- If no result number is specified, return without one. -/
  let some resultCount ← parseOptionalToken .hashIdent
    | return UnresolvedOperand.mk name none tokenPos

  /- Parse the result count as a Nat. -/
  let hashPos := resultCount.slice.start
  let resultCount := { resultCount.slice with start := resultCount.slice.start + 1 }.of (← getInput) -- skip # character
  let some resultCount := String.fromUTF8? resultCount >>= String.toNat?
    | throwAt hashPos "invalid SSA value result number"
  return UnresolvedOperand.mk name resultCount tokenPos

/--
  Parse a list of operation operands delimited by parentheses.
-/
def parseOperands : MlirParserM OpInfo (Array UnresolvedOperand) := do
  parseDelimitedList .paren parseOperand

/-- A resolved value and the context transition that preserves earlier operand certificates. -/
private structure ResolvedOperand (s : MlirParserState OpInfo) where
  value : ValuePtr
  state : MlirParserState OpInfo
  inBounds : value.InBounds state.ctx.raw
  realValues_eq : state.realValues = s.realValues
  preserves : ∀ (value : ValuePtr), value.InBounds s.ctx.raw → value.InBounds state.ctx.raw
  preservesStructure : StructuralBoundsPreserved s.ctx.raw state.ctx.raw

private def createForwardOperandState (s : MlirParserState OpInfo)
    (operand : UnresolvedOperand) (expectedType : TypeAttr) :
    EStateM ParserError ParserState (ResolvedOperand s) := do
  let idx := operand.indexD
  match hCreated : WfRewriter.createOp s.ctx Builtin.unrealized_conversion_cast
      #[expectedType] #[] #[] #[] default none with
  | none => throwAt operand.pos "internal error: failed to create forward-reference placeholder"
  | some (ctx', op) =>
    let hPreserves : ∀ (value : ValuePtr), value.InBounds s.ctx.raw → value.InBounds ctx'.raw :=
      fun _ h => WfRewriter.createOp_valueInBounds_mono hCreated h
    let hStructure := WfRewriter.createOp_structuralBoundsPreserved hCreated
    let next := s.withContext ctx' hPreserves hStructure
    let result := next.insertForwardPlaceholder operand.name idx op operand.pos
      (by simpa [next, MlirParserState.withContext] using WfRewriter.createOp_result_inBounds hCreated 0 (by simp))
      (by
        intro value hv
        have h := WfRewriter.createOp_existingValue_not_result hCreated (s.realInBounds value hv)
        cases value <;> exact h)
      (by
        intro name fwd hf index oldOp loc hp
        have hOld := s.forwardInBounds name fwd hf index oldOp loc hp
        have hDifferent := WfRewriter.createOp_existingValue_not_result hCreated hOld
        simpa using hDifferent)
    return {
      value := op.getResult 0
      state := result
      inBounds := by simpa [result, MlirParserState.insertForwardPlaceholder, next, MlirParserState.withContext] using WfRewriter.createOp_result_inBounds hCreated 0 (by simp)
      realValues_eq := rfl
      preserves := hPreserves
      preservesStructure := hStructure
    }

private def resolveForwardOperandState (s : MlirParserState OpInfo)
    (operand : UnresolvedOperand) (expectedType : TypeAttr) :
    EStateM ParserError ParserState (ResolvedOperand s) := do
  let idx := operand.indexD
  match hf : s.forwardValues[operand.name]? with
  | none => createForwardOperandState s operand expectedType
  | some fwd =>
    match hp : fwd.placeholders[idx]? with
    | none => createForwardOperandState s operand expectedType
    | some (placeholderOp, useLoc) =>
      let placeholderValue : ValuePtr := placeholderOp.getResult 0
      let parsedType := placeholderValue.getType s.ctx.raw
        (s.forwardInBounds operand.name fwd hf idx placeholderOp useLoc hp)
      if parsedType ≠ expectedType then
        throw (({ msg := s!"type mismatch for value {operand}: expected {expectedType}, got {parsedType}",
                  pos := some operand.pos } : ParserError).addNote useLoc "value first used here")
      return {
        value := placeholderValue
        state := s
        inBounds := s.forwardInBounds operand.name fwd hf idx placeholderOp useLoc hp
        realValues_eq := rfl
        preserves := fun _ h => h
        preservesStructure := .refl _
      }

private def resolveOperandState (s : MlirParserState OpInfo)
    (operand : UnresolvedOperand) (expectedType : TypeAttr) :
    EStateM ParserError ParserState (ResolvedOperand s) := do
  match hValues : s.values[operand.name]? with
  | none => resolveForwardOperandState s operand expectedType
  | some (values, defPos) =>
    let real ← match hValue : values[operand.indexD]? with
      | none => throw (({ msg := s!"invalid result index {operand.indexD} for %{operand.nameString}", pos := some operand.pos } : ParserError).addNote defPos "value defined here")
      | some value => pure (⟨value, by grind⟩ : { value : ValuePtr // value ∈ values })
    let value := real.val
    let hBounds := s.realInBounds value (s.valuesReal operand.name (values, defPos) hValues value real.property)
    let parsedType := value.getType s.ctx.raw hBounds
    if parsedType ≠ expectedType then
      throw (({ msg := s!"type mismatch for value {operand}: expected {expectedType}, got {parsedType}",
                pos := some operand.pos } : ParserError).addNote defPos "value defined here")
    return {
      value
      state := s
      inBounds := hBounds
      realValues_eq := rfl
      preserves := fun _ h => h
      preservesStructure := .refl _
    }

private structure ResolvedOperands (s : MlirParserState OpInfo) where
  values : Array ValuePtr
  state : MlirParserState OpInfo
  inBounds : ∀ value ∈ values, value.InBounds state.ctx.raw
  realValues_eq : state.realValues = s.realValues
  preserves : ∀ (value : ValuePtr), value.InBounds s.ctx.raw → value.InBounds state.ctx.raw
  preservesStructure : StructuralBoundsPreserved s.ctx.raw state.ctx.raw

/-- Resolve operands with a fixed initial state so the runtime loop remains tail recursive. -/
private def resolveOperandsFrom (initial state : MlirParserState OpInfo)
    (operands : List (UnresolvedOperand × TypeAttr)) (values : Array ValuePtr)
    (hValues : ∀ value ∈ values, value.InBounds state.ctx.raw)
    (hReal : state.realValues = initial.realValues)
    (hPreserves : ∀ (value : ValuePtr), value.InBounds initial.ctx.raw → value.InBounds state.ctx.raw)
    (hStructure : StructuralBoundsPreserved initial.ctx.raw state.ctx.raw) :
    EStateM ParserError ParserState (ResolvedOperands initial) := do
  match operands with
  | [] => return ⟨values, state, hValues, hReal, hPreserves, hStructure⟩
  | (operand, ty) :: rest =>
    let resolved ← resolveOperandState state operand ty
    let nextValues := values.push resolved.value
    let hNext : ∀ value ∈ nextValues, value.InBounds resolved.state.ctx.raw := by
      intro value hv
      have hOld := fun value hv => resolved.preserves value (hValues value hv)
      have hNew := resolved.inBounds
      grind
    resolveOperandsFrom initial resolved.state rest nextValues hNext
      (resolved.realValues_eq.trans hReal)
      (fun value h => resolved.preserves value (hPreserves value h))
      (hStructure.trans resolved.preservesStructure)

private def resolveOperandsState (state : MlirParserState OpInfo)
    (operands : List (UnresolvedOperand × TypeAttr)) (values : Array ValuePtr)
    (hValues : ∀ value ∈ values, value.InBounds state.ctx.raw) :
    EStateM ParserError ParserState (ResolvedOperands state) :=
  resolveOperandsFrom state state operands values hValues rfl (fun _ h => h) (.refl _)

/-- The attribute parser state derived from the current parser state. -/
def attrParserState : MlirParserM OpInfo AttrParserState := do
  let state ← get
  return {
    allowUnregisteredDialect := state.allowUnregisteredDialect
    typeAliases := state.typeAliases
  }

/--
  Parse a type, if present.
-/
def parseOptionalType : MlirParserM OpInfo (Option TypeAttr) := do
  match AttrParser.parseOptionalType.run (← attrParserState) (← getThe ParserState) with
  | .ok (ty, _, parserState) =>
    set parserState
    return ty
  | .error err => throw err

/--
  Parse a type, otherwise return an error.
-/
def parseType (errorMsg : String := "type expected") : MlirParserM OpInfo TypeAttr := do
  match ← parseOptionalType with
  | some ty => return ty
  | none => throwAtCurrentPos errorMsg

/--
  Parse an operation type, consisting of a colon followed by a function type.
-/
def parseOperationType : MlirParserM OpInfo (Array TypeAttr × Array TypeAttr) := do
  parsePunctuation ":"
  let inputs ← parseDelimitedList .paren parseType
  parsePunctuation "->"
  if (←peekToken).kind = .lParen then
    let outputs ← parseDelimitedList .paren parseType
    return (inputs, outputs)
  else
    let outputType ← parseType
    return (inputs, #[outputType])

/--
  Parse an SSA value followed by a colon and a type, if present.
  Also returns the location of the value definition.
-/
def parseTypedValue : MlirParserM OpInfo (ByteArray × TypeAttr × Location) := do
  let nameToken ← parseToken .percentIdent "value expected"
  let tokenPos := nameToken.slice.start
  let slice := { nameToken.slice with start := nameToken.slice.start + 1 } -- skip % character
  let name := slice.of (← getInput)
  parsePunctuation ":"
  let ty ← parseType
  return (name, ty, tokenPos)

/--
  Parse the properties of an operation.
  Currently, these properties are not stored in the IR, but we still need to parse them to be able
  to parse valid MLIR syntax.
  The integer literals in a `mod_arith` operation's properties are kept as written (see
  `AttrParserState.rawIntegerLiterals`).
-/
def parseOpProperties (opCode : OpInfo) : MlirParserM OpInfo (propertiesOf opCode) := do
  let propertiesStart ← getPos
  if not (← parseOptionalPunctuation "<") then
    match IsOpCode.fromAttrDict opCode {} with
    | .ok properties => return properties
    | .error err => throwAtCurrentPos err
  let rawIntegerLiterals :=
    (String.fromUTF8! (IsOpCode.name opCode)).startsWith "mod_arith."
  let attrState := { (← attrParserState) with rawIntegerLiterals }
  match AttrParser.parseAttributeDictionary.run attrState (← getThe ParserState) with
  | .ok (properties, _, parserState) =>
    set parserState
    parsePunctuation ">"
    match IsOpCode.fromAttrDict opCode (.ofArray properties) with
    | .ok properties => return properties
    | .error err => throwAt propertiesStart err
  | .error err => throw err

/--
Record the source operation name in the properties of a `builtin.unregistered`
operation.
-/
private def optionallySetUnregisteredOpName (opCode : OpInfo)
    (properties : propertiesOf opCode) (opName : ByteArray) :
    propertiesOf opCode :=
  if h : some .unregistered = toDialect? Builtin opCode then
    have h' : ofDialect OpInfo Builtin.unregistered = opCode := by grind
    let properties : UnregisteredProperties :=
      HasDialect.toDialectProperties Builtin.unregistered (h' ▸ properties)
    let properties := { properties with opName := opName }
    h' ▸ HasDialect.ofDialectProperties OpInfo Builtin.unregistered properties
  else
    properties

/--
  Parse the attributes of an operation, if present.
  Currently, these attributes are not stored in the IR, but we still need to parse them to be able
  to parse valid MLIR syntax.
-/
def parseOpAttributes : MlirParserM OpInfo DictionaryAttr := do
  match AttrParser.parseOptionalAttributeDictionary.run (← attrParserState) (← getThe ParserState) with
  | .ok (attrs, _, parserState) =>
    set parserState
    match attrs with
    | none => return DictionaryAttr.empty
    | some attrs => return DictionaryAttr.fromArray attrs
  | .error err => throw err

/-- Syntax actions used by the explicit-state parser only inspect MLIR state. Their
returned MLIR state is discarded; lexer state and diagnostics are retained. -/
private def readSyntax (s : MlirParserState OpInfo) (m : MlirParserM OpInfo α) :
    EStateM ParserError ParserState α := do
  let (value, _) ← m s
  return value

/-- A parser result with erased bounds and structural context transport. -/
private structure Parsed (s : MlirParserState OpInfo) (α : Type)
    (bounds : α → IRContext OpInfo → Prop) where
  value : α
  state : MlirParserState OpInfo
  inBounds : bounds value state.ctx.raw
  preserves : StructuralBoundsPreserved s.ctx.raw state.ctx.raw

private abbrev ParsedBlock (s : MlirParserState OpInfo) := Parsed s BlockPtr BlockPtr.InBounds
private abbrev ParsedBlocks (s : MlirParserState OpInfo) :=
  Parsed s (Array BlockPtr) (fun blocks ctx => ∀ block ∈ blocks, block.InBounds ctx)
private abbrev ParsedRegion (s : MlirParserState OpInfo) := Parsed s RegionPtr RegionPtr.InBounds
private abbrev ParsedRegions (s : MlirParserState OpInfo) :=
  Parsed s (Array RegionPtr) (fun regions ctx => ∀ region ∈ regions, region.InBounds ctx)
private abbrev ParsedOptionalBlock (s : MlirParserState OpInfo) :=
  Parsed s (Option BlockPtr) (fun block ctx => block.maybe BlockPtr.InBounds ctx)
private abbrev ParsedOptionalOp (s : MlirParserState OpInfo) :=
  Parsed s (Option OperationPtr) (fun _ _ => True)

@[inline]
private def MlirParserState.insertBlockName (s : MlirParserState OpInfo)
    (name : ByteArray) (entry : BlockEntry) (h : entry.block.InBounds s.ctx.raw) :
    MlirParserState OpInfo :=
  { s with
    blocks := s.blocks.insert name entry
    blocksInBounds := by
      intro key value hv
      have hOld := s.blocksInBounds
      grind }

private def defineBlockState (s : MlirParserState OpInfo) (name : ByteArray)
    (ip : BlockInsertPoint) (hip : ip.InBounds s.ctx.raw) (loc : Location) :
    EStateM ParserError ParserState (ParsedBlock s) := do
  match he : s.blocks[name]? with
  | some (.Defined _ prevLoc) =>
    throw (({ msg := s!"block %{String.fromUTF8! name} has already been defined",
                    pos := some loc } : ParserError).addNote prevLoc "block previously defined here")
  | some (.ForwardDeclared block oldLoc) =>
    let hb := s.blocksInBounds name (.ForwardDeclared block oldLoc) he
    match hc : WfRewriter.insertBlock s.ctx block ip hb hip with
    | none => throwAt loc "internal error: failed to insert block"
    | some ctx =>
      let hs := WfRewriter.insertBlock_structuralBoundsPreserved hc
      let next := s.withContext ctx (fun _ h => WfRewriter.insertBlock_valueInBounds_mono hc h) hs
      let hb := hs.blocks block hb
      return ⟨block, next.insertBlockName name (.Defined block loc) hb, hb, hs⟩
  | none =>
    match hc : WfRewriter.createBlock s.ctx #[] ip (by simpa using hip) with
    | none => throwAt loc "internal error: failed to create block"
    | some (ctx, block) =>
      let hs := WfRewriter.createBlock_structuralBoundsPreserved hc
      let next := s.withContext ctx (fun _ h => WfRewriter.createBlock_valueInBounds_mono hc h) hs
      let hb := WfRewriter.createBlock_new_inBounds hc
      return ⟨block, next.insertBlockName name (.Defined block loc) hb, hb, hs⟩

private def defineBlockUseState (s : MlirParserState OpInfo) (name : ByteArray) (loc : Location) :
    EStateM ParserError ParserState (ParsedBlock s) := do
  match he : s.blocks[name]? with
  | some entry => return ⟨entry.block, s, s.blocksInBounds name entry he, .refl _⟩
  | none =>
    match hc : WfRewriter.createBlock s.ctx #[] none Option.maybe_none with
    | none => throwAt loc "internal error: failed to create block"
    | some (ctx, block) =>
      let hs := WfRewriter.createBlock_structuralBoundsPreserved hc
      let next := s.withContext ctx (fun _ h => WfRewriter.createBlock_valueInBounds_mono hc h) hs
      let hb := WfRewriter.createBlock_new_inBounds hc
      return ⟨block, next.insertBlockName name (.ForwardDeclared block loc) hb, hb, hs⟩

private def parseBlockOperandState (s : MlirParserState OpInfo) :
    EStateM ParserError ParserState (ParsedBlock s) := do
  let token ← readSyntax s (parseToken .caretIdent "block name expected")
  let name := { token.slice with start := token.slice.start + 1 }.of (← readSyntax s getInput)
  defineBlockUseState s name token.slice.start

private partial def parseBlockOperandsLoop (initial s : MlirParserState OpInfo)
    (blocks : Array BlockPtr) (hb : ∀ block ∈ blocks, block.InBounds s.ctx.raw)
    (hs : StructuralBoundsPreserved initial.ctx.raw s.ctx.raw) :
    EStateM ParserError ParserState (ParsedBlocks initial) := do
  let parsed ← parseBlockOperandState s
  let next := blocks.push parsed.value
  let hn : ∀ block ∈ next, block.InBounds parsed.state.ctx.raw := by
    intro block h
    have hOld := fun block h => parsed.preserves.blocks block (hb block h)
    have hNew := parsed.inBounds
    grind
  let hs := hs.trans parsed.preserves
  if ← readSyntax parsed.state (parseOptionalPunctuation ",") then
    parseBlockOperandsLoop initial parsed.state next hn hs
  else
    readSyntax parsed.state (parsePunctuation "]" "closing delimiter ']' expected")
    return ⟨next, parsed.state, hn, hs⟩

private def parseBlockOperandsState (s : MlirParserState OpInfo) :
    EStateM ParserError ParserState (ParsedBlocks s) := do
  if !(← readSyntax s (parseOptionalPunctuation "[")) then
    return ⟨#[], s, by simp, .refl _⟩
  if ← readSyntax s (parseOptionalPunctuation "]") then
    return ⟨#[], s, by simp, .refl _⟩
  parseBlockOperandsLoop s s #[] (by simp) (.refl _)

private def parseOptionalBlockLabelState (s : MlirParserState OpInfo)
    (ip : BlockInsertPoint) (hip : ip.InBounds s.ctx.raw) :
    EStateM ParserError ParserState (ParsedOptionalBlock s) := do
  let some labelToken ← readSyntax s (parseOptionalToken .caretIdent)
    | return ⟨none, s, Option.maybe_none, .refl _⟩
  let name := { labelToken.slice with start := labelToken.slice.start + 1 }.of (← readSyntax s getInput)
  let arguments := (← readSyntax s (parseOptionalDelimitedList .paren parseTypedValue)).getD #[]
  readSyntax s (parsePunctuation ":" "':' expected after block label")
  let parsed ← defineBlockState s name ip hip labelToken.slice.start
  let state := parsed.state
  let block := parsed.value
  let ctx := state.ctx
  let argTypes := arguments.map (·.2.1)
  let h_block_InBounds := parsed.inBounds
  let ⟨h_block_NoArgs⟩ ← checkBlockHasNoArgs block ctx.raw
  let ctx' := WfRewriter.setBlockArguments ctx block argTypes h_block_InBounds
    (by grind [BlockPtr.getArguments!.mem_iff_exists_index])
  let hStructure := WfRewriter.setBlockArguments_structuralBoundsPreserved
  let next := state.withContext ctx' (fun _ hv =>
    WfRewriter.setBlockArguments_valueInBounds_mono h_block_NoArgs hv) hStructure
  let argumentValues : Array ValuePtr := Array.ofFn fun i : Fin arguments.size =>
    .blockArgument { block, index := i.val }
  let next := next.addRealValues argumentValues
    (by
      intro value hv
      rcases Array.mem_ofFn.mp hv with ⟨i, rfl⟩
      have h := WfRewriter.setBlockArguments_inBounds_iff
        (ptr := .value (.blockArgument { block, index := i.val }))
        (ctx := ctx) (blockPtr := block) (types := argTypes)
        (hblock := h_block_InBounds)
        (noUses := by grind [BlockPtr.getArguments!.mem_iff_exists_index])
      exact (GenericPtr.iff_value _).mp (h.mpr (by simp [argTypes])))
    (by
      intro value hv name fwd hf index op loc hp
      rcases Array.mem_ofFn.mp hv with ⟨i, rfl⟩
      trivial)
  let mut current : { state : MlirParserState OpInfo // state.realValues = next.realValues ∧
      StructuralBoundsPreserved next.ctx.raw state.ctx.raw } := ⟨next, rfl, .refl _⟩
  for i in List.finRange arguments.size do
    let (argName, _, tokenPos) := arguments[i]
    let value : ValuePtr := .blockArgument { block, index := i.val }
    let hReal : current.val.realValues value := by
      rw [current.property.1]
      exact Or.inr (Array.mem_ofFn.mpr ⟨i, rfl⟩)
    let registered ← registerValueDefsState current.val argName tokenPos #[value]
      (by
        intro v hv
        simp only [Array.mem_singleton] at hv
        subst v
        exact hReal)
    current := ⟨registered.val, registered.property.1.trans current.property.1,
      current.property.2.trans registered.property.2⟩
  let hs := parsed.preserves.trans (hStructure.trans current.property.2)
  return ⟨some block, current.val,
    (by simpa using current.property.2.blocks block (hStructure.blocks block h_block_InBounds)), hs⟩

/-- Remove the names introduced in the innermost scope, retaining erased provenance. -/
private def scopeValues (s : MlirParserState OpInfo) :
    { table : Std.HashMap ByteArray (Array ValuePtr × Location) //
      ∀ (name : ByteArray) (entry : Array ValuePtr × Location), table[name]? = some entry → ∀ value ∈ entry.1, s.realValues value } := Id.run do
  let mut values := (⟨s.values, s.valuesReal⟩ :
    { table : Std.HashMap ByteArray (Array ValuePtr × Location) //
      ∀ (name : ByteArray) (entry : Array ValuePtr × Location), table[name]? = some entry → ∀ value ∈ entry.1, s.realValues value })
  for name in s.definitionsPerScope.back! do
    values := ⟨values.val.erase name, by
      intro key entry h value hv
      have := values.property
      grind⟩
  return values

private def parseEntryBlockLabelState (s : MlirParserState OpInfo)
    (ip : BlockInsertPoint) (hip : ip.InBounds s.ctx.raw) :
    EStateM ParserError ParserState (ParsedBlock s) := do
  let parsed ← parseOptionalBlockLabelState s ip hip
  match he : parsed.value with
  | some block => return ⟨block, parsed.state, (by simpa [he] using parsed.inBounds), parsed.preserves⟩
  | none =>
    let hip := ip.inBounds_of_structuralBoundsPreserved parsed.preserves hip
    let block ← defineBlockState parsed.state ByteArray.empty ip hip (← readSyntax parsed.state getPos)
    return ⟨block.value, block.state, block.inBounds, parsed.preserves.trans block.preserves⟩

mutual

private partial def parseOpRegionsLoop (initial s : MlirParserState OpInfo)
    (regions : Array RegionPtr) (hr : ∀ region ∈ regions, region.InBounds s.ctx.raw)
    (hs : StructuralBoundsPreserved initial.ctx.raw s.ctx.raw) :
    EStateM ParserError ParserState (ParsedRegions initial) := do
  let parsed ← parseRegionState s
  let next := regions.push parsed.value
  let hn : ∀ region ∈ next, region.InBounds parsed.state.ctx.raw := by
    intro region h
    have hOld := fun region h => parsed.preserves.regions region (hr region h)
    have hNew := parsed.inBounds
    grind
  let hs := hs.trans parsed.preserves
  if ← readSyntax parsed.state (parseOptionalPunctuation ",") then
    parseOpRegionsLoop initial parsed.state next hn hs
  else
    readSyntax parsed.state (parsePunctuation ")" "closing delimiter ')' expected")
    return ⟨next, parsed.state, hn, hs⟩

private partial def parseOpRegionsState (s : MlirParserState OpInfo) :
    EStateM ParserError ParserState (ParsedRegions s) := do
  if !(← readSyntax s (parseOptionalPunctuation "(")) then
    return ⟨#[], s, by simp, .refl _⟩
  if ← readSyntax s (parseOptionalPunctuation ")") then
    return ⟨#[], s, by simp, .refl _⟩
  parseOpRegionsLoop s s #[] (by simp) (.refl _)

/-- Operation insertion during parsing uses a detached operation or the end of a certified block. -/
private partial def parseOptionalOpState (initial : MlirParserState OpInfo)
    (block : Option BlockPtr) (hblock : block.maybe BlockPtr.InBounds initial.ctx.raw) :
    EStateM ParserError ParserState (ParsedOptionalOp initial) := do
  let opStart ← readSyntax initial getPos
  let results ← readSyntax initial parseOpResults
  let opNameStart ← readSyntax initial getPos
  let some opName ← readSyntax initial parseOptionalStringLiteral
    | return ⟨none, initial, trivial, .refl _⟩
  let some opNameStr := String.fromUTF8? opName
    | throwAt opNameStart s!"op '{escapeStringLiteral opName}' not a valid UTF8 string."
  let operands ← readSyntax initial parseOperands
  let blockOperands ← parseBlockOperandsState initial
  let state := blockOperands.state
  let unregisteredOp : OpInfo := ofDialect OpInfo Builtin.unregistered
  let opId := (IsOpCode.fromName opName).getD unregisteredOp
  if opId = unregisteredOp then
    if !state.allowUnregisteredDialect then
      throwAt opNameStart s!"op '{opNameStr}' is not registered. Consider using --allow-unregistered-dialect."
  let properties ← readSyntax state (parseOpProperties opId)
  let properties := optionallySetUnregisteredOpName opId properties opName
  let regions ← parseOpRegionsState state
  let state := regions.state
  let attrs ← readSyntax state parseOpAttributes
  let (inputTypes, outputTypes) ← readSyntax state parseOperationType
  let numResults := (results.toList.map (fun result => result.2.1)).sum
  let ⟨hCounts⟩ : PLift (outputTypes.size = numResults) ←
    if h : outputTypes.size = numResults then pure ⟨h⟩
    else throwAt opNameStart s!"operation '{opNameStr}' declares {outputTypes.size} result types, but {numResults} result values were provided"
  if inputTypes.size ≠ operands.size then
    throwAt opNameStart s!"operation '{opNameStr}' declares {inputTypes.size} operand types, but {operands.size} operands were provided"
  let resolved ← resolveOperandsState state (operands.zip inputTypes).toList #[] (by simp)
  let state := resolved.state
  let ctx := state.ctx
  let hblockOperands : ∀ b ∈ blockOperands.value, b.InBounds ctx.raw := fun b hb =>
    resolved.preservesStructure.blocks b (regions.preserves.blocks b (blockOperands.inBounds b hb))
  let hregions : ∀ r ∈ regions.value, r.InBounds ctx.raw := fun r hr =>
    resolved.preservesStructure.regions r (regions.inBounds r hr)
  let hs := blockOperands.preserves.trans (regions.preserves.trans resolved.preservesStructure)
  let ip : Option InsertPoint := block.map InsertPoint.atEnd
  let hins : ip.maybe InsertPoint.InBounds ctx.raw := by
    cases block with
    | none => exact Option.maybe_none
    | some b => simpa [ip] using hs.blocks b (by simpa using hblock)
  match hctx' : WfRewriter.createOp ctx opId outputTypes resolved.values blockOperands.value regions.value properties ip
      resolved.inBounds hblockOperands hregions hins with
  | none => throwAt opNameStart "internal error: failed to create operation"
  | some (ctx', op) =>
    let ctx'' := WfRewriter.setAttributes ctx' op attrs
      (WfRewriter.createOp_new_inBounds op hctx')
    let hAttrs : StructuralBoundsPreserved ctx'.raw ctx''.raw := WfRewriter.setAttributes_structuralBoundsPreserved
    let hn := (WfRewriter.createOp_structuralBoundsPreserved hctx').trans hAttrs
    let contextState := state.withContext ctx'' (by
      intro value hv
      exact WfRewriter.setAttributes_valueInBounds_iff.mpr
        (WfRewriter.createOp_valueInBounds_mono hctx' hv)) hn
    let resultValues : Array ValuePtr := Array.ofFn fun i : Fin outputTypes.size => op.getResult i
    let next := contextState.addRealValues resultValues
      (by
        intro value hv
        rcases Array.mem_ofFn.mp hv with ⟨i, rfl⟩
        have hResult := WfRewriter.createOp_result_inBounds hctx' i.val i.isLt
        exact WfRewriter.setAttributes_valueInBounds_iff.mpr (by simpa using hResult))
      (by
        intro value hv name fwd hf index oldOp loc hp
        rcases Array.mem_ofFn.mp hv with ⟨i, rfl⟩
        have hOld := state.forwardInBounds name fwd hf index oldOp loc hp
        have hDifferent := WfRewriter.createOp_existingValue_not_result hctx' hOld
        simpa using Ne.symm hDifferent)
    let mut current : { state : MlirParserState OpInfo // state.realValues = next.realValues ∧
        StructuralBoundsPreserved next.ctx.raw state.ctx.raw } := ⟨next, rfl, .refl _⟩
    for group in boundResultGroups results do
      let values : Array ValuePtr := Array.ofFn fun i : Fin group.count => op.getResult (group.offset + i.val)
      let hValues : ∀ value ∈ values, current.val.realValues value := by
        intro value hv
        rw [current.property.1]
        apply Or.inr
        rcases Array.mem_ofFn.mp hv with ⟨i, rfl⟩
        apply Array.mem_ofFn.mpr
        exact ⟨⟨group.offset + i.val, by
          have := group.inBounds
          have := i.isLt
          omega⟩, rfl⟩
      let registered ← registerValueDefsState current.val group.name group.pos values hValues
      current := ⟨registered.val, registered.property.1.trans current.property.1,
        current.property.2.trans registered.property.2⟩
    let final := { current.val with opLocations := current.val.opLocations.insert op opStart }
    return ⟨some op, final, trivial, hs.trans (hn.trans (by
      simpa [next, contextState, MlirParserState.addRealValues, MlirParserState.withContext] using current.property.2))⟩

private partial def parseBlockBodyState (initial s : MlirParserState OpInfo) (block : BlockPtr)
    (hb : block.InBounds s.ctx.raw) (hs : StructuralBoundsPreserved initial.ctx.raw s.ctx.raw) :
    EStateM ParserError ParserState (ParsedBlock initial) := do
  let parsed ← parseOptionalOpState s (some block) (by simpa using hb)
  let hb := parsed.preserves.blocks block hb
  let hs := hs.trans parsed.preserves
  match parsed.value with
  | none => return ⟨block, parsed.state, hb, hs⟩
  | some _ => parseBlockBodyState initial parsed.state block hb hs

private partial def parseEntryBlockState (s : MlirParserState OpInfo)
    (ip : BlockInsertPoint) (hip : ip.InBounds s.ctx.raw) :
    EStateM ParserError ParserState (ParsedBlock s) := do
  let block ← parseEntryBlockLabelState s ip hip
  parseBlockBodyState s block.state block.value block.inBounds block.preserves

private partial def parseOptionalBlockState (s : MlirParserState OpInfo)
    (ip : BlockInsertPoint) (hip : ip.InBounds s.ctx.raw) :
    EStateM ParserError ParserState (ParsedOptionalBlock s) := do
  let block ← parseOptionalBlockLabelState s ip hip
  match he : block.value with
  | none => return block
  | some b =>
    let body ← parseBlockBodyState s block.state b (by simpa [he] using block.inBounds) block.preserves
    return ⟨some body.value, body.state, (by simpa using body.inBounds), body.preserves⟩

private partial def parseRegionBlocksState (initial s : MlirParserState OpInfo)
    (region : RegionPtr) (hr : region.InBounds s.ctx.raw)
    (hs : StructuralBoundsPreserved initial.ctx.raw s.ctx.raw) :
    EStateM ParserError ParserState (ParsedRegion initial) := do
  let parsed ← parseOptionalBlockState s (BlockInsertPoint.atEnd region) (by simpa only [BlockInsertPoint.inBounds_atEnd] using hr)
  let hr := parsed.preserves.regions region hr
  let hs := hs.trans parsed.preserves
  match parsed.value with
  | none => return ⟨region, parsed.state, hr, hs⟩
  | some _ => parseRegionBlocksState initial parsed.state region hr hs

private partial def parseRegionState (initial : MlirParserState OpInfo) :
    EStateM ParserError ParserState (ParsedRegion initial) := do
  let oldBlocks := initial.blocks
  let state : MlirParserState OpInfo := { initial with
    definitionsPerScope := initial.definitionsPerScope.push (.emptyWithCapacity 128)
    blocks := Std.HashMap.emptyWithCapacity 1
    blocksInBounds := by simp }
  readSyntax state (parsePunctuation "{")
  match hc : WfRewriter.createRegion state.ctx with
  | none => throwAtCurrentPos "internal error: failed to create region"
  | some (ctx, region) =>
    let hs := WfRewriter.createRegion_structuralBoundsPreserved hc
    let next := state.withContext ctx (fun _ h => WfRewriter.createRegion_valueInBounds_mono hc h) hs
    let hr := WfRewriter.createRegion_new_inBounds hc
    let parsed ← if ← readSyntax next (parseOptionalPunctuation "}") then
      pure (⟨region, next, hr, hs⟩ : ParsedRegion initial)
    else do
      let entry ← parseEntryBlockState next (BlockInsertPoint.atEnd region) (by simpa only [BlockInsertPoint.inBounds_atEnd, next, MlirParserState.withContext] using hr)
      let body ← parseRegionBlocksState initial entry.state region
        (entry.preserves.regions region hr) (hs.trans entry.preserves)
      readSyntax body.state (parsePunctuation "}")
      for (blockName, blockEntry) in body.state.blocks do
        if let .ForwardDeclared _ forwardLoc := blockEntry then
          throwAt forwardLoc s!"block %{String.fromUTF8! blockName} was used but never defined"
      pure body
    let values := scopeValues parsed.state
    let final : MlirParserState OpInfo := { parsed.state with
      values := values.val
      valuesReal := values.property
      definitionsPerScope := parsed.state.definitionsPerScope.pop
      blocks := oldBlocks
      blocksInBounds := fun name entry he =>
        parsed.preserves.blocks entry.block (initial.blocksInBounds name entry he) }
    return ⟨parsed.value, final, parsed.inBounds, parsed.preserves⟩

end

private def parseOp : MlirParserM OpInfo OperationPtr :=
  modifyParserStateM' fun state => do
    let parsed ← parseOptionalOpState state none Option.maybe_none
    let some op := parsed.value | throwAtCurrentPos "operation expected"
    return (op, parsed.state)


/-- Check that all SSA values forward referenced while parsing were eventually defined. -/
def checkNoUnresolvedForwardValues : MlirParserM OpInfo Unit := do
  for (valueName, fwd) in (← get).forwardValues do
    throwAt fwd.loc s!"use of undefined value %{String.fromUTF8! valueName}"

/--
  Parse the `!name = type` alias definitions preceding the top-level operation. As in MLIR, a
  definition may use earlier aliases, a name may not be redefined, and names containing a `.` are
  reserved for dialect types.
-/
def parseTypeAliasDefs : MlirParserM OpInfo Unit := do
  repeat
    let startPos ← getPos
    let some name ← parseOptionalPrefixedKeyword .exclamationIdent | break
    if (← get).typeAliases.contains name then
      throwAt startPos s!"redefinition of type alias id '{String.fromUTF8! name}'"
    if name.toList.contains '.'.toUInt8 then
      throwAt startPos "type names with a '.' are reserved for dialect-defined names"
    parsePunctuation "=" "expected '=' in type alias definition"
    let type ← parseType
    modify fun state => { state with typeAliases := state.typeAliases.insert name type }

/--
  Parse the top-level alias definitions and operation, and report unresolved forward references.
-/
partial def parseTopLevelOp : MlirParserM OpInfo OperationPtr := do
  parseTypeAliasDefs
  let op ← parseOp
  checkNoUnresolvedForwardValues
  return op

end Veir.Parser
