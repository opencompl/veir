module

public import Veir.Parser.State
public import Veir.Parser.StaticIR

/-!
Pointer invariants independent of the runtime allocation registry. In particular, removing a
forward-reference name transfers ownership to the resolver's locals; it does not justify
assuming that those locals, or other table entries, survive deletion. The deletion frame
below proves precisely which references survive.
-/
@[expose] public section
namespace Veir.Parser

/-- The parser's byte-string names use structural byte-array equality. -/
instance : LawfulBEq ByteArray where
  eq_of_beq := by
    intro a b h
    change (a.data == b.data) = true at h
    exact congrArg ByteArray.mk (eq_of_beq h)
  rfl := by
    intro a
    change (a.data == a.data) = true
    exact BEq.rfl

namespace MlirParserData

def DefinedValue (d : MlirParserData) (v : IR.Value) : Prop :=
  ∃ (name : ByteArray) (values : Array IR.Value) (loc : Location),
    d.values[name]? = some (values, loc) ∧ v ∈ values

def ForwardEntry (d : MlirParserData) (name : ByteArray) (index : Nat) (op : IR.Op) (loc : Location) : Prop :=
  ∃ fwd, d.forwardValues[name]? = some fwd ∧ fwd.placeholders[index]? = some (op, loc)

def blockEntry? (d : MlirParserData) (scope : Nat) (name : ByteArray) : Option BlockEntry :=
  match scope with
  | 0 => d.blocks[name]?
  | i + 1 => d.blockScopes[i]? >>= (·[name]?)

/-- This witness is used only in proofs. The runtime result pointer is still obtained with
`getResultPtr`, without performing a lookup or checking the pointer's address. -/
def FirstResultLive (ctx : IR.RawContext) (op : IR.Op) : Prop :=
  ∃ v : IR.Value, v.InBounds ctx ∧ v.spec = .opResult ⟨op.spec, 0⟩

structure Live (d : MlirParserData) (ctx : IR.RawContext) : Prop where
  values : ∀ v, d.DefinedValue v → v.InBounds ctx
  blocks : ∀ scope name entry, d.blockEntry? scope name = some entry → entry.block.InBounds ctx
  forward : ∀ name index op loc, d.ForwardEntry name index op loc → op.InBounds ctx ∧ FirstResultLive ctx op
  unique : ∀ n i op loc n' i' op' loc',
    d.ForwardEntry n i op loc → d.ForwardEntry n' i' op' loc' → op.spec = op'.spec → n = n' ∧ i = i'
  privateValues : ∀ v, d.DefinedValue v → ∀ n i op loc,
    d.ForwardEntry n i op loc → ∀ res, v.spec = .opResult res → res.op ≠ op.spec
  uniqueBlocks : ∀ scope name block loc,
    d.blockEntry? scope name = some (.ForwardDeclared block loc) →
    ∀ scope' name' entry, d.blockEntry? scope' name' = some entry →
    block.spec = entry.block.spec → scope = scope' ∧ name = name'

/-- Non-reference bookkeeping (aliases, definition scopes, source locations) does not
change pointer validity. -/
theorem Live.sameReferences {d next : MlirParserData} {ctx : IR.RawContext} (h : d.Live ctx)
    (hv : next.values = d.values) (hf : next.forwardValues = d.forwardValues)
    (hb : next.blocks = d.blocks) (hs : next.blockScopes = d.blockScopes) : next.Live ctx := by
  have hvalues : ∀ v, next.DefinedValue v ↔ d.DefinedValue v := by
    intro v; simp only [DefinedValue, hv]
  have hforward : ∀ n i op l, next.ForwardEntry n i op l ↔ d.ForwardEntry n i op l := by
    intros; simp only [ForwardEntry, hf]
  have hblocks : ∀ s n, next.blockEntry? s n = d.blockEntry? s n := by
    intro s n; cases s <;> simp only [blockEntry?, hb, hs]
  constructor
  · intro v he; exact h.values v ((hvalues v).mp he)
  · intro s n e he; rw [hblocks] at he; exact h.blocks s n e he
  · intro n i op l he; exact h.forward n i op l ((hforward n i op l).mp he)
  · intros; apply h.unique <;> (first | assumption | (apply (hforward ..).mp; assumption))
  · intro v he n i op l he'
    exact h.privateValues v ((hvalues v).mp he) n i op l ((hforward n i op l).mp he')
  · intro s n b l he s' n' e he' heq
    rw [hblocks] at he he'
    exact h.uniqueBlocks s n b l he s' n' e he' heq

theorem FirstResultLive.mono {a b : IR.RawContext} {op : IR.Op}
    (h : FirstResultLive a op) (frame : StaticIR.Preserves a b) : FirstResultLive b op := by
  obtain ⟨v, hv, hs⟩ := h
  exact ⟨v, frame.value hv, hs⟩

theorem FirstResultLive.inBounds {ctx : IR.RawContext} {op : IR.Op}
    (h : FirstResultLive ctx op) (hop : op.InBounds ctx) :
    (Sim.ValuePtr.fromOpResultPtr (op.getResultPtr ctx 0 hop)).InBounds ctx := by
  obtain ⟨v, hv, hs⟩ := h
  have hvib := hv.ib
  have hi : 0 < op.spec.getNumResults! ctx.spec := by
    rw [hs] at hvib
    have hr : (OpResultPtr.mk op.spec 0).InBounds ctx.spec := by
      simpa only [ValuePtr.inBounds_opResult] using hvib
    grind [OpResultPtr.inBounds_def]
  grind [generic_ptr_grind]

theorem Live.mono {d : MlirParserData} {a b : IR.RawContext} (h : d.Live a)
    (frame : StaticIR.Preserves a b) : d.Live b where
  values v hv := frame.value (h.values v hv)
  blocks s n e he := frame.block (h.blocks s n e he)
  forward n i op l he := ⟨frame.operation (h.forward n i op l he).1,
    (h.forward n i op l he).2.mono frame⟩
  unique := h.unique
  privateValues := h.privateValues
  uniqueBlocks := h.uniqueBlocks

/-- Remove the whole name once, before consuming its privately owned placeholders. -/
def takeForwardName (d : MlirParserData) (name : ByteArray) : MlirParserData :=
  { d with forwardValues := d.forwardValues.erase name }

@[simp]
theorem forwardEntry_takeForwardName {d : MlirParserData} {name n i op loc} :
    (d.takeForwardName name).ForwardEntry n i op loc ↔ name ≠ n ∧ d.ForwardEntry n i op loc := by
  simp only [ForwardEntry, takeForwardName, Std.HashMap.getElem?_erase]
  split <;> simp_all

@[simp]
theorem definedValue_takeForwardName {d : MlirParserData} {name v} :
    (d.takeForwardName name).DefinedValue v ↔ d.DefinedValue v := Iff.rfl

@[simp]
theorem blockEntry_takeForwardName {d : MlirParserData} {name scope n} :
    (d.takeForwardName name).blockEntry? scope n = d.blockEntry? scope n := rfl

theorem Live.takeForwardName {d : MlirParserData} {ctx : IR.RawContext} (h : d.Live ctx)
    (name : ByteArray) : (d.takeForwardName name).Live ctx where
  values := h.values
  blocks := h.blocks
  forward n i op l he := h.forward n i op l (forwardEntry_takeForwardName.mp he).2
  unique n i op l n' i' op' l' he he' hs := h.unique n i op l n' i' op' l'
    (forwardEntry_takeForwardName.mp he).2 (forwardEntry_takeForwardName.mp he').2 hs
  privateValues v hv n i op l he := h.privateValues v hv n i op l (forwardEntry_takeForwardName.mp he).2
  uniqueBlocks := h.uniqueBlocks

/-- No surviving table reference may target a reclaimed operation. Caller-local references
have a separate obligation, discharged using `OpDeletion.values`/`operations`. -/
structure CanDeleteOp (d : MlirParserData) (dead : IR.Op) : Prop where
  values : ∀ v, d.DefinedValue v → ∀ res, v.spec = .opResult res → res.op ≠ dead.spec
  forward : ∀ n i op loc, d.ForwardEntry n i op loc → op.spec ≠ dead.spec

theorem Live.takeForwardName_canDelete {d : MlirParserData} {ctx : IR.RawContext}
    (h : d.Live ctx) {name index dead loc} (he : d.ForwardEntry name index dead loc) :
    (d.takeForwardName name).CanDeleteOp dead where
  values v hv := h.privateValues v hv name index dead loc he
  forward n i op l he' := by
    obtain ⟨hne, he'⟩ := forwardEntry_takeForwardName.mp he'
    intro hs
    exact hne ((h.unique name index dead loc n i op l he he' hs.symm).1)

theorem Live.eraseOp {d : MlirParserData} {ctx : IR.RawContext} {dead : IR.Op}
    (h : d.Live ctx) (safe : d.CanDeleteOp dead) (deleted : StaticIR.OpDeletion ctx dead) :
    d.Live deleted.ctx.raw where
  values v hv := deleted.values v (h.values v hv) (safe.values v hv)
  blocks s n e he := deleted.blocks e.block (h.blocks s n e he)
  forward n i op l he := by
    obtain ⟨hop, v, hv, hs⟩ := h.forward n i op l he
    have hn := safe.forward n i op l he
    refine ⟨deleted.operations op hop hn, v, deleted.values v hv ?_, hs⟩
    intro res hr
    grind
  unique := h.unique
  privateValues := h.privateValues
  uniqueBlocks := h.uniqueBlocks

def putValues (d : MlirParserData) (name : ByteArray) (values : Array IR.Value) (loc : Location) : MlirParserData :=
  { d with values := d.values.insert name (values, loc) }

theorem definedValue_putValues {d : MlirParserData} {name values loc v}
    (he : (d.putValues name values loc).DefinedValue v) : v ∈ values ∨ d.DefinedValue v := by
  obtain ⟨n, vs, l, he, hm⟩ := he
  by_cases hn : name = n
  · simp [putValues, hn] at he
    obtain ⟨rfl, rfl⟩ := he
    exact Or.inl hm
  · right
    refine ⟨n, vs, l, ?_, hm⟩
    simpa [putValues, Std.HashMap.getElem?_insert, hn] using he

theorem Live.putValues {d : MlirParserData} {ctx : IR.RawContext} (h : d.Live ctx)
    (name : ByteArray) (values : Array IR.Value) (loc : Location)
    (hi : ∀ v, v ∈ values → v.InBounds ctx)
    (hp : ∀ v, v ∈ values → ∀ n i op l, d.ForwardEntry n i op l →
      ∀ res, v.spec = .opResult res → res.op ≠ op.spec) :
    (d.putValues name values loc).Live ctx where
  values v he := (definedValue_putValues he).elim (hi v) (h.values v)
  blocks := h.blocks
  forward := h.forward
  unique := h.unique
  privateValues v he := (definedValue_putValues he).elim (hp v) (h.privateValues v)
  uniqueBlocks := h.uniqueBlocks

def forgetValueName (d : MlirParserData) (name : ByteArray) : MlirParserData :=
  { d with values := d.values.erase name }

theorem definedValue_forgetValueName {d : MlirParserData} {name v}
    (he : (d.forgetValueName name).DefinedValue v) : d.DefinedValue v := by
  obtain ⟨n, vs, l, he, hm⟩ := he
  change (d.values.erase name)[n]? = some (vs, l) at he
  simp only [Std.HashMap.getElem?_erase] at he
  split at he
  · contradiction
  · exact ⟨n, vs, l, he, hm⟩

theorem Live.forgetValueName {d : MlirParserData} {ctx : IR.RawContext} (h : d.Live ctx)
    (name : ByteArray) : (d.forgetValueName name).Live ctx where
  values v he := h.values v (definedValue_forgetValueName he)
  blocks := h.blocks
  forward := h.forward
  unique := h.unique
  privateValues v he := h.privateValues v (definedValue_forgetValueName he)
  uniqueBlocks := h.uniqueBlocks

def putBlock (d : MlirParserData) (name : ByteArray) (entry : BlockEntry) : MlirParserData :=
  { d with blocks := d.blocks.insert name entry }

@[simp]
theorem blockEntry_putBlock {d : MlirParserData} {name newEntry scope n entry} :
    (d.putBlock name newEntry).blockEntry? scope n = some entry ↔
      (scope = 0 ∧ n = name ∧ entry = newEntry) ∨
      ((scope ≠ 0 ∨ n ≠ name) ∧ d.blockEntry? scope n = some entry) := by
  cases scope <;> by_cases hn : name = n <;>
    simp_all [putBlock, blockEntry?, Std.HashMap.getElem?_insert] <;> grind only

theorem Live.putFreshBlock {d : MlirParserData} {ctx : IR.RawContext} (h : d.Live ctx)
    (name : ByteArray) (entry : BlockEntry) (hi : entry.block.InBounds ctx)
    (fresh : ∀ s n e, d.blockEntry? s n = some e → entry.block.spec ≠ e.block.spec) :
    (d.putBlock name entry).Live ctx := by
  constructor
  · exact h.values
  · intro s n e he
    rcases blockEntry_putBlock.mp he with ⟨rfl, rfl, rfl⟩ | ⟨_, he⟩
    · exact hi
    · exact h.blocks s n e he
  · exact h.forward
  · exact h.unique
  · exact h.privateValues
  · intro s n b l he s' n' e he' hs
    rw [blockEntry_putBlock (d := d)] at he he'
    rcases he with ⟨rfl, rfl, he⟩ | ⟨_, he⟩
    · subst entry
      rcases he' with ⟨rfl, rfl, _⟩ | ⟨_, he'⟩
      · exact ⟨rfl, rfl⟩
      · exact False.elim (fresh s' n' e he' (by simpa only [BlockEntry.block] using hs))
    · rcases he' with ⟨rfl, rfl, rfl⟩ | ⟨_, he'⟩
      · exact False.elim (fresh s n (.ForwardDeclared b l) he (by simpa only [BlockEntry.block] using hs.symm))
      · exact h.uniqueBlocks s n b l he s' n' e he' hs

def takeBlockName (d : MlirParserData) (name : ByteArray) : MlirParserData :=
  { d with blocks := d.blocks.erase name }

@[simp]
theorem blockEntry_takeBlockName {d : MlirParserData} {name scope n entry} :
    (d.takeBlockName name).blockEntry? scope n = some entry ↔
      (scope ≠ 0 ∨ name ≠ n) ∧ d.blockEntry? scope n = some entry := by
  cases scope <;> by_cases hn : name = n <;>
    simp_all [takeBlockName, blockEntry?, Std.HashMap.getElem?_erase]

theorem Live.takeBlockName {d : MlirParserData} {ctx : IR.RawContext} (h : d.Live ctx)
    (name : ByteArray) : (d.takeBlockName name).Live ctx where
  values := h.values
  blocks s n e he := h.blocks s n e (blockEntry_takeBlockName.mp he).2
  forward := h.forward
  unique := h.unique
  privateValues := h.privateValues
  uniqueBlocks s n b l he s' n' e he' hs := h.uniqueBlocks s n b l
    (blockEntry_takeBlockName.mp he).2 s' n' e (blockEntry_takeBlockName.mp he').2 hs

def CanDeleteBlock (d : MlirParserData) (dead : IR.Block) : Prop :=
  ∀ scope name entry, d.blockEntry? scope name = some entry → entry.block.spec ≠ dead.spec

/-- Exclusive ownership prevents an outer/suspended table from naming a block being deleted
in the current scope. This is proved from the name-table invariant, not checked by address. -/
theorem Live.takeBlockName_canDelete {d : MlirParserData} {ctx : IR.RawContext}
    (h : d.Live ctx) {name dead loc}
    (he : d.blockEntry? 0 name = some (.ForwardDeclared dead loc)) :
    (d.takeBlockName name).CanDeleteBlock dead := by
  intro scope n entry hentry hs
  obtain ⟨hne, hentry⟩ := blockEntry_takeBlockName.mp hentry
  obtain ⟨hscope, hname⟩ := h.uniqueBlocks 0 name dead loc he scope n entry hentry hs.symm
  grind only

theorem Live.eraseBlock {d : MlirParserData} {ctx : IR.RawContext} {dead : IR.Block}
    (h : d.Live ctx) (safe : d.CanDeleteBlock dead) (deleted : StaticIR.BlockDeletion ctx dead) :
    d.Live deleted.ctx.raw where
  values v hv := deleted.values v (h.values v hv)
  blocks s n e he := deleted.blocks e.block (h.blocks s n e he) (safe s n e he)
  forward n i op l he := by
    obtain ⟨hop, v, hv, hs⟩ := h.forward n i op l he
    exact ⟨deleted.operations op hop, v, deleted.values v hv, hs⟩
  unique := h.unique
  privateValues := h.privateValues
  uniqueBlocks := h.uniqueBlocks

def enterBlockScope (d : MlirParserData) : MlirParserData :=
  { d with blocks := .emptyWithCapacity 1, blockScopes := d.blockScopes.push d.blocks }

private def outerScope (d : MlirParserData) (i : Nat) : Nat :=
  if i = d.blockScopes.size then 0 else i + 1

private theorem outerScope_injective (d : MlirParserData) : Function.Injective (outerScope d) := by
  intro i j h
  by_cases hi : i = d.blockScopes.size <;> by_cases hj : j = d.blockScopes.size <;>
    simp_all [outerScope] <;> omega

private theorem blockEntry_enter_zero (d : MlirParserData) (n : ByteArray) :
    d.enterBlockScope.blockEntry? 0 n = none := by simp [enterBlockScope, blockEntry?]

private theorem blockEntry_enter_succ (d : MlirParserData) (i : Nat) (n : ByteArray) :
    d.enterBlockScope.blockEntry? (i + 1) n = d.blockEntry? (outerScope d i) n := by
  by_cases hi : i = d.blockScopes.size <;>
    simp [enterBlockScope, blockEntry?, outerScope, Array.getElem?_push, hi]

theorem blockEntry_enter_origin {d : MlirParserData} {scope name entry}
    (he : d.enterBlockScope.blockEntry? scope name = some entry) :
    ∃ oldScope, d.blockEntry? oldScope name = some entry := by
  cases scope with
  | zero => simp [blockEntry_enter_zero] at he
  | succ i => exact ⟨outerScope d i, by rwa [blockEntry_enter_succ] at he⟩

/-- Entering a nested region keeps the outer block references live and exclusively owned. -/
theorem Live.enterBlockScope {d : MlirParserData} {ctx : IR.RawContext} (h : d.Live ctx) :
    d.enterBlockScope.Live ctx := by
  constructor
  · exact h.values
  · intro scope n entry he
    cases scope with
    | zero => simp [blockEntry_enter_zero] at he
    | succ i => rw [blockEntry_enter_succ] at he; exact h.blocks _ n entry he
  · exact h.forward
  · exact h.unique
  · exact h.privateValues
  · intro scope n block loc he scope' n' entry he' hs
    cases scope with
    | zero => simp [blockEntry_enter_zero] at he
    | succ i =>
      cases scope' with
      | zero => simp [blockEntry_enter_zero] at he'
      | succ j =>
        rw [blockEntry_enter_succ] at he he'
        obtain ⟨hij, hn⟩ := h.uniqueBlocks _ n block loc he _ n' entry he' hs
        exact ⟨congrArg Nat.succ (outerScope_injective d hij), hn⟩

private def restoreScope (n scope : Nat) : Nat :=
  if scope = 0 then n + 1 else if scope ≤ n then scope else scope + 1

private theorem restoreScope_injective (n : Nat) : Function.Injective (restoreScope n) := by
  intro i j h
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
    by_cases hni : i ≤ n <;> by_cases hnj : j ≤ n <;>
    simp_all [restoreScope] <;> omega

private theorem blockEntry_restore {d : MlirParserData} {outer : BlockTable} {saved : Array BlockTable}
    (hs : d.blockScopes = saved.push outer) (scope : Nat) (name : ByteArray) :
    ({ d with blocks := outer, blockScopes := saved } : MlirParserData).blockEntry? scope name =
      d.blockEntry? (restoreScope saved.size scope) name := by
  cases scope with
  | zero => simp [blockEntry?, restoreScope, hs]
  | succ i =>
    by_cases hi : i < saved.size
    · have hle : i + 1 ≤ saved.size := by omega
      have hne : i ≠ saved.size := by omega
      simp [blockEntry?, restoreScope, hs, hle, Array.getElem?_push, hne]
    · have hle : ¬ i + 1 ≤ saved.size := by omega
      have hget : saved[i]? = none := by simp; omega
      have hget' : (saved.push outer)[i + 1]? = none := by simp; omega
      simp [blockEntry?, restoreScope, hs, hle, hget, hget']

theorem blockEntry_restore_origin {d : MlirParserData} {outer : BlockTable} {saved : Array BlockTable}
    (hs : d.blockScopes = saved.push outer) {scope name entry}
    (he : ({ d with blocks := outer, blockScopes := saved } : MlirParserData).blockEntry? scope name = some entry) :
    ∃ oldScope, d.blockEntry? oldScope name = some entry :=
  ⟨restoreScope saved.size scope, by rwa [blockEntry_restore hs] at he⟩

/-- Restoring an outer scope is a restriction/reindexing of the live scope entries. It
preserves ownership even when inner and outer scopes contain identical textual names. -/
theorem Live.restoreBlockScope {d : MlirParserData} {ctx : IR.RawContext}
    (h : d.Live ctx) {outer : BlockTable} {saved : Array BlockTable}
    (hs : d.blockScopes = saved.push outer) :
    ({ d with blocks := outer, blockScopes := saved } : MlirParserData).Live ctx := by
  constructor
  · exact h.values
  · intro scope n e he
    rw [blockEntry_restore hs] at he
    exact h.blocks _ n e he
  · exact h.forward
  · exact h.unique
  · exact h.privateValues
  · intro scope n b l he scope' n' e he' hb
    rw [blockEntry_restore hs] at he he'
    obtain ⟨hi, hn⟩ := h.uniqueBlocks _ n b l he _ n' e he' hb
    exact ⟨restoreScope_injective saved.size hi, hn⟩

def leaveBlockScope? (d : MlirParserData) : Option MlirParserData :=
  match d.blockScopes.back? with
  | none => none
  | some outer => some { d with blocks := outer, blockScopes := d.blockScopes.pop }

theorem Live.leaveBlockScope {d next : MlirParserData} {ctx : IR.RawContext} (h : d.Live ctx)
    (he : d.leaveBlockScope? = some next) : next.Live ctx := by
  simp only [leaveBlockScope?] at he
  split at he
  · contradiction
  · rename_i outer hback
    cases he
    obtain ⟨saved, hs⟩ := Array.back?_eq_some_iff.mp hback
    simpa only [hs, Array.pop_push] using h.restoreBlockScope hs

/-- Ordinary SSA lookup supplies the proof from the table invariant. No second, address-keyed
lookup is performed. -/
def liveValue? (d : MlirParserData) (ctx : IR.RawContext) (live : d.Live ctx)
    (name : ByteArray) (index : Nat) : Option { v : IR.Value // d.DefinedValue v ∧ v.InBounds ctx } :=
  match hn : d.values[name]? with
  | none => none
  | some (values, loc) =>
    match hv : values[index]? with
    | none => none
    | some v =>
      have he : d.DefinedValue v := ⟨name, values, loc, hn, by grind⟩
      some ⟨v, he, live.values v he⟩

def liveBlock? (d : MlirParserData) (ctx : IR.RawContext) (live : d.Live ctx)
    (name : ByteArray) : Option { entry : BlockEntry //
      d.blockEntry? 0 name = some entry ∧ entry.block.InBounds ctx } :=
  match he : d.blocks[name]? with
  | none => none
  | some entry => some ⟨entry, he, live.blocks 0 name entry he⟩

end MlirParserData

/-- Only the ordinary parser data and IR buffer remain at runtime. -/
structure StaticParserState where
  data : MlirParserData
  ctx : StaticIR.Context
  live : data.Live ctx.raw

def staticInitialData (allow : Bool) : MlirParserData :=
  { values := .emptyWithCapacity 128, definitionsPerScope := #[.emptyWithCapacity 2],
    forwardValues := .emptyWithCapacity 1, blocks := .emptyWithCapacity 1,
    allowUnregisteredDialect := allow }

theorem staticInitialData_live (allow : Bool) (ctx : IR.RawContext) :
    (staticInitialData allow).Live ctx := by
  have hb : ∀ scope name, (staticInitialData allow).blockEntry? scope name = none := by
    intro scope name
    cases scope <;> simp [staticInitialData, MlirParserData.blockEntry?]
  simp only [staticInitialData] at hb
  constructor
  all_goals simp [MlirParserData.DefinedValue, MlirParserData.ForwardEntry, staticInitialData, hb]

def StaticParserState.initial (allowUnregisteredDialect := false) : StaticParserState :=
  ⟨staticInitialData allowUnregisteredDialect, StaticIR.empty, staticInitialData_live _ _⟩

/-- Consume the state wrapper before touching the buffer; only context-free name tables
are retained across a transaction. -/
@[noinline, nospecialize]
def StaticParserState.withParts {α : MlirParserData → StaticIR.Context → Type}
    (s : StaticParserState)
    (f : (data : MlirParserData) → (ctx : StaticIR.Context) → data.Live ctx.raw → α data ctx) :
    α s.data s.ctx :=
  f s.data s.ctx s.live

/-- The certificate includes caller-local liveness and preservation of the previously
published block bindings; the latter lets an operand-array loop retain earlier results. -/
structure ResolvedBlockUse (beforeData : MlirParserData) (before : IR.RawContext) (name : ByteArray) where
  state : StaticParserState
  block : IR.Block
  inBounds : block.InBounds state.ctx.raw
  named : ∃ entry, state.data.blockEntry? 0 name = some entry ∧ entry.block = block
  preserves : StaticIR.Preserves before state.ctx.raw
  bindings : ∀ scope n entry, beforeData.blockEntry? scope n = some entry →
    state.data.blockEntry? scope n = some entry
  suspended : state.data.blockScopes = beforeData.blockScopes
  forwardValues : state.data.forwardValues = beforeData.forwardValues
  origins : ∀ scope n p l, state.data.blockEntry? scope n = some (.ForwardDeclared p l) →
    beforeData.blockEntry? scope n = some (.ForwardDeclared p l) ∨ ¬ p.spec.InBounds before.spec

/-- Resolve a successor using the normal name table. A newly encountered name allocates a
placeholder; existing pointers obtain their proof directly from the table invariant. -/
def StaticParserState.useBlock (s : StaticParserState) (name : ByteArray) (loc : Location) :
    Option (ResolvedBlockUse s.data s.ctx.raw name) :=
  s.withParts (α := fun data ctx => Option (ResolvedBlockUse data ctx.raw name)) fun data ctx live =>
    match he : data.blocks[name]? with
    | some entry => some ⟨⟨data, ctx, live⟩, entry.block, live.blocks 0 name entry he,
        ⟨entry, he, rfl⟩, StaticIR.Preserves.refl ctx.raw, fun _ _ _ h => h, rfl, rfl,
        fun _ _ _ _ h => Or.inl h⟩
    | none => do
      let created ← StaticIR.createBlock ctx #[] none (by simp) (by simp)
      let entry := BlockEntry.ForwardDeclared created.pointer loc
      let next := data.putBlock name entry
      have hfresh : ∀ scope n e, data.blockEntry? scope n = some e → entry.block.spec ≠ e.block.spec := by
        intro scope n e hlookup hs
        apply created.fresh
        rw [show created.pointer.spec = e.block.spec from hs]
        exact (live.blocks scope n e hlookup).ib
      have hlive := (live.mono created.preserves).putFreshBlock name entry created.inBounds hfresh
      return ⟨⟨next, created.ctx, hlive⟩, created.pointer, created.inBounds,
        ⟨entry, by simp [next, MlirParserData.blockEntry?, MlirParserData.putBlock], rfl⟩,
        created.preserves, by
          intro scope n e hlookup
          apply MlirParserData.blockEntry_putBlock.mpr
          right
          refine ⟨?_, hlookup⟩
          by_cases hs : scope = 0
          · subst scope
            right
            intro hn
            subst n
            change data.blocks[name]? = some e at hlookup
            rw [he] at hlookup
            contradiction
          · exact Or.inl hs,
        rfl, rfl, by
          intro scope n p l hlookup
          change (data.putBlock name entry).blockEntry? scope n = some (.ForwardDeclared p l) at hlookup
          rw [MlirParserData.blockEntry_putBlock] at hlookup
          rcases hlookup with ⟨rfl, rfl, hnew⟩ | ⟨_, hprevious⟩
          · have hp : p = created.pointer := by
              simpa only [entry, BlockEntry.block] using congrArg BlockEntry.block hnew
            rw [hp]
            exact Or.inr created.fresh
          · exact Or.inl hprevious⟩

/-- Rewire a locally owned placeholder. Bounds are taken from erased certificates, not from
an address lookup. The returned deletion frame also protects locals in the calling resolver. -/
def StaticParserState.rewirePlaceholder (s : StaticParserState) (op : IR.Op) (target : IR.Value) :
    op.InBounds s.ctx.raw → MlirParserData.FirstResultLive s.ctx.raw op →
    target.InBounds s.ctx.raw → s.data.CanDeleteOp op →
    Option { result : StaticParserState // result.data = s.data ∧ StaticIR.OpFrame s.ctx.raw result.ctx.raw op } :=
  s.withParts (α := fun data ctx => op.InBounds ctx.raw → MlirParserData.FirstResultLive ctx.raw op →
    target.InBounds ctx.raw → data.CanDeleteOp op →
    Option { result : StaticParserState // result.data = data ∧ StaticIR.OpFrame ctx.raw result.ctx.raw op })
    fun data ctx live hop hresult htarget safe => do
      let old := Sim.ValuePtr.fromOpResultPtr (op.getResultPtr ctx.raw 0 hop)
      let changed ← StaticIR.replaceValue ctx old target (hresult.inBounds hop) htarget
      let deleted ← StaticIR.eraseOp changed.ctx op (changed.preserves.operation hop)
      let frame : StaticIR.OpDeletion ctx.raw op :=
        ⟨deleted.ctx,
          fun p hp hn => deleted.operations p (changed.preserves.operation hp) hn,
          fun p hp => deleted.blocks p (changed.preserves.block hp),
          fun p hp => deleted.regions p (changed.preserves.region hp),
          fun p hp hn => deleted.values p (changed.preserves.value hp) hn⟩
      return ⟨⟨data, deleted.ctx, live.eraseOp safe frame⟩, rfl, frame.frame⟩

end Veir.Parser
