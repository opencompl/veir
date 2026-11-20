module

public import Veir.PatternRewriter.Puddle.CTreeValidityLemmas
public import Veir.PatternRewriter.Puddle.SemanticAssignmentLemmas
public import Veir.PatternRewriter.Puddle.ExecutionLemmas
import all Veir.PatternRewriter.Puddle.Execution
import all Veir.PatternRewriter.Puddle.Validity
import all Veir.PatternRewriter.Puddle.CTreeValidityLemmas

namespace Veir.Puddle

public section

/-- A partially replayed matcher agrees with its concrete execution wherever it is bound. -/
def SemanticAssignment.AgreesWith (stage target : SemanticAssignment) : Prop :=
  ∀ id binding, stage id = some binding → target id = some binding

theorem SemanticAssignment.AgreesWith.empty (target : SemanticAssignment) :
    SemanticAssignment.empty.AgreesWith target := by
  intro id binding h
  simp [SemanticAssignment.empty] at h

theorem SemanticAssignment.AgreesWith.bind {stage target : SemanticAssignment}
    (h : stage.AgreesWith target) (id : Nat) (binding : SemanticBinding)
    (hbinding : target id = some binding) :
    (stage.bind id binding).AgreesWith target := by
  intro queried value hv
  by_cases heq : queried = id
  · subst queried
    simp only [SemanticAssignment.bind_same_eq, Option.some.injEq] at hv
    simpa [← hv] using hbinding
  · exact h queried value (by simpa [SemanticAssignment.bind, heq] using hv)

/-- The final assignment contains each listed result value. -/
inductive SemanticAssignment.ValuesBound (target : SemanticAssignment) :
    List (Handle OpCode .value) → List RuntimeValue → List TypeAttr → Prop
  | nil : ValuesBound target [] [] []
  | cons {handle value handles values type types}
      (head : target handle.id = some (.value value type))
      (tail : ValuesBound target handles values types) :
      ValuesBound target (handle :: handles) (value :: values) (type :: types)

/-- Bind fixed result values while maintaining agreement with a final execution. -/
theorem SemanticAssignment.bindsValues_of_target {stage target : SemanticAssignment}
    (h : stage.AgreesWith target) (handles : List (Handle OpCode .value))
    (values : List RuntimeValue) {types : List TypeAttr}
    (bound : SemanticAssignment.ValuesBound target handles values types) :
    ∃ final, stage.BindsValues handles values final types ∧ final.AgreesWith target := by
  induction bound generalizing stage with
  | nil => exact ⟨stage, .nil _, h⟩
  | @cons handle value handles values type types hb htail ih =>
    obtain ⟨final, hf, ha⟩ := ih (h.bind handle.id (.value value type) hb)
    exact ⟨final, .cons handle value type hf, ha⟩

/-- Successful fresh insertion establishes exactly the inserted kind. -/
theorem HandleContext.lookup_of_insertFresh {before after : HandleContext}
    {kind : HandleType OpCode} {handle : Handle OpCode kind}
    (h : before.insertFresh handle = some after) : after.lookup handle.id = some kind := by
  unfold HandleContext.insertFresh at h
  split at h
  · cases h
    simp [HandleContext.lookup, HandleContext.lookup.lookupBindings]
  · contradiction

/-- Inserting a fresh handle preserves the kinds already known to the static context. -/
theorem HandleContext.lookup_preserved_of_insertFresh {before after : HandleContext}
    {kind : HandleType OpCode} {handle : Handle OpCode kind} {id : Nat} {oldKind : HandleType OpCode}
    (h : before.insertFresh handle = some after) (hold : before.lookup id = some oldKind) :
    after.lookup id = some oldKind := by
  unfold HandleContext.insertFresh at h
  split at h
  · rename_i hnone
    cases h
    have hne : handle.id ≠ id := by
      intro heq
      subst id
      simp_all
    simp [HandleContext.lookup, HandleContext.lookup.lookupBindings, hne]
    exact hold
  · contradiction

/-- A fresh insertion leaves availability of every other handle unchanged. -/
theorem HandleContext.require_of_insertFresh_of_ne {before after : HandleContext}
    {kind queriedKind : HandleType OpCode} {handle : Handle OpCode kind}
    {queried : Handle OpCode queriedKind} (h : before.insertFresh handle = some after)
    (hne : queried.id ≠ handle.id) : after.require queried = before.require queried := by
  unfold HandleContext.insertFresh at h
  split at h
  · cases h
    simp [HandleContext.require, HandleContext.lookup, HandleContext.lookup.lookupBindings,
      Ne.symm hne]
    grind
  · contradiction

/-- Agreement on available non-operation handles. `ignored` contains the root's result IDs,
which are intentionally absent from the semantic replay. -/
def HandleContext.AgreesOn (defined : HandleContext) (ignored : List Nat)
    (stage target : SemanticAssignment) : Prop :=
  ∀ kind (handle : Handle OpCode kind), kind ≠ .op → defined.require handle = true →
    handle.id ∉ ignored → stage handle.id = target handle.id

/-- Adding a semantically bound handle consistent prefix agreement with the static context. -/
theorem HandleContext.AgreesOn.bind_insertFresh {before after : HandleContext}
    {ignored : List Nat} {stage target : SemanticAssignment}
    {kind : HandleType OpCode} {handle : Handle OpCode kind} {binding : SemanticBinding}
    (agree : before.AgreesOn ignored stage target)
    (inserted : before.insertFresh handle = some after)
    (bound : target handle.id = some binding) :
    after.AgreesOn ignored (stage.bind handle.id binding) target := by
  intro queriedKind queried notOp available notIgnored
  by_cases heq : queried.id = handle.id
  · simp [SemanticAssignment.bind, heq, bound]
  · have hbefore : before.require queried = true := by
      rw [← HandleContext.require_of_insertFresh_of_ne inserted heq]
      exact available
    simpa [SemanticAssignment.bind, heq] using
      agree queriedKind queried notOp hbefore notIgnored

/-- Root results and operation handles can be collected without adding semantic bindings. -/
theorem HandleContext.AgreesOn.insertFresh_ignored {before after : HandleContext}
    {ignored : List Nat} {stage target : SemanticAssignment}
    {kind : HandleType OpCode} {handle : Handle OpCode kind}
    (agree : before.AgreesOn ignored stage target)
    (inserted : before.insertFresh handle = some after)
    (skip : kind = .op ∨ handle.id ∈ ignored) :
    after.AgreesOn ignored stage target := by
  intro queriedKind queried notOp available notIgnored
  have hne : queried.id ≠ handle.id := by
    intro heq
    have hlookup := HandleContext.lookup_of_insertFresh inserted
    have hrequire : after.lookup queried.id = some queriedKind := by
      have hh := available
      simp only [HandleContext.require, decide_eq_true_eq] at hh
      exact hh.1
    have hk : kind = queriedKind := by rw [heq, hlookup] at hrequire; exact Option.some.inj hrequire
    rcases skip with hop | hignored
    · exact notOp (hk ▸ hop)
    · exact notIgnored (heq ▸ hignored)
  exact agree queriedKind queried notOp
    (by rw [← HandleContext.require_of_insertFresh_of_ne inserted hne]; exact available) notIgnored

theorem HandleContext.AgreesOn.getType {defined : HandleContext} {ignored : List Nat}
    {stage target : SemanticAssignment} (h : defined.AgreesOn ignored stage target)
    (handle : Handle OpCode .type) (available : defined.require handle = true)
    (notIgnored : handle.id ∉ ignored) : stage.getType handle = target.getType handle := by
  simp only [SemanticAssignment.getType, h .type handle (by intro heq; cases heq) available notIgnored]

theorem HandleContext.AgreesOn.getValue {defined : HandleContext} {ignored : List Nat}
    {stage target : SemanticAssignment} (h : defined.AgreesOn ignored stage target)
    (handle : Handle OpCode .value) (available : defined.require handle = true)
    (notIgnored : handle.id ∉ ignored) : stage.getValue handle = target.getValue handle := by
  simp only [SemanticAssignment.getValue, h .value handle (by intro heq; cases heq) available notIgnored]

theorem HandleContext.AgreesOn.getValueType {defined : HandleContext} {ignored : List Nat}
    {stage target : SemanticAssignment} (h : defined.AgreesOn ignored stage target)
    (handle : Handle OpCode .value) (available : defined.require handle = true)
    (notIgnored : handle.id ∉ ignored) : stage.getValueType handle = target.getValueType handle := by
  simp only [SemanticAssignment.getValueType, h .value handle (by intro heq; cases heq) available notIgnored]

theorem HandleContext.AgreesOn.getProperty {defined : HandleContext} {ignored : List Nat}
    {stage target : SemanticAssignment} (h : defined.AgreesOn ignored stage target)
    {code : OpCode} (handle : Handle OpCode (.prop code))
    (available : defined.require handle = true) (notIgnored : handle.id ∉ ignored) :
    stage.getProperty handle = target.getProperty handle := by
  simp only [SemanticAssignment.getProperty, h (.prop code) handle (by intro heq; cases heq) available notIgnored]

/-- Available non-root input collections have identical semantic lookup results. -/
theorem HandleContext.AgreesOn.getValues {defined : HandleContext} {ignored : List Nat}
    {stage target : SemanticAssignment} (h : defined.AgreesOn ignored stage target)
    (handles : List (Handle OpCode .value)) (available : defined.requireMany handles = true)
    (notIgnored : ∀ handle ∈ handles, handle.id ∉ ignored) :
    stage.getValues handles = target.getValues handles := by
  simp only [HandleContext.requireMany, List.all_eq_true] at available
  induction handles with
  | nil => rfl
  | cons handle handles ih =>
    have hhead := h.getValue handle (available handle (by simp)) (notIgnored handle (by simp))
    have htail := ih (fun handle hm => notIgnored handle (by simp [hm]))
      (fun handle hm => available handle (by simp [hm]))
    simp only [SemanticAssignment.getValues, List.mapM_cons] at htail ⊢
    rw [hhead, htail]

/-- Available value handles retain their declared type metadata during replay. -/
theorem HandleContext.AgreesOn.getValueTypes {defined : HandleContext} {ignored : List Nat}
    {stage target : SemanticAssignment} (h : defined.AgreesOn ignored stage target)
    (handles : List (Handle OpCode .value)) (available : defined.requireMany handles = true)
    (notIgnored : ∀ handle ∈ handles, handle.id ∉ ignored) :
    stage.getValueTypes handles = target.getValueTypes handles := by
  simp only [HandleContext.requireMany, List.all_eq_true] at available
  induction handles with
  | nil => rfl
  | cons handle handles ih =>
    have hhead := h.getValueType handle (available handle (by simp)) (notIgnored handle (by simp))
    have htail := ih (fun handle hm => notIgnored handle (by simp [hm]))
      (fun handle hm => available handle (by simp [hm]))
    simp only [SemanticAssignment.getValueTypes, List.mapM_cons] at htail ⊢
    rw [hhead, htail]

/-- Available non-root input collections have identical semantic lookup results. -/
theorem HandleContext.AgreesOn.getTypes {defined : HandleContext} {ignored : List Nat}
    {stage target : SemanticAssignment} (h : defined.AgreesOn ignored stage target)
    (handles : List (Handle OpCode .type)) (available : defined.requireMany handles = true)
    (notIgnored : ∀ handle ∈ handles, handle.id ∉ ignored) :
    stage.getTypes handles = target.getTypes handles := by
  simp only [HandleContext.requireMany, List.all_eq_true] at available
  induction handles with
  | nil => rfl
  | cons handle handles ih =>
    have hhead := h.getType handle (available handle (by simp)) (notIgnored handle (by simp))
    have htail := ih (fun handle hm => notIgnored handle (by simp [hm]))
      (fun handle hm => available handle (by simp [hm]))
    simp only [SemanticAssignment.getTypes, List.mapM_cons] at htail ⊢
    rw [hhead, htail]

/-- Replay fresh result bindings in the same order as static collection. -/
theorem SemanticAssignment.bindsValues_of_collect
    {before after : HandleContext} {ignored : List Nat} {stage target : SemanticAssignment}
    (handles : List (Handle OpCode .value)) (values : List RuntimeValue) {types : List TypeAttr}
    (collected : before.insertManyFresh handles = some after)
    (bound : SemanticAssignment.ValuesBound target handles values types)
    (agree : before.AgreesOn ignored stage target) (consistent : stage.AgreesWith target) :
    ∃ final, stage.BindsValues handles values final types ∧
      after.AgreesOn ignored final target ∧ final.AgreesWith target := by
  induction bound generalizing before stage with
  | nil =>
    simp only [HandleContext.insertManyFresh, List.foldlM_nil, Option.pure_def,
      Option.some.injEq] at collected
    subst after
    exact ⟨stage, .nil _, agree, consistent⟩
  | @cons handle value handles values type types hb htail ih =>
    simp only [HandleContext.insertManyFresh, List.foldlM_cons, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at collected
    obtain ⟨middle, hinsert, hrest⟩ := collected
    obtain ⟨final, hf, ha, he⟩ := ih hrest (agree.bind_insertFresh hinsert hb)
      (consistent.bind handle.id (.value value type) hb)
    exact ⟨final, .cons handle value type hf, ha, he⟩

/-- Collecting only ignored result IDs needs no semantic bindings. -/
theorem HandleContext.AgreesOn.insertManyFresh_ignored
    {before after : HandleContext} {ignored : List Nat} {stage target : SemanticAssignment}
    (handles : List (Handle OpCode .value))
    (collected : before.insertManyFresh handles = some after)
    (skip : ∀ handle ∈ handles, handle.id ∈ ignored)
    (agree : before.AgreesOn ignored stage target) : after.AgreesOn ignored stage target := by
  induction handles generalizing before with
  | nil =>
    simp only [HandleContext.insertManyFresh, List.foldlM_nil, Option.pure_def,
      Option.some.injEq] at collected
    subst after; exact agree
  | cons handle handles ih =>
    simp only [HandleContext.insertManyFresh, List.foldlM_cons, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at collected
    obtain ⟨middle, hinsert, hrest⟩ := collected
    exact ih hrest (fun handle hm => skip handle (by simp [hm]))
      (agree.insertFresh_ignored hinsert (.inr (skip handle (by simp))))

namespace MetadataTuple.Shape

/-- Every output metadata value occurs at its designated handle in the final assignment. -/
def TargetBound (target : SemanticAssignment) (shape : MetadataTuple.Shape OpCode Handles)
    (handles : Handles) (values : shape.Values) : Prop :=
  match shape with
  | .unit => True
  | .atom .type => target handles.id = some (.type values)
  | .atom (.property code) => target handles.id = some (.property code values)
  | .cons .type tail => target handles.1.id = some (.type values.1) ∧
      tail.TargetBound target handles.2 values.2
  | .cons (.property code) tail => target handles.1.id = some (.property code values.1) ∧
      tail.TargetBound target handles.2 values.2

/-- Metadata binding follows the exact sequence of static fresh insertion. -/
theorem bindSemantic_of_collect {target stage : SemanticAssignment}
    {before after : HandleContext} {ignored : List Nat}
    (shape : MetadataTuple.Shape OpCode Handles) (handles : Handles) (values : shape.Values)
    (collected : shape.insertFreshBindings before handles = some after)
    (bound : shape.TargetBound target handles values)
    (agree : before.AgreesOn ignored stage target) (consistent : stage.AgreesWith target) :
    after.AgreesOn ignored (shape.bindSemantic stage handles values) target ∧
      (shape.bindSemantic stage handles values).AgreesWith target := by
  induction shape generalizing before stage with
  | unit =>
    simp only [MetadataTuple.Shape.insertFreshBindings, Option.some.injEq] at collected
    subst after; exact ⟨agree, consistent⟩
  | atom atom =>
    cases atom with
    | type => exact ⟨agree.bind_insertFresh collected bound, consistent.bind _ _ bound⟩
    | property code => exact ⟨agree.bind_insertFresh collected bound, consistent.bind _ _ bound⟩
  | cons atom tail ih =>
    cases atom with
    | type =>
      simp only [MetadataTuple.Shape.insertFreshBindings, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at collected
      obtain ⟨middle, hinsert, hrest⟩ := collected
      exact ih _ _ hrest bound.2 (agree.bind_insertFresh hinsert bound.1)
        (consistent.bind _ _ bound.1)
    | property code =>
      simp only [MetadataTuple.Shape.insertFreshBindings, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at collected
      obtain ⟨middle, hinsert, hrest⟩ := collected
      exact ih _ _ hrest bound.2 (agree.bind_insertFresh hinsert bound.1)
        (consistent.bind _ _ bound.1)

/-- Input metadata handles exclude the root results omitted from semantic replay. -/
def Avoids (ignored : List Nat) (shape : MetadataTuple.Shape OpCode Handles)
    (handles : Handles) : Prop :=
  match shape with
  | .unit => True
  | .atom .type => handles.id ∉ ignored
  | .atom (.property _) => handles.id ∉ ignored
  | .cons .type tail => handles.1.id ∉ ignored ∧ tail.Avoids ignored handles.2
  | .cons (.property _) tail => handles.1.id ∉ ignored ∧ tail.Avoids ignored handles.2

theorem resolveSemantic_eq_of_agreesOn {target stage : SemanticAssignment}
    {defined : HandleContext} {ignored : List Nat}
    (shape : MetadataTuple.Shape OpCode Handles) (handles : Handles)
    (required : shape.requireBindings defined handles = true)
    (safe : shape.Avoids ignored handles) (agree : defined.AgreesOn ignored stage target) :
    shape.resolveSemantic stage handles = shape.resolveSemantic target handles := by
  induction shape with
  | unit => rfl
  | atom atom =>
    cases atom with
    | type => exact agree.getType _ required safe
    | property code => exact agree.getProperty _ required safe
  | cons atom tail ih =>
    cases atom with
    | type =>
      simp only [MetadataTuple.Shape.requireBindings, Bool.and_eq_true] at required
      simp only [MetadataTuple.Shape.resolveSemantic, MetadataTuple.Atom.resolveSemantic, agree.getType _ required.1 safe.1,
        ih _ required.2 safe.2]
    | property code =>
      simp only [MetadataTuple.Shape.requireBindings, Bool.and_eq_true] at required
      simp only [MetadataTuple.Shape.resolveSemantic, MetadataTuple.Atom.resolveSemantic, agree.getProperty _ required.1 safe.1,
        ih _ required.2 safe.2]

end MetadataTuple.Shape

/-- A later concrete assignment preserves every populated slot of an earlier assignment. -/
def Assignment.Extends (later earlier : Assignment OpCode) : Prop :=
  ∀ kind (handle : Handle OpCode kind) binding,
    earlier.getBinding handle = some binding → later.getBinding handle = some binding

theorem Assignment.Extends.refl (assignment : Assignment OpCode) : assignment.Extends assignment := by
  intro kind handle binding h; exact h

theorem Assignment.Extends.trans {a b c : Assignment OpCode}
    (hcb : c.Extends b) (hba : b.Extends a) : c.Extends a := by
  intro kind handle binding h; exact hcb kind handle binding (hba kind handle binding h)

theorem Assignment.Extends.of_runDecls {decls : List (MatchDecl OpCode)}
    {ctx : IRContext OpCode} {a b : Assignment OpCode}
    (h : MatchProg.runDecls decls ctx a = some b) : b.Extends a := by
  intro kind handle binding hold
  exact MatchProg.getBinding_preserved_of_runDecls decls h hold

theorem Assignment.Extends.of_metadata_bind
    (shape : MetadataTuple.Shape OpCode Handles) (handles : Handles) (values : shape.Values)
    {a b : Assignment OpCode} (h : shape.bind a handles values = some b) : b.Extends a := by
  intro kind handle binding hold
  exact MetadataTuple.Shape.getBinding_preserved_of_bind shape handles values h hold

theorem Assignment.Extends.getOp {a b : Assignment OpCode} (h : b.Extends a)
    {handle : Handle OpCode .op} {value : OperationPtr} (hv : a.getOp handle = some value) :
    b.getOp handle = some value := by
  cases hb : a.getBinding handle with
  | none => simp [Assignment.getOp, hb] at hv
  | some binding =>
    cases binding <;> simp [Assignment.getOp, hb] at hv
    subst value
    simp [Assignment.getOp, h _ handle _ hb]

theorem Assignment.Extends.getValue {a b : Assignment OpCode} (h : b.Extends a)
    {handle : Handle OpCode .value} {value : ValuePtr} (hv : a.getValue handle = some value) :
    b.getValue handle = some value := by
  cases hb : a.getBinding handle with
  | none => simp [Assignment.getValue, hb] at hv
  | some binding =>
    cases binding <;> simp [Assignment.getValue, hb] at hv
    subst value
    simp [Assignment.getValue, h _ handle _ hb]

theorem Assignment.Extends.getType {a b : Assignment OpCode} (h : b.Extends a)
    {handle : Handle OpCode .type} {value : TypeAttr} (hv : a.getType handle = some value) :
    b.getType handle = some value := by
  cases hb : a.getBinding handle with
  | none => simp [Assignment.getType, hb] at hv
  | some binding =>
    cases binding <;> simp [Assignment.getType, hb] at hv
    subst value
    simp [Assignment.getType, h _ handle _ hb]

theorem Assignment.Extends.getProperty {a b : Assignment OpCode} (h : b.Extends a)
    {code : OpCode} {handle : Handle OpCode (.prop code)} {value : propertiesOf code}
    (hv : a.getProperty handle = some value) : b.getProperty handle = some value := by
  cases hb : a.getBinding handle with
  | none => simp [Assignment.getProperty, hb] at hv
  | some binding =>
    have hb' := h _ handle binding hb
    simpa [Assignment.getProperty, hb, hb'] using hv

theorem Assignment.Extends.getValues {a b : Assignment OpCode} (h : b.Extends a)
    {handles : Array (Handle OpCode .value)} {values : Array ValuePtr}
    (hv : a.getValues handles = some values) : b.getValues handles = some values := by
  apply (Array.mapM_eq_some_iff_of_size_eq (Array.size_eq_of_mapM_eq_some hv)).mpr
  intro i hi
  exact h.getValue ((Array.mapM_eq_some_iff_of_size_eq
    (Array.size_eq_of_mapM_eq_some hv)).mp hv i hi)

theorem Assignment.Extends.getTypes {a b : Assignment OpCode} (h : b.Extends a)
    {handles : Array (Handle OpCode .type)} {values : Array TypeAttr}
    (hv : a.getTypes handles = some values) : b.getTypes handles = some values := by
  apply (Array.mapM_eq_some_iff_of_size_eq (Array.size_eq_of_mapM_eq_some hv)).mpr
  intro i hi
  exact h.getType ((Array.mapM_eq_some_iff_of_size_eq
    (Array.size_eq_of_mapM_eq_some hv)).mp hv i hi)

theorem MetadataTuple.Shape.targetBound_of_bind
    (shape : MetadataTuple.Shape OpCode Handles) (handles : Handles) (values : shape.Values)
    {a b final : Assignment OpCode} (resolve : ValuePtr → Option RuntimeValue)
    (run : shape.bind a handles values = some b) (preserved : final.Extends b)
    (typeOf : ValuePtr → TypeAttr) :
    shape.TargetBound (final.denote resolve typeOf) handles values := by
  induction shape generalizing a b with
  | unit => trivial
  | atom atom =>
    cases atom with
    | type =>
      have hb := preserved _ handles _ (Assignment.getBinding_of_bind run)
      simpa [MetadataTuple.Shape.TargetBound, Assignment.denote, Assignment.getBinding, Binding.denote] using
        congrArg (fun result => result >>= Binding.denote resolve typeOf) hb
    | property code =>
      have hb := preserved _ handles _ (Assignment.getBinding_of_bind run)
      simpa [MetadataTuple.Shape.TargetBound, Assignment.denote, Assignment.getBinding, Binding.denote] using
        congrArg (fun result => result >>= Binding.denote resolve typeOf) hb
  | cons atom tail ih =>
    simp only [MetadataTuple.Shape.bind, Option.bind_eq_bind, Option.bind_eq_some_iff] at run
    obtain ⟨middle, hh, ht⟩ := run
    have hpreserved := preserved.trans (Assignment.Extends.of_metadata_bind tail _ _ ht)
    cases atom with
    | type =>
      constructor
      · have hb := hpreserved _ handles.1 _ (Assignment.getBinding_of_bind hh)
        simpa [MetadataTuple.Shape.TargetBound, Assignment.denote, Assignment.getBinding, Binding.denote] using
          congrArg (fun result => result >>= Binding.denote resolve typeOf) hb
      · exact ih _ _ ht preserved
    | property code =>
      constructor
      · have hb := hpreserved _ handles.1 _ (Assignment.getBinding_of_bind hh)
        simpa [MetadataTuple.Shape.TargetBound, Assignment.denote, Assignment.getBinding, Binding.denote] using
          congrArg (fun result => result >>= Binding.denote resolve typeOf) hb
      · exact ih _ _ ht preserved

theorem MetadataTuple.Shape.resolveSemantic_of_resolve
    (shape : MetadataTuple.Shape OpCode Handles) (handles : Handles) (values : shape.Values)
    {a final : Assignment OpCode} (resolve : ValuePtr → Option RuntimeValue)
    (run : shape.resolve a handles = some values) (preserved : final.Extends a)
    (typeOf : ValuePtr → TypeAttr) :
    shape.resolveSemantic (final.denote resolve typeOf) handles = some values := by
  induction shape with
  | unit => cases values; rfl
  | atom atom =>
    cases atom with
    | type => exact (Assignment.denote_getType final resolve handles typeOf).trans (preserved.getType run)
    | property code =>
      exact (Assignment.denote_getProperty final resolve handles typeOf).trans (preserved.getProperty run)
  | cons atom tail ih =>
    simp only [MetadataTuple.Shape.resolve, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at run
    obtain ⟨headValue, hh, tailValues, ht, heq⟩ := run
    cases heq
    have htail := ih _ _ ht
    cases atom with
    | type =>
      have hhead := (Assignment.denote_getType final resolve handles.1 typeOf).trans (preserved.getType hh)
      simp [MetadataTuple.Shape.resolveSemantic, MetadataTuple.Atom.resolveSemantic, hhead, htail]
    | property code =>
      have hhead := (Assignment.denote_getProperty final resolve handles.1 typeOf).trans (preserved.getProperty hh)
      simp [MetadataTuple.Shape.resolveSemantic, MetadataTuple.Atom.resolveSemantic, hhead, htail]

theorem SemanticAssignment.valueBinding_of_getValue {assignment : SemanticAssignment}
    {handle : Handle OpCode .value} {value : RuntimeValue} {type : TypeAttr}
    (h : assignment.getValue handle = some value)
    (ht : assignment.getValueType handle = some type) :
    assignment handle.id = some (.value value type) := by
  cases hb : assignment handle.id with
  | none => simp [SemanticAssignment.getValue, hb] at h
  | some binding => cases binding <;> simp_all [SemanticAssignment.getValue, SemanticAssignment.getValueType]

theorem SemanticAssignment.typeBinding_of_getType {assignment : SemanticAssignment}
    {handle : Handle OpCode .type} {value : TypeAttr}
    (h : assignment.getType handle = some value) : assignment handle.id = some (.type value) := by
  cases hb : assignment handle.id with
  | none => simp [SemanticAssignment.getType, hb] at h
  | some binding => cases binding <;> simp_all [SemanticAssignment.getType]

theorem SemanticAssignment.propertyBinding_of_getProperty {assignment : SemanticAssignment}
    {code : OpCode} {handle : Handle OpCode (.prop code)} {value : propertiesOf code}
    (h : assignment.getProperty handle = some value) :
    assignment handle.id = some (.property code value) := by
  cases hb : assignment handle.id with
  | none => simp [SemanticAssignment.getProperty, hb] at h
  | some binding =>
    cases binding <;> simp [SemanticAssignment.getProperty, hb] at h
    obtain ⟨heq, hvalue⟩ := h
    cases heq
    cases hvalue
    rfl

theorem SemanticAssignment.valuesBound_of_getValues {assignment : SemanticAssignment}
    {handles : List (Handle OpCode .value)} {values : List RuntimeValue} {types : List TypeAttr}
    (h : assignment.getValues handles = some values)
    (ht : assignment.getValueTypes handles = some types) : assignment.ValuesBound handles values types := by
  induction handles generalizing values types with
  | nil => cases h; cases ht; exact .nil
  | cons handle handles ih =>
    simp only [SemanticAssignment.getValues, SemanticAssignment.getValueTypes, List.mapM_cons,
      Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h ht
    obtain ⟨value, hv, rest, hr, rfl⟩ := h
    obtain ⟨type, hty, types, htypes, rfl⟩ := ht
    exact .cons (SemanticAssignment.valueBinding_of_getValue hv hty) (ih hr htypes)

namespace CTree

/-- Semantic equations supplied by a concrete match at one replay stage.
Inputs must already be available at the stage; newly chosen outputs are read from `target`.
Unlike `Realizes`, this predicate contains no proposed intermediate assignment. -/
def MatchDecl.Constraints (root : Handle OpCode .op) (target stage : SemanticAssignment)
    (decl : MatchDecl OpCode) : Prop :=
  match decl with
  | .type matcher handle =>
      ∃ ty, matcher ty = true ∧ target handle.id = some (.type ty)
  | .value typeHandle handle =>
      ∃ ty value, stage.getType typeHandle = some ty ∧ value.Conforms ty ∧
        target handle.id = some (.value value ty)
  | .operation code operands types matcher propertyHandle opHandle results _ =>
      ∃ operandValues operandTypes resultTypes property,
        stage.getValues operands.toList = some operandValues ∧
        stage.getValueTypes operands.toList = some operandTypes ∧
        stage.getTypes types.toList = some resultTypes ∧ matcher property = true ∧
        IsFromVerifiedOp code operandTypes.toArray resultTypes.toArray property ∧
        target propertyHandle.id = some (.property code property) ∧
        (opHandle ≠ root → ∃ resultValues,
          SemanticAssignment.ValuesBound target
            results.toList resultValues resultTypes ∧
          CanInterpretTo code property resultTypes.toArray operandValues.toArray
            (.ok resultValues.toArray))
  | @MatchDecl.inspectOperation _ _ _ bundle _ _ outputs =>
      ∃ values : MetadataValues OpCode _,
        ∀ stage, stage.AgreesWith target →
          (MetadataTuple.bindSemantic (self := bundle) stage outputs values).AgreesWith target
  | @MatchDecl.applyNative _ _ _ bundle inputs predicate =>
      ∃ values, MetadataTuple.resolveSemantic (self := bundle) stage inputs = some values ∧
        predicate values = true

/-- Final-assignment equations extracted from concrete matcher execution. -/
def MatchDecl.TargetConstraints (root : Handle OpCode .op) (target : SemanticAssignment)
    (decl : MatchDecl OpCode) : Prop :=
  match decl with
  | @MatchDecl.inspectOperation _ _ _ bundle _ _ outputs =>
      ∃ values : bundle.shape.Values, bundle.shape.TargetBound target outputs values
  | _ => MatchDecl.Constraints root target target decl

/-- Runtime operation matching plus SSA resolver equations imply its semantic target equations.
The equation hypothesis concerns the raw opcode interpreter, rather than Puddle semantics. -/
theorem MatchDecl.operation_targetConstraints_of_run
    {code : OpCode} {operands : Array (Handle OpCode .value)}
    {types : Array (Handle OpCode .type)} {matcher : PropertyMatcher code}
    {property : Handle OpCode (.prop code)} {op : Handle OpCode .op}
    {results : Array (Handle OpCode .value)} {count : results.size = types.size}
    {ctx : IRContext OpCode} {a b final : Assignment OpCode} {root : Handle OpCode .op}
    (resolve : ValuePtr → Option RuntimeValue)
    (run : (MatchDecl.operation code operands types matcher property op results count).run ctx a = some b)
    (preserved : final.Extends b)
    (equation : ∀ (matched : OperationPtr), final.getOp op = some matched →
      matched.getOpType! ctx = code →
      IsFromVerifiedOp code (matched.getOperandTypes! ctx) (matched.getResultTypes! ctx)
        (matched.getProperties! ctx code) ∧
      ∃ operandValues, (matched.getOperands! ctx).toList.mapM resolve = some operandValues ∧
        (op ≠ root → ∃ resultValues,
          (matched.getResults! ctx).toList.mapM resolve = some resultValues ∧
          CanInterpretTo code (matched.getProperties! ctx code) (matched.getResultTypes! ctx)
            operandValues.toArray (.ok resultValues.toArray))) :
    MatchDecl.TargetConstraints root (final.denote resolve (fun ptr => ptr.getType! ctx))
      (.operation code operands types matcher property op results count) := by
  obtain ⟨matched, hop, hcode, haccepted, hoperands, htypes, hproperty, hresults⟩ :=
    MatchDecl.operation_fields_of_run run
  obtain ⟨hverified, operandValues, hresolve, hsem⟩ := equation matched (preserved.getOp hop) hcode
  have hv : (final.denote resolve (fun ptr => ptr.getType! ctx)).getValues operands.toList = some operandValues := by
    rw [Assignment.denote_getValues final resolve operands (fun ptr => ptr.getType! ctx), preserved.getValues hoperands]
    exact hresolve
  have ht : (final.denote resolve (fun ptr => ptr.getType! ctx)).getTypes types.toList = some (matched.getResultTypes! ctx).toList := by
    rw [Assignment.denote_getTypes final resolve types (fun ptr => ptr.getType! ctx), preserved.getTypes htypes]; rfl
  have hp : (final.denote resolve (fun ptr => ptr.getType! ctx)) property.id = some (.property code (matched.getProperties! ctx code)) :=
    SemanticAssignment.propertyBinding_of_getProperty
      ((Assignment.denote_getProperty final resolve property (fun ptr => ptr.getType! ctx)).trans (preserved.getProperty hproperty))
  have hvt : (final.denote resolve (fun ptr => ptr.getType! ctx)).getValueTypes operands.toList =
      some (matched.getOperandTypes! ctx).toList := by
    rw [Assignment.denote_getValueTypes_of_getValues final resolve operands
      (preserved.getValues hoperands) hresolve (fun ptr => ptr.getType! ctx)]
    simp [OperationPtr.getOperandTypes!_def]
  refine ⟨operandValues, (matched.getOperandTypes! ctx).toList,
    (matched.getResultTypes! ctx).toList, _, hv, hvt, ht, haccepted, by simpa using hverified, hp, ?_⟩
  intro hnotRoot
  obtain ⟨resultValues, hresolveResults, hinterpret⟩ := hsem hnotRoot
  have hr : (final.denote resolve (fun ptr => ptr.getType! ctx)).getValues results.toList = some resultValues := by
    rw [Assignment.denote_getValues final resolve results (fun ptr => ptr.getType! ctx), preserved.getValues hresults]
    exact hresolveResults
  exact ⟨resultValues, SemanticAssignment.valuesBound_of_getValues hr (by
    rw [Assignment.denote_getValueTypes_of_getValues final resolve results
      (preserved.getValues hresults) hresolveResults (fun ptr => ptr.getType! ctx)]
    simp [OperationPtr.getResultTypes!_def]), by simpa using hinterpret⟩

private theorem bool_eq_true_of_guard {b : Bool} {u : Unit}
    (h : (guard (b = true) : Option Unit) = some u) : b = true := by
  cases b <;> simp_all [guard]

theorem MatchDecl.type_targetConstraints_of_run
    {matcher : TypeMatcher} {handle : Handle OpCode .type}
    {ctx : IRContext OpCode} {a b final : Assignment OpCode} {root : Handle OpCode .op}
    (resolve : ValuePtr → Option RuntimeValue)
    (run : (MatchDecl.type matcher handle).run ctx a = some b) (preserved : final.Extends b) :
    MatchDecl.TargetConstraints root (final.denote resolve (fun ptr => ptr.getType! ctx)) (.type matcher handle) := by
  simp only [MatchDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at run
  obtain ⟨ty, htype, u, haccepted, rfl⟩ := run
  exact ⟨ty, bool_eq_true_of_guard haccepted,
    SemanticAssignment.typeBinding_of_getType
      ((Assignment.denote_getType final resolve handle (fun ptr => ptr.getType! ctx)).trans (preserved.getType htype))⟩

theorem MatchDecl.value_targetConstraints_of_run
    {typeHandle : Handle OpCode .type} {handle : Handle OpCode .value}
    {ctx : IRContext OpCode} {a b final : Assignment OpCode} {root : Handle OpCode .op}
    (resolve : ValuePtr → Option RuntimeValue)
    (run : (MatchDecl.value typeHandle handle).run ctx a = some b) (preserved : final.Extends b)
    (wellTyped : ∀ ptr, final.getValue handle = some ptr →
      ∃ value, resolve ptr = some value ∧ value.Conforms (ptr.getType! ctx)) :
    MatchDecl.TargetConstraints root (final.denote resolve (fun ptr => ptr.getType! ctx)) (.value typeHandle handle) := by
  have hkeep : b.Extends a := by
    intro kind queried binding hb
    exact MatchDecl.getBinding_preserved_of_run _ run hb
  simp only [MatchDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff] at run
  obtain ⟨ptr, hptr, hbind⟩ := run
  have hptrFinal := (preserved.trans hkeep).getValue hptr
  obtain ⟨value, hresolve, hconforms⟩ := wellTyped ptr hptrFinal
  have htype := Assignment.getType_of_bindType hbind
  refine ⟨ptr.getType! ctx, value, ?_, hconforms, ?_⟩
  · exact (Assignment.denote_getType final resolve typeHandle (fun ptr => ptr.getType! ctx)).trans (preserved.getType htype)
  · apply SemanticAssignment.valueBinding_of_getValue
    · rw [Assignment.denote_getValue final resolve handle (fun ptr => ptr.getType! ctx), hptrFinal]
      exact hresolve
    · exact Assignment.denote_getValueType_of_getValue final resolve handle hptrFinal hresolve
        (fun ptr => ptr.getType! ctx)

theorem MatchDecl.inspect_targetConstraints_of_run
    {Outputs : Type} [bundle : IsMetadataTuple OpCode Outputs]
    {op : Handle OpCode .op} {inspect : IRContext OpCode → OperationPtr → Option (MetadataValues OpCode Outputs)}
    {outputs : Outputs} {ctx : IRContext OpCode} {a b final : Assignment OpCode}
    {root : Handle OpCode .op} (resolve : ValuePtr → Option RuntimeValue)
    (run : (MatchDecl.inspectOperation op inspect outputs).run ctx a = some b)
    (preserved : final.Extends b) :
    MatchDecl.TargetConstraints root (final.denote resolve (fun ptr => ptr.getType! ctx)) (.inspectOperation op inspect outputs) := by
  simp only [MatchDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff] at run
  obtain ⟨operation, _, values, _, hbind⟩ := run
  exact ⟨values, MetadataTuple.Shape.targetBound_of_bind bundle.shape outputs values resolve hbind preserved
    (fun ptr => ptr.getType! ctx)⟩

theorem MatchDecl.native_targetConstraints_of_run
    {Inputs : Type} [bundle : IsMetadataTuple OpCode Inputs]
    {inputs : Inputs} {predicate : MetadataValues OpCode Inputs → Bool}
    {ctx : IRContext OpCode} {a b final : Assignment OpCode} {root : Handle OpCode .op}
    (resolve : ValuePtr → Option RuntimeValue)
    (run : (MatchDecl.applyNative inputs predicate).run ctx a = some b)
    (preserved : final.Extends b) :
    MatchDecl.TargetConstraints root (final.denote resolve (fun ptr => ptr.getType! ctx)) (.applyNative inputs predicate) := by
  simp only [MatchDecl.run, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at run
  obtain ⟨values, hresolve, u, haccepted, rfl⟩ := run
  exact ⟨values, MetadataTuple.Shape.resolveSemantic_of_resolve bundle.shape inputs values resolve
    hresolve preserved (fun ptr => ptr.getType! ctx), bool_eq_true_of_guard haccepted⟩

/-- Interpreter facts needed from a reachable execution when replaying a concrete matcher.
Only value declarations need conformance; only non-root operations need successful pure outcomes. -/
def MatchDecl.RuntimeEquations (ctx : IRContext OpCode) (root : Handle OpCode .op)
    (resolve : ValuePtr → Option RuntimeValue) (final : Assignment OpCode)
    (decl : MatchDecl OpCode) : Prop :=
  match decl with
  | .value _ handle => ∀ ptr, final.getValue handle = some ptr →
      ∃ value, resolve ptr = some value ∧ value.Conforms (ptr.getType! ctx)
  | .operation code _ _ _ _ op _ _ => ∀ (matched : OperationPtr), final.getOp op = some matched →
      matched.getOpType! ctx = code →
      IsFromVerifiedOp code (matched.getOperandTypes! ctx) (matched.getResultTypes! ctx)
        (matched.getProperties! ctx code) ∧
      ∃ operandValues, (matched.getOperands! ctx).toList.mapM resolve = some operandValues ∧
        (op ≠ root → ∃ resultValues,
          (matched.getResults! ctx).toList.mapM resolve = some resultValues ∧
          CanInterpretTo code (matched.getProperties! ctx code) (matched.getResultTypes! ctx)
            operandValues.toArray (.ok resultValues.toArray))
  | _ => True

theorem MatchDecl.targetConstraints_of_run (decl : MatchDecl OpCode)
    {ctx : IRContext OpCode} {a b final : Assignment OpCode} {root : Handle OpCode .op}
    (resolve : ValuePtr → Option RuntimeValue) (run : decl.run ctx a = some b)
    (preserved : final.Extends b)
    (equations : MatchDecl.RuntimeEquations ctx root resolve final decl) :
    MatchDecl.TargetConstraints root (final.denote resolve (fun ptr => ptr.getType! ctx)) decl := by
  cases decl with
  | type matcher handle => exact MatchDecl.type_targetConstraints_of_run resolve run preserved
  | value ty handle => exact MatchDecl.value_targetConstraints_of_run resolve run preserved equations
  | operation code operands types matcher property op results count =>
    exact MatchDecl.operation_targetConstraints_of_run resolve run preserved equations
  | inspectOperation op inspect outputs =>
    exact MatchDecl.inspect_targetConstraints_of_run resolve run preserved
  | applyNative inputs predicate => exact MatchDecl.native_targetConstraints_of_run resolve run preserved

/-- Successful runtime matching establishes equations for every declaration at its final assignment. -/
theorem MatchProg.targetConstraints_of_runDecls (decls : List (MatchDecl OpCode))
    {ctx : IRContext OpCode} {a b final : Assignment OpCode} {root : Handle OpCode .op}
    (resolve : ValuePtr → Option RuntimeValue)
    (run : MatchProg.runDecls decls ctx a = some b) (preserved : final.Extends b)
    (equations : ∀ decl ∈ decls, MatchDecl.RuntimeEquations ctx root resolve final decl) :
    ∀ decl ∈ decls, MatchDecl.TargetConstraints root (final.denote resolve (fun ptr => ptr.getType! ctx)) decl := by
  induction decls generalizing a with
  | nil => simp
  | cons first rest ih =>
    simp only [MatchProg.runDecls, Option.bind_eq_bind, Option.bind_eq_some_iff] at run
    obtain ⟨middle, hfirst, hrest⟩ := run
    intro decl hdecl
    rcases List.mem_cons.mp hdecl with heq | hmem
    · subst decl
      exact MatchDecl.targetConstraints_of_run _ resolve hfirst
        (preserved.trans (Assignment.Extends.of_runDecls hrest)) (equations first (by simp))
    · exact ih hrest (fun decl hd => equations decl (by simp [hd])) decl hmem

theorem MatchProg.mem_bindingDecls {prog : MatchProg OpCode α} {decl : MatchDecl OpCode} :
    decl ∈ prog.bindingDecls ↔ decl ∈ prog.decls := by
  simp [MatchProg.bindingDecls, List.partition_eq_filter_filter]
  grind

/-- Extract final concrete equations directly from a successful matcher, in semantic binding order. -/
theorem MatchProg.targetConstraints_of_run {prog : MatchProg OpCode α}
    {ctx : IRContext OpCode} {root : OperationPtr} {final : Assignment OpCode}
    (resolve : ValuePtr → Option RuntimeValue) (run : prog.run ctx root = some final)
    (equations : ∀ decl ∈ prog.decls,
      MatchDecl.RuntimeEquations ctx prog.rootHandle resolve final decl) :
    ∀ decl ∈ prog.bindingDecls,
      MatchDecl.TargetConstraints prog.rootHandle (final.denote resolve (fun ptr => ptr.getType! ctx)) decl := by
  have hr : ∃ initial, MatchProg.runDecls prog.decls ctx initial = some final := by
    unfold MatchProg.run at run
    split at run <;> simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at run
    all_goals
      repeat first | obtain ⟨_, _, run⟩ := run
      exact ⟨_, run⟩
  obtain ⟨initial, hr⟩ := hr
  intro decl hdecl
  exact MatchProg.targetConstraints_of_runDecls _ resolve hr (Assignment.Extends.refl final)
    equations decl (MatchProg.mem_bindingDecls.mp hdecl)

/-- No semantic input refers to the root results omitted from replay. -/
def MatchDecl.Avoids (ignored : List Nat) (decl : MatchDecl OpCode) : Prop :=
  match decl with
  | .type .. => True
  | .value ty _ => ty.id ∉ ignored
  | .operation _ operands types _ _ _ _ _ =>
      (∀ handle ∈ operands, handle.id ∉ ignored) ∧
      (∀ handle ∈ types, handle.id ∉ ignored)
  | @MatchDecl.inspectOperation _ _ _ _ _ _ _ => True
  | @MatchDecl.applyNative _ _ _ bundle inputs _ => bundle.shape.Avoids ignored inputs

/-- Concrete semantic equations produce one semantic replay step without losing agreement. -/
theorem MatchDecl.realizes_of_constraints {root : Handle OpCode .op}
    {target stage : SemanticAssignment} {decl : MatchDecl OpCode}
    (agree : stage.AgreesWith target) (constraints : MatchDecl.Constraints root target stage decl) :
    ∃ final, MatchDecl.Realizes root decl stage final ∧ final.AgreesWith target := by
  cases decl with
  | type matcher handle =>
    obtain ⟨ty, accepted, bound⟩ := constraints
    exact ⟨_, .type ty accepted, agree.bind handle.id (.type ty) bound⟩
  | value typeHandle handle =>
    obtain ⟨ty, value, typeBound, conforms, bound⟩ := constraints
    exact ⟨_, .value ty value typeBound conforms, agree.bind handle.id (.value value ty) bound⟩
  | operation code operands types matcher propertyHandle opHandle results count =>
    obtain ⟨operandValues, operandTypes, resultTypes, property, hv, hvt, ht, hp, hverified, hb, hout⟩ := constraints
    by_cases hroot : opHandle = root
    · exact ⟨_, .rootOperation operandValues operandTypes resultTypes property hv hvt ht hp hverified hroot,
        agree.bind propertyHandle.id (.property code property) hb⟩
    · obtain ⟨resultValues, hresults, hsem⟩ := hout hroot
      obtain ⟨middle, hm, ha⟩ := SemanticAssignment.bindsValues_of_target agree _ _ hresults
      exact ⟨_, .operation operandValues operandTypes resultTypes property resultValues hv hvt ht hp hverified hroot hm hsem,
        ha.bind propertyHandle.id (.property code property) hb⟩
  | inspectOperation handle inspect outputs =>
    obtain ⟨values, hvalues⟩ := constraints
    exact ⟨_, .inspectOperation values, hvalues stage agree⟩
  | applyNative inputs predicate =>
    obtain ⟨values, resolved, accepted⟩ := constraints
    exact ⟨_, .applyNative values resolved accepted, agree⟩


/-- Static collection and final concrete equations reconstruct one semantic matcher step. -/
theorem MatchDecl.realizes_of_collectBindings {root : Handle OpCode .op}
    {target stage : SemanticAssignment} {before after : HandleContext} {ignored : List Nat}
    (decl : MatchDecl OpCode) (collected : decl.collectBindings before = some after)
    (equations : MatchDecl.TargetConstraints root target decl)
    (safe : MatchDecl.Avoids ignored decl)
    (rootResults : ∀ code operands types matcher propertyHandle opHandle results count,
      decl = .operation code operands types matcher propertyHandle opHandle results count →
      opHandle = root → ∀ handle ∈ results, handle.id ∈ ignored)
    (agree : before.AgreesOn ignored stage target) (consistent : stage.AgreesWith target) :
    ∃ final, MatchDecl.Realizes root decl stage final ∧
      after.AgreesOn ignored final target ∧ final.AgreesWith target := by
  cases decl with
  | type matcher handle =>
    obtain ⟨ty, accepted, bound⟩ := equations
    exact ⟨_, .type ty accepted, agree.bind_insertFresh collected bound,
      consistent.bind handle.id (.type ty) bound⟩
  | value typeHandle handle =>
    simp only [MatchDecl.collectBindings, Option.bind_eq_bind, Option.bind_eq_some_iff] at collected
    obtain ⟨u, hguard, hinsert⟩ := collected
    obtain ⟨ty, value, htype, hconforms, hbound⟩ := equations
    have hinput := agree.getType typeHandle (bool_eq_true_of_guard hguard) safe
    exact ⟨_, .value ty value (hinput.trans htype) hconforms,
      agree.bind_insertFresh hinsert hbound, consistent.bind handle.id (.value value ty) hbound⟩
  | operation code operands types matcher propertyHandle opHandle results count =>
    simp only [MatchDecl.collectBindings, Option.bind_eq_bind, Option.bind_eq_some_iff] at collected
    obtain ⟨u, hoperands, u', htypes, middle₁, hresults, middle₂, hprop, hop⟩ := collected
    obtain ⟨operandValues, operandTypes, resultTypes, property, hv, hvt, ht, hp, hverified, hb, hout⟩ := equations
    have hvalues : stage.getValues operands.toList = some operandValues := by
      rw [agree.getValues operands.toList (bool_eq_true_of_guard hoperands) (by simpa using safe.1)]; exact hv
    have hvalueTypes : stage.getValueTypes operands.toList = some operandTypes := by
      rw [agree.getValueTypes operands.toList (bool_eq_true_of_guard hoperands) (by simpa using safe.1)]; exact hvt
    have htypes' : stage.getTypes types.toList = some resultTypes := by
      rw [agree.getTypes types.toList (bool_eq_true_of_guard htypes) (by simpa using safe.2)]; exact ht
    by_cases hroot : opHandle = root
    · have hagree := agree.insertManyFresh_ignored _ hresults
        (by simpa using rootResults code operands types matcher propertyHandle opHandle results count rfl hroot)
      exact ⟨_, .rootOperation operandValues operandTypes resultTypes property hvalues hvalueTypes htypes' hp hverified hroot,
        (hagree.bind_insertFresh hprop hb).insertFresh_ignored hop (.inl rfl),
        consistent.bind propertyHandle.id (.property code property) hb⟩
    · obtain ⟨resultValues, hbound, hsem⟩ := hout hroot
      obtain ⟨middle, hbinds, hagree, hconsistent⟩ :=
        SemanticAssignment.bindsValues_of_collect _ _ hresults hbound agree consistent
      exact ⟨_, .operation operandValues operandTypes resultTypes property resultValues hvalues hvalueTypes htypes' hp
        hverified hroot hbinds hsem,
        (hagree.bind_insertFresh hprop hb).insertFresh_ignored hop (.inl rfl),
        hconsistent.bind propertyHandle.id (.property code property) hb⟩
  | inspectOperation opHandle inspect outputs =>
    simp only [MatchDecl.collectBindings, Option.bind_eq_bind, Option.bind_eq_some_iff] at collected
    obtain ⟨u, _, hout⟩ := collected
    obtain ⟨values, hbound⟩ := equations
    have hf := MetadataTuple.Shape.bindSemantic_of_collect _ _ values hout hbound agree consistent
    exact ⟨_, .inspectOperation values, hf⟩
  | applyNative inputs predicate =>
    simp only [MatchDecl.collectBindings, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at collected
    obtain ⟨u, hinputs, rfl⟩ := collected
    obtain ⟨values, hresolved, haccepted⟩ := equations
    have heq := MetadataTuple.Shape.resolveSemantic_eq_of_agreesOn _ inputs (bool_eq_true_of_guard hinputs) safe agree
    exact ⟨_, .applyNative values (heq.trans hresolved) haccepted, agree, consistent⟩

/-- Reconstruct a complete semantic trace from static collection and concrete equations.
Root results remain absent while every available non-root handle agrees with the concrete match. -/
theorem MatchProg.realizesDecls_of_collectDeclBindings
    {root : Handle OpCode .op} {target stage : SemanticAssignment}
    {before after : HandleContext} {ignored : List Nat}
    (decls : List (MatchDecl OpCode))
    (collected : MatchProg.collectDeclBindings decls before = some after)
    (equations : ∀ decl ∈ decls, MatchDecl.TargetConstraints root target decl)
    (safe : ∀ decl ∈ decls, MatchDecl.Avoids ignored decl)
    (rootResults : ∀ decl ∈ decls, ∀ code operands types matcher propertyHandle opHandle results count,
      decl = .operation code operands types matcher propertyHandle opHandle results count →
      opHandle = root → ∀ handle ∈ results, handle.id ∈ ignored)
    (agree : before.AgreesOn ignored stage target) (consistent : stage.AgreesWith target) :
    ∃ final, MatchProg.RealizesDecls root decls stage final ∧
      after.AgreesOn ignored final target ∧ final.AgreesWith target := by
  induction decls generalizing before stage with
  | nil =>
    simp only [MatchProg.collectDeclBindings, Option.some.injEq] at collected
    subst after
    exact ⟨stage, .nil _, agree, consistent⟩
  | cons decl decls ih =>
    simp only [MatchProg.collectDeclBindings, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at collected
    obtain ⟨middleContext, hdecl, hrest⟩ := collected
    obtain ⟨middle, hrealizes, hagree, hconsistent⟩ := MatchDecl.realizes_of_collectBindings decl hdecl
      (equations decl (by simp)) (safe decl (by simp)) (rootResults decl (by simp)) agree consistent
    obtain ⟨final, htail, hfinal, hfinalConsistent⟩ := ih hrest
      (fun decl hd => equations decl (by simp [hd]))
      (fun decl hd => safe decl (by simp [hd]))
      (fun decl hd => rootResults decl (by simp [hd])) hagree hconsistent
    exact ⟨final, .cons hrealizes htail, hfinal, hfinalConsistent⟩

theorem HandleContext.agreesOn_empty (ignored : List Nat) (target : SemanticAssignment) :
    HandleContext.empty.AgreesOn ignored SemanticAssignment.empty target := by
  intro kind handle _ hrequired _
  simp [HandleContext.require, HandleContext.empty, HandleContext.lookup,
    HandleContext.lookup.lookupBindings] at hrequired

/-- Concrete execution equations for the binding-order declarations instantiate matcher semantics. -/
theorem MatchProg.realizes_of_collectDeclBindings {prog : MatchProg OpCode α}
    {target : SemanticAssignment} {after : HandleContext} {ignored : List Nat}
    (collected : MatchProg.collectDeclBindings prog.bindingDecls HandleContext.empty = some after)
    (equations : ∀ decl ∈ prog.bindingDecls, MatchDecl.TargetConstraints prog.rootHandle target decl)
    (safe : ∀ decl ∈ prog.bindingDecls, MatchDecl.Avoids ignored decl)
    (rootResults : ∀ decl ∈ prog.bindingDecls,
      ∀ code operands types matcher propertyHandle opHandle results count,
      decl = .operation code operands types matcher propertyHandle opHandle results count →
      opHandle = prog.rootHandle → ∀ handle ∈ results, handle.id ∈ ignored) :
    ∃ final, MatchProg.Realizes prog final ∧ after.AgreesOn ignored final target ∧
      final.AgreesWith target :=
  MatchProg.realizesDecls_of_collectDeclBindings _ collected equations safe rootResults
    (HandleContext.agreesOn_empty ignored target) (SemanticAssignment.AgreesWith.empty target)

/-- A successful matcher yields a realized semantic assignment from explicit execution equations. -/
theorem MatchProg.realizes_of_run {prog : MatchProg OpCode α}
    {ctx : IRContext OpCode} {root : OperationPtr} {concrete : Assignment OpCode}
    {after : HandleContext} {ignored : List Nat} (resolve : ValuePtr → Option RuntimeValue)
    (run : prog.run ctx root = some concrete)
    (collected : MatchProg.collectDeclBindings prog.bindingDecls HandleContext.empty = some after)
    (equations : ∀ decl ∈ prog.decls,
      MatchDecl.RuntimeEquations ctx prog.rootHandle resolve concrete decl)
    (safe : ∀ decl ∈ prog.bindingDecls, MatchDecl.Avoids ignored decl)
    (rootResults : ∀ decl ∈ prog.bindingDecls,
      ∀ code operands types matcher propertyHandle opHandle results count,
      decl = .operation code operands types matcher propertyHandle opHandle results count →
      opHandle = prog.rootHandle → ∀ handle ∈ results, handle.id ∈ ignored) :
    ∃ semantic, MatchProg.Realizes prog semantic ∧
      after.AgreesOn ignored semantic (concrete.denote resolve (fun ptr => ptr.getType! ctx)) ∧
      semantic.AgreesWith (concrete.denote resolve (fun ptr => ptr.getType! ctx)) :=
  MatchProg.realizes_of_collectDeclBindings collected
    (MatchProg.targetConstraints_of_run resolve run equations) safe rootResults

/-- The replayed root uses precisely the concrete root operands, result types, and properties. -/
theorem MatchProg.rootSemantics_eq_of_agreesOn {prog : MatchProg OpCode α}
    {stage target : SemanticAssignment} {defined : HandleContext} {ignored : List Nat}
    {code : OpCode} {operands : Array (Handle OpCode .value)}
    {types : Array (Handle OpCode .type)} {matcher : propertiesOf code → Bool}
    {propertyHandle : Handle OpCode (.prop code)} {opHandle : Handle OpCode .op}
    {results : Array (Handle OpCode .value)} {count : results.size = types.size} {rest : List (MatchDecl OpCode)}
    (decls : prog.decls = .operation code operands types matcher propertyHandle opHandle results count :: rest)
    (agree : defined.AgreesOn ignored stage target)
    (operandsAvailable : defined.requireMany operands.toList = true)
    (typesAvailable : defined.requireMany types.toList = true)
    (propertyAvailable : defined.require propertyHandle = true)
    (operandsSafe : ∀ handle ∈ operands, handle.id ∉ ignored)
    (typesSafe : ∀ handle ∈ types, handle.id ∉ ignored)
    (propertySafe : propertyHandle.id ∉ ignored) (memory : MemoryState) :
    MatchProg.rootSemantics prog stage memory = MatchProg.rootSemantics prog target memory := by
  have hv := agree.getValues operands.toList operandsAvailable (by simpa using operandsSafe)
  have ht := agree.getTypes types.toList typesAvailable (by simpa using typesSafe)
  have hp := agree.getProperty propertyHandle propertyAvailable propertySafe
  simp only [MatchProg.rootSemantics, decls, hv, ht, hp]

/-- Replay a list using a prefix invariant whose one-step equations come from concrete execution.
The invariant can carry static handle availability, conformance, and opcode equation facts. -/
theorem MatchProg.realizesDecls_of_constraints
    (root : Handle OpCode .op) (target : SemanticAssignment)
    (invariant : List (MatchDecl OpCode) → SemanticAssignment → Prop)
    (step : ∀ decl rest stage, invariant (decl :: rest) stage →
      MatchDecl.Constraints root target stage decl ∧
      ∀ next, MatchDecl.Realizes root decl stage next → next.AgreesWith target →
        invariant rest next)
    (decls : List (MatchDecl OpCode)) (stage : SemanticAssignment)
    (agree : stage.AgreesWith target) (ready : invariant decls stage) :
    ∃ final, MatchProg.RealizesDecls root decls stage final ∧
      final.AgreesWith target ∧ invariant [] final := by
  induction decls generalizing stage with
  | nil => exact ⟨stage, .nil _, agree, ready⟩
  | cons decl rest ih =>
    obtain ⟨constraints, advance⟩ := step decl rest stage ready
    obtain ⟨middle, hstep, hagree⟩ := MatchDecl.realizes_of_constraints agree constraints
    obtain ⟨final, htail, hfinal, hinvariant⟩ := ih middle hagree (advance middle hstep hagree)
    exact ⟨final, .cons hstep htail, hfinal, hinvariant⟩


end CTree

end

end Veir.Puddle
