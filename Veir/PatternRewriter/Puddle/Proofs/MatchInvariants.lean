module

public import Veir.PatternRewriter.Puddle.Validity
public import Veir.Interpreter.Evaluate
public import Veir.PatternRewriter.Semantics

import Veir.Data.LLVM.Int.Lemmas
import Veir.Data.Refinement
import all Veir.Data.LLVM.Int.Basic
import Veir.Interpreter.Lemmas
import Veir.Interpreter.Refinement.Lemmas
import all Veir.Interpreter.Basic
import all Veir.Interpreter.EquationLemma
import all Veir.Interpreter.Refinement.Basic
import all Veir.IR.Basic
import all Veir.PatternRewriter.Semantics
import all Veir.Verifier.Lemmas

/-! Operational invariants established by successful Puddle matching and replacement resolution. -/

namespace Veir.Puddle

public section

variable {OpInfo : Type} [HasOpInfo OpInfo]

/-- Every concrete binding discovered by the backwards matcher is rooted at the distinguished
operation. Operation bindings are the root or strict dominators of it; value bindings dominate
the insertion point immediately before the root. -/
@[expose]
def Assignment.Rooted (assignment : Assignment OpCode)
  (ctx : WfIRContext OpCode) (root : OperationPtr) : Prop :=
  (∀ handle operation, Assignment.getOp assignment handle = some operation →
      operation.InBounds ctx.raw ∧
        (operation = root ∨ operation.ProperlyDominates root ctx true)) ∧
  (∀ handle value, Assignment.getValue assignment handle = some value →
      ∃ consumer,
        consumer.InBounds ctx.raw ∧
        (consumer = root ∨ consumer.ProperlyDominates root ctx true) ∧
        consumer.Pure ctx.raw ∧
        value ∈ consumer.getOperands! ctx.raw)

theorem Assignment.matchBind_binding
    {assignment assignment' : Assignment OpCode} {id query : Nat}
    {binding existing : Binding OpCode}
    (hbind : Assignment.matchBind assignment id binding = some assignment')
    (hget : assignment'.bindings[query]? = some (some existing)) :
    (query = id ∧ existing = binding) ∨
      assignment.bindings[query]? = some (some existing) := by
  unfold Assignment.matchBind at hbind
  split at hbind
  · split at hbind
    · simp only [Option.some.injEq] at hbind
      subst assignment'
      rw [Array.getElem?_set] at hget
      split at hget
      · simp_all
      · exact Or.inr hget
    · split at hbind <;> simp_all
  · simp at hbind

/-- `later` retains every binding already present in `earlier`. -/
@[expose]
def Assignment.Extends (earlier later : Assignment OpCode) : Prop :=
  ∀ (id : Nat) (binding : Binding OpCode), earlier.bindings[id]? = some (some binding) →
    later.bindings[id]? = some (some binding)

theorem Assignment.Extends.refl {assignment : Assignment OpCode} :
    Assignment.Extends assignment assignment := by
  intro id binding h
  exact h

theorem Assignment.Extends.trans
    {first second third : Assignment OpCode}
    (h₁ : Assignment.Extends first second) (h₂ : Assignment.Extends second third) :
    Assignment.Extends first third := by
  intro id binding h
  exact h₂ id binding (h₁ id binding h)

theorem Assignment.Extends.getBinding
    {assignment assignment' : Assignment OpCode} {id : Nat} {binding : Binding OpCode}
    (h : Assignment.Extends assignment assignment')
    (hget : assignment.getBinding id = some binding) :
    assignment'.getBinding id = some binding := by
  rw [Assignment.getBinding_eq_some_iff] at hget ⊢
  exact h id binding hget

theorem Assignment.Extends.bind
    {assignment assignment' : Assignment OpCode} {id : Nat} {binding : Binding OpCode}
    (hbind : Assignment.matchBind assignment id binding = some assignment') :
    Assignment.Extends assignment assignment' := by
  intro query existing hget
  unfold Assignment.matchBind at hbind
  split at hbind
  · split at hbind
    · simp only [Option.some.injEq] at hbind
      subst assignment'
      rw [Array.getElem?_set]
      split
      · subst query
        simp_all
      · exact hget
    · split at hbind <;> simp_all
  · simp at hbind

theorem Assignment.Extends.getOp
    {assignment assignment' : Assignment OpCode} {handle : Handle OpCode .op}
    {operation : OperationPtr}
    (h : Assignment.Extends assignment assignment')
    (hget : Assignment.getOp assignment handle = some operation) :
    Assignment.getOp assignment' handle = some operation := by
  have hbinding : assignment.getBinding handle.id = some (.op operation) := by
    unfold Assignment.getOp at hget
    split at hget <;> simp_all
  unfold Assignment.getOp
  rw [h.getBinding hbinding]

theorem Assignment.Extends.getValue
    {assignment assignment' : Assignment OpCode} {handle : Handle OpCode .value} {value : ValuePtr}
    (h : Assignment.Extends assignment assignment')
    (hget : Assignment.getValue assignment handle = some value) :
    Assignment.getValue assignment' handle = some value := by
  have hbinding : assignment.getBinding handle.id = some (.value value) := by
    unfold Assignment.getValue at hget
    split at hget <;> simp_all
  unfold Assignment.getValue
  rw [h.getBinding hbinding]

theorem Assignment.Extends.getType
    {assignment assignment' : Assignment OpCode} {handle : Handle OpCode .type} {type : TypeAttr}
    (h : Assignment.Extends assignment assignment')
    (hget : Assignment.getType assignment handle = some type) :
    Assignment.getType assignment' handle = some type := by
  have hbinding : assignment.getBinding handle.id = some (.type type) := by
    unfold Assignment.getType at hget
    split at hget <;> simp_all
  unfold Assignment.getType
  rw [h.getBinding hbinding]

theorem Assignment.Extends.getProperty
    {assignment assignment' : Assignment OpCode}
    {handle : Handle OpCode (.prop opCode)} {value : propertiesOf opCode}
    (h : Assignment.Extends assignment assignment')
    (hget : Assignment.getProperty assignment handle = some value) :
    Assignment.getProperty assignment' handle = some value := by
  unfold Assignment.getProperty at hget ⊢
  cases hslot : assignment.getBinding handle.id with
  | none => simp [hslot] at hget
  | some binding =>
    cases binding with
    | op operation => simp [hslot] at hget
    | value boundValue => simp [hslot] at hget
    | type boundType => simp [hslot] at hget
    | property actualOpCode actualValue =>
      have hlater := h.getBinding hslot
      rw [hlater]
      simpa [hslot] using hget

theorem Assignment.Rooted.bind
    {assignment assignment' : Assignment OpCode} {ctx : WfIRContext OpCode}
    {root : OperationPtr} {id : Nat} {binding : Binding OpCode}
    (h : Assignment.Rooted assignment ctx root)
    (hop : ∀ operation, binding = .op operation →
      operation.InBounds ctx.raw ∧
        (operation = root ∨ operation.ProperlyDominates root ctx true))
    (hvalue : ∀ value, binding = .value value →
      ∃ consumer,
        consumer.InBounds ctx.raw ∧
        (consumer = root ∨ consumer.ProperlyDominates root ctx true) ∧
        consumer.Pure ctx.raw ∧
        value ∈ consumer.getOperands! ctx.raw)
    (hbind : Assignment.matchBind assignment id binding = some assignment') :
    Assignment.Rooted assignment' ctx root := by
  constructor
  · intro handle operation hget
    have hgetBinding : assignment'.bindings[handle.id]? =
        some (some (.op operation)) := by
      apply (Assignment.getBinding_eq_some_iff _ _ _).mp
      unfold Assignment.getOp at hget
      split at hget <;> simp_all
    have hbinding := Assignment.matchBind_binding hbind hgetBinding
    rcases hbinding with ⟨_, hEq⟩ | hold
    · exact hop operation hEq.symm
    · apply h.1 handle operation
      simp [Assignment.getOp, Assignment.getBinding, hold]
  · intro handle value hget
    have hgetBinding : assignment'.bindings[handle.id]? =
        some (some (.value value)) := by
      apply (Assignment.getBinding_eq_some_iff _ _ _).mp
      unfold Assignment.getValue at hget
      split at hget <;> simp_all
    have hbinding := Assignment.matchBind_binding hbind hgetBinding
    rcases hbinding with ⟨_, hEq⟩ | hold
    · exact hvalue value hEq.symm
    · apply h.2 handle value
      simp [Assignment.getValue, Assignment.getBinding, hold]

theorem Assignment.Rooted.empty (size : Nat) :
    Assignment.Rooted (Assignment.empty OpCode size) ctx root := by
  grind [Assignment.Rooted, Assignment.empty, Assignment.getBinding,
    Assignment.getOp, Assignment.getValue]

theorem Assignment.Rooted.bindType
    {assignment assignment' : Assignment OpCode} {ctx : WfIRContext OpCode}
    {root : OperationPtr} {handle : Handle OpCode .type} {type : TypeAttr}
    (h : Assignment.Rooted assignment ctx root)
    (hbind : Assignment.matchBindType assignment handle type = some assignment') :
    Assignment.Rooted assignment' ctx root := by
  exact h.bind (by simp) (by simp) hbind

theorem Assignment.Rooted.bindProperty
    {assignment assignment' : Assignment OpCode} {ctx : WfIRContext OpCode}
    {root : OperationPtr} {handle : Handle OpCode (.prop opCode)} {value : propertiesOf opCode}
    (h : Assignment.Rooted assignment ctx root)
    (hbind : Assignment.matchBindProperty assignment handle value = some assignment') :
    Assignment.Rooted assignment' ctx root := by
  exact h.bind (by simp) (by simp) hbind

theorem Assignment.Rooted.bindOp
    {assignment assignment' : Assignment OpCode} {ctx : WfIRContext OpCode}
    {root operation : OperationPtr} {handle : Handle OpCode .op}
    (h : Assignment.Rooted assignment ctx root)
    (hop : operation.InBounds ctx.raw ∧
      (operation = root ∨ operation.ProperlyDominates root ctx true))
    (hbind : Assignment.matchBindOp assignment handle operation = some assignment') :
    Assignment.Rooted assignment' ctx root := by
  exact h.bind (by simpa using hop) (by simp) hbind

theorem Assignment.Rooted.bindValue
    {assignment assignment' : Assignment OpCode} {ctx : WfIRContext OpCode}
    {root : OperationPtr} {handle : Handle OpCode .value} {value : ValuePtr}
    (h : Assignment.Rooted assignment ctx root)
    (hvalue : ∃ consumer,
      consumer.InBounds ctx.raw ∧
      (consumer = root ∨ consumer.ProperlyDominates root ctx true) ∧
      consumer.Pure ctx.raw ∧
      value ∈ consumer.getOperands! ctx.raw)
    (hbind : Assignment.matchBindValue assignment handle value = some assignment') :
    Assignment.Rooted assignment' ctx root := by
  exact h.bind (by simp) (by simpa using hvalue) hbind

theorem Assignment.Rooted.bindTypes
    {assignment assignment' : Assignment OpCode} {ctx : WfIRContext OpCode}
    {root : OperationPtr} {handles : List (Handle OpCode .type)} {types : List TypeAttr}
    (h : Assignment.Rooted assignment ctx root)
    (hbind : Assignment.matchBindTypes assignment handles types = some assignment') :
    Assignment.Rooted assignment' ctx root := by
  induction handles generalizing assignment assignment' types with
  | nil => cases types <;> simp [Assignment.matchBindTypes] at hbind <;> subst_vars <;> assumption
  | cons handle handles ih =>
    cases types with
    | nil => simp [Assignment.matchBindTypes] at hbind
    | cons type types =>
      change (Assignment.matchBindType assignment handle type).bind
        (fun assignment => Assignment.matchBindTypes assignment handles types) = some assignment' at hbind
      rw [Option.bind_eq_some_iff] at hbind
      obtain ⟨assignment₁, htype, hrest⟩ := hbind
      exact ih (h.bindType htype) hrest

theorem Assignment.Rooted.bindValues
    {assignment assignment' : Assignment OpCode} {ctx : WfIRContext OpCode}
    {root operation : OperationPtr} {handles : List (Handle OpCode .value)} {values : List ValuePtr}
    (h : Assignment.Rooted assignment ctx root)
    (hconsumer : operation.InBounds ctx.raw ∧
      (operation = root ∨ operation.ProperlyDominates root ctx true))
    (hpure : operation.Pure ctx.raw)
    (hvalues : ∀ value ∈ values, value ∈ operation.getOperands! ctx.raw)
    (hbind : Assignment.matchBindValues assignment handles values = some assignment') :
    Assignment.Rooted assignment' ctx root := by
  induction handles generalizing assignment assignment' values with
  | nil => cases values <;> simp [Assignment.matchBindValues] at hbind <;> subst_vars <;> assumption
  | cons handle handles ih =>
    cases values with
    | nil => simp [Assignment.matchBindValues] at hbind
    | cons value values =>
      change (Assignment.matchBindValue assignment handle value).bind
        (fun assignment => Assignment.matchBindValues assignment handles values) = some assignment' at hbind
      rw [Option.bind_eq_some_iff] at hbind
      obtain ⟨assignment₁, hvalue, hrest⟩ := hbind
      apply ih (values := values)
        (h.bindValue ⟨operation, hconsumer.1, hconsumer.2, hpure,
          hvalues value (by simp)⟩ hvalue)
      · intro v hv
        exact hvalues v (by simp [hv])
      · exact hrest

theorem Assignment.Extends.bindType
    {assignment assignment' : Assignment OpCode} {handle : Handle OpCode .type} {type : TypeAttr}
    (h : Assignment.matchBindType assignment handle type = some assignment') :
    Assignment.Extends assignment assignment' :=
  .bind h

theorem Assignment.Extends.bindProperty
    {assignment assignment' : Assignment OpCode}
    {handle : Handle OpCode (.prop opCode)} {value : propertiesOf opCode}
    (h : Assignment.matchBindProperty assignment handle value = some assignment') :
    Assignment.Extends assignment assignment' :=
  .bind h

theorem Assignment.Extends.bindOp
    {assignment assignment' : Assignment OpCode} {handle : Handle OpCode .op}
    {operation : OperationPtr}
    (h : Assignment.matchBindOp assignment handle operation = some assignment') :
    Assignment.Extends assignment assignment' :=
  .bind h

theorem Assignment.Extends.bindValue
    {assignment assignment' : Assignment OpCode} {handle : Handle OpCode .value} {value : ValuePtr}
    (h : Assignment.matchBindValue assignment handle value = some assignment') :
    Assignment.Extends assignment assignment' := by
  exact .bind h

theorem Assignment.Extends.bindTypes
    {assignment assignment' : Assignment OpCode} {handles : List (Handle OpCode .type)}
    {types : List TypeAttr}
    (h : Assignment.matchBindTypes assignment handles types = some assignment') :
    Assignment.Extends assignment assignment' := by
  induction handles generalizing assignment assignment' types with
  | nil => cases types <;> simp [Assignment.matchBindTypes] at h <;> subst_vars <;> exact .refl
  | cons handle handles ih =>
    cases types with
    | nil => simp [Assignment.matchBindTypes] at h
    | cons type types =>
      change (Assignment.matchBindType assignment handle type).bind
        (fun assignment => Assignment.matchBindTypes assignment handles types) = some assignment' at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨assignment₁, htype, hrest⟩ := h
      exact (Assignment.Extends.bindType htype).trans (ih hrest)

theorem Assignment.Extends.bindValues
    {assignment assignment' : Assignment OpCode} {handles : List (Handle OpCode .value)}
    {values : List ValuePtr}
    (h : Assignment.matchBindValues assignment handles values = some assignment') :
    Assignment.Extends assignment assignment' := by
  induction handles generalizing assignment assignment' values with
  | nil => cases values <;> simp [Assignment.matchBindValues] at h <;> subst_vars <;> exact .refl
  | cons handle handles ih =>
    cases values with
    | nil => simp [Assignment.matchBindValues] at h
    | cons value values =>
      change (Assignment.matchBindValue assignment handle value).bind
        (fun assignment => Assignment.matchBindValues assignment handles values) = some assignment' at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨assignment₁, hvalue, hrest⟩ := h
      exact (Assignment.Extends.bindValue hvalue).trans (ih hrest)

theorem Assignment.matchBind_get
    {assignment after : Assignment OpCode} {id : Nat} {binding : Binding OpCode}
    (hbind : Assignment.matchBind assignment id binding = some after) :
    after.bindings[id]? = some (some binding) := by
  simp [Assignment.matchBind] at hbind
  obtain ⟨hId, hbind⟩ := hbind
  cases hslot : assignment.bindings[id] with
  | none =>
    rw [hslot] at hbind
    simp only [Option.some.injEq] at hbind
    subst after
    simp
  | some existing =>
    rw [hslot] at hbind
    by_cases heq : existing = binding
    · simp [heq] at hbind
      subst after
      rw [Array.getElem?_eq_getElem hId, hslot, heq]
    · simp [heq] at hbind

theorem Assignment.matchBindOp_get
    {assignment after : Assignment OpCode} {handle : Handle OpCode .op} {operation : OperationPtr}
    (hbind : Assignment.matchBindOp assignment handle operation = some after) :
    Assignment.getOp after handle = some operation := by
  have h := Assignment.matchBind_get hbind
  simp [Assignment.getOp, Assignment.getBinding, h]

theorem Assignment.matchBindProperty_get
    {assignment after : Assignment OpCode}
    {handle : Handle OpCode (.prop opCode)} {value : propertiesOf opCode}
    (hbind : Assignment.matchBindProperty assignment handle value = some after) :
    Assignment.getProperty after handle = some value := by
  have h := Assignment.matchBind_get hbind
  simp [Assignment.getProperty, Assignment.getBinding, h]

theorem Assignment.matchGetOrBindOp_extends
    {assignment : Assignment OpCode} {ctx : IRContext OpCode}
    {opHandle : Handle OpCode .op} {results : Array (Handle OpCode .value)}
    {found : OperationPtr × Assignment OpCode}
    (hfound : Assignment.matchGetOrBindOp assignment ctx opHandle results = some found) :
    Assignment.Extends assignment found.2 := by
  unfold Assignment.matchGetOrBindOp at hfound
  cases hget : Assignment.getOp assignment opHandle with
  | some concrete => simp [hget] at hfound; subst found; exact .refl
  | none =>
    rw [hget] at hfound
    cases hresult : results[0]? with
    | none => simp [hresult] at hfound
    | some resultHandle =>
      cases hvalue : Assignment.getValue assignment resultHandle with
      | none => simp [hresult, hvalue] at hfound
      | some value =>
        cases value with
        | blockArgument ptr => simp [hresult, hvalue] at hfound
        | opResult resultPtr =>
          by_cases hindex : resultPtr.index = 0
          · cases hbind : Assignment.matchBindOp assignment opHandle resultPtr.op with
            | none => simp [hresult, hvalue, hindex, hbind] at hfound
            | some bound =>
              simp [hresult, hvalue, hindex, hbind] at hfound
              subst found
              exact .bindOp hbind
          · simp [hresult, hvalue, hindex] at hfound

theorem Assignment.matchGetOrBindOp_getOp
    {assignment : Assignment OpCode} {ctx : IRContext OpCode}
    {opHandle : Handle OpCode .op} {results : Array (Handle OpCode .value)}
    {found : OperationPtr × Assignment OpCode}
    (hfound : Assignment.matchGetOrBindOp assignment ctx opHandle results = some found) :
    Assignment.getOp found.2 opHandle = some found.1 := by
  unfold Assignment.matchGetOrBindOp at hfound
  cases hget : Assignment.getOp assignment opHandle with
  | some concrete => simp [hget] at hfound; subst found; exact hget
  | none =>
    rw [hget] at hfound
    cases hresult : results[0]? with
    | none => simp [hresult] at hfound
    | some resultHandle =>
      cases hvalue : Assignment.getValue assignment resultHandle with
      | none => simp [hresult, hvalue] at hfound
      | some value =>
        cases value with
        | blockArgument ptr => simp [hresult, hvalue] at hfound
        | opResult resultPtr =>
          by_cases hindex : resultPtr.index = 0
          · cases hbind : Assignment.matchBindOp assignment opHandle resultPtr.op with
            | none => simp [hresult, hvalue, hindex, hbind] at hfound
            | some bound =>
              simp [hresult, hvalue, hindex, hbind] at hfound
              subst found
              exact Assignment.matchBindOp_get hbind
          · simp [hresult, hvalue, hindex] at hfound

theorem Assignment.matchCheckOperationResult_getValue
    {assignment : Assignment OpCode} {operation : OperationPtr}
    {results : Array (Handle OpCode .value)} {resultHandle : Handle OpCode .value}
    (hresult : results[0]? = some resultHandle)
    (hcheck : Assignment.matchCheckOperationResult assignment operation results = some ()) :
    Assignment.getValue assignment resultHandle = some (.opResult (operation.getResult 0)) := by
  unfold Assignment.matchCheckOperationResult at hcheck
  rw [hresult] at hcheck
  cases hvalue : Assignment.getValue assignment resultHandle with
  | none => simp [hvalue] at hcheck
  | some value =>
    have : value = .opResult (operation.getResult 0) := by
      simpa [hvalue, _root_.guard] using hcheck
    subst value
    rfl

theorem Assignment.Rooted.getOrBindOp
    {assignment : Assignment OpCode} {ctx : WfIRContext OpCode}
    {root : OperationPtr} {opHandle : Handle OpCode .op}
    {results : Array (Handle OpCode .value)} {found : OperationPtr × Assignment OpCode}
    (ctxDom : ctx.Dom) (h : Assignment.Rooted assignment ctx root)
    (hfound : Assignment.matchGetOrBindOp assignment ctx.raw opHandle results = some found) :
    Assignment.Rooted found.2 ctx root ∧
      found.1.InBounds ctx.raw ∧
        (found.1 = root ∨ found.1.ProperlyDominates root ctx true) := by
  unfold Assignment.matchGetOrBindOp at hfound
  cases hget : Assignment.getOp assignment opHandle with
  | some concrete =>
    simp [hget] at hfound
    subst found
    exact ⟨h, h.1 opHandle concrete hget⟩
  | none =>
    rw [hget] at hfound
    cases hresult : results[0]? with
    | none => simp [hresult] at hfound
    | some resultHandle =>
      cases hvalue : Assignment.getValue assignment resultHandle with
      | none => simp [hresult, hvalue] at hfound
      | some value =>
        cases value with
        | blockArgument ptr => simp [hresult, hvalue] at hfound
        | opResult resultPtr =>
          by_cases hindex : resultPtr.index = 0
          · cases hbind : Assignment.matchBindOp assignment opHandle resultPtr.op with
            | none => simp [hresult, hvalue, hindex, hbind] at hfound
            | some bound =>
              simp [hresult, hvalue, hindex, hbind] at hfound
              subst found
              obtain ⟨consumer, hconsumerIn, hconsumer, _, hmem⟩ :=
                h.2 resultHandle (.opResult resultPtr) hvalue
              have hdefDom : resultPtr.op.ProperlyDominates consumer ctx true :=
                OperationPtr.properlyDominates_of_definingOp?_of_mem_getOperands!
                  ctxDom ValuePtr.definingOp?_opResult hmem
              have hdefIn : resultPtr.op.InBounds ctx.raw := by grind
              have hopRooted : resultPtr.op.InBounds ctx.raw ∧
                    (resultPtr.op = root ∨ resultPtr.op.ProperlyDominates root ctx true) := by
                  refine ⟨hdefIn, Or.inr ?_⟩
                  rcases hconsumer with rfl | hconsumer
                  · exact hdefDom
                  · exact OperationPtr.properlyDominates_trans hdefDom hconsumer
              exact ⟨h.bindOp hopRooted hbind, hopRooted⟩
          · simp [hresult, hvalue, hindex] at hfound



theorem Assignment.Rooted.matchDecl
    {assignment assignment' : Assignment OpCode} {ctx : WfIRContext OpCode}
    {root : OperationPtr} {decl : MatchDecl OpCode} (ctxDom : ctx.Dom)
    (rootInBounds : root.InBounds ctx.raw)
    (h : Assignment.Rooted assignment ctx root)
    (hsupported : decl.Supported)
    (hmatch : decl.match ctx.raw root assignment = some assignment') :
    Assignment.Rooted assignment' ctx root := by
  cases decl with
  | root _ _ _ _ _ opHandle =>
    exact h.bindOp ⟨rootInBounds, Or.inl rfl⟩ hmatch
  | type matcher handle =>
    cases hget : Assignment.getType assignment handle with
    | none => simp [MatchDecl.match, hget] at hmatch
    | some actual =>
      by_cases hmatcher : matcher actual = true <;>
        simp [MatchDecl.match, hget, hmatcher, _root_.guard, pure,
          Alternative.failure] at hmatch
      subst assignment'
      exact h
  | guard inputs predicate =>
    simp only [MatchDecl.match, Option.bind_eq_bind] at hmatch
    rw [Option.bind_eq_some_iff] at hmatch
    obtain ⟨_, _, hmatch⟩ := hmatch
    rw [Option.bind_eq_some_iff] at hmatch
    obtain ⟨_, _, hmatch⟩ := hmatch
    simp only [pure, Option.some.injEq] at hmatch
    subst assignment'
    exact h
  | operation opCode operands returnTypes property propertyHandle opHandle results =>
    simp [MatchDecl.match] at hmatch
    simp only [Option.bind_eq_some_iff] at hmatch
    obtain ⟨operation, hget, _, _hcheck, _, hopcode, _, hpropertyMatch,
      propertyAssignment, hproperty, _, _hresultSize, typedAssignment, htypes,
      _, _hoperandSize, hmatch⟩ := hmatch
    obtain ⟨hbaseRooted, hopRooted⟩ := h.getOrBindOp ctxDom hget
    have hopcodeEq : operation.1.getOpType! ctx.raw = opCode := by
      simpa [_root_.guard] using hopcode
    have hopPure : operation.1.Pure ctx.raw := by
      change property.Supported operands.size returnTypes.size ∧ _ at hsupported
      apply hsupported.1.pure hopcodeEq
      simpa [_root_.guard] using hpropertyMatch
    apply ((hbaseRooted.bindProperty hproperty).bindTypes htypes).bindValues
      hopRooted hopPure ?_ hmatch
    intro value hvalue
    simpa using hvalue
  | value typeHandle handle =>
    simp [MatchDecl.match] at hmatch
    rw [Option.bind_eq_some_iff] at hmatch
    obtain ⟨_, _, htype⟩ := hmatch
    exact h.bindType htype

theorem Assignment.Extends.matchDecl
    {assignment assignment' : Assignment OpCode} {ctx : IRContext OpCode}
    {root : OperationPtr} {decl : MatchDecl OpCode}
    (hmatch : decl.match ctx root assignment = some assignment') :
    Assignment.Extends assignment assignment' := by
  cases decl with
  | root _ _ _ _ _ opHandle => exact .bindOp hmatch
  | type matcher handle =>
    cases hget : Assignment.getType assignment handle with
    | none => simp [MatchDecl.match, hget] at hmatch
    | some actual =>
      by_cases hmatcher : matcher actual = true <;>
        simp [MatchDecl.match, hget, hmatcher, _root_.guard, pure,
          Alternative.failure] at hmatch
      subst assignment'
      exact .refl
  | guard inputs predicate =>
    simp only [MatchDecl.match, Option.bind_eq_bind] at hmatch
    rw [Option.bind_eq_some_iff] at hmatch
    obtain ⟨_, _, hmatch⟩ := hmatch
    rw [Option.bind_eq_some_iff] at hmatch
    obtain ⟨_, _, hmatch⟩ := hmatch
    simp only [pure, Option.some.injEq] at hmatch
    subst assignment'
    exact .refl
  | operation opCode operands returnTypes property propertyHandle opHandle results =>
    simp [MatchDecl.match] at hmatch
    simp only [Option.bind_eq_some_iff] at hmatch
    obtain ⟨found, hfound, _, _, _, _, _, _, propertyAssignment, hproperty,
      _, _, assignment₁, htypes, _, _, hvalues⟩ := hmatch
    exact (Assignment.matchGetOrBindOp_extends hfound).trans
      ((Assignment.Extends.bindProperty hproperty).trans
        ((Assignment.Extends.bindTypes htypes).trans (.bindValues hvalues)))
  | value typeHandle handle =>
    simp [MatchDecl.match] at hmatch
    rw [Option.bind_eq_some_iff] at hmatch
    obtain ⟨_, _, htype⟩ := hmatch
    exact .bindType htype

@[expose]
def MatchDecl.Occurred (decl : MatchDecl OpCode) (ctx : IRContext OpCode)
    (root : OperationPtr) (final : Assignment OpCode) : Prop :=
  ∃ before after,
    decl.match ctx root before = some after ∧ Assignment.Extends after final

theorem MatchProg.matchDecls_postconditions
    {decls : List (MatchDecl OpCode)} {ctx : IRContext OpCode} {root : OperationPtr}
    {initial final : Assignment OpCode}
    (hmatch : MatchProg.matchDecls decls ctx root initial = some final) :
    Assignment.Extends initial final ∧
      ∀ decl ∈ decls, decl.Occurred ctx root final := by
  induction decls generalizing initial with
  | nil =>
    simp [MatchProg.matchDecls] at hmatch
    subst final
    exact ⟨.refl, by simp⟩
  | cons decl decls ih =>
    change (decl.match ctx root initial).bind
      (fun assignment => MatchProg.matchDecls decls ctx root assignment) = some final at hmatch
    rw [Option.bind_eq_some_iff] at hmatch
    obtain ⟨after, hdecl, hrest⟩ := hmatch
    obtain ⟨hext, hoccurs⟩ := ih hrest
    constructor
    · exact (Assignment.Extends.matchDecl hdecl).trans hext
    · intro query hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with hEq | hmem
      · subst query
        exact ⟨initial, after, hdecl, hext⟩
      · exact hoccurs query hmem

theorem Assignment.Rooted.matchDecls
    {assignment assignment' : Assignment OpCode} {ctx : WfIRContext OpCode}
    {root : OperationPtr} (ctxDom : ctx.Dom)
    (rootInBounds : root.InBounds ctx.raw)
    (hsupported : ∀ decl ∈ decls, decl.Supported)
    (h : Assignment.Rooted assignment ctx root)
    (hmatch : MatchProg.matchDecls decls ctx.raw root assignment = some assignment') :
    Assignment.Rooted assignment' ctx root := by
  induction decls generalizing assignment with
  | nil =>
    simp [MatchProg.matchDecls] at hmatch
    subst assignment'
    exact h
  | cons decl decls ih =>
    change (decl.match ctx.raw root assignment).bind
      (fun assignment => MatchProg.matchDecls decls ctx.raw root assignment) =
        some assignment' at hmatch
    rw [Option.bind_eq_some_iff] at hmatch
    obtain ⟨assignment₁, hdecl, hrest⟩ := hmatch
    apply ih (fun query hmem => hsupported query (by simp [hmem]))
      (h.matchDecl ctxDom rootInBounds (hsupported decl (by simp)) hdecl) hrest


theorem MatchProg.rooted_of_run
    {prog : MatchProg OpCode α} {ctx : WfIRContext OpCode} {root : OperationPtr}
    {assignment : Assignment OpCode} (ctxDom : ctx.Dom)
    (rootInBounds : root.InBounds ctx.raw)
    (hsupported : ∀ decl ∈ prog.decls, decl.Supported)
    (h : prog.run ctx.raw root = some assignment) :
    Assignment.Rooted assignment ctx root :=
  Assignment.Rooted.matchDecls ctxDom rootInBounds hsupported (.empty prog.numHandles) h

theorem Replacement.resolve_eq_some
    {replacement : Replacement OpCode} {assignment : Assignment OpCode} {ctx : IRContext OpCode}
    {root : OperationPtr} {resolved : Array ValuePtr}
    (h : replacement.resolve assignment ctx root = some resolved) :
    root.getNumResults! ctx = resolved.size ∧
      replacement.resolveValues assignment = some resolved ∧
      ∀ value ∈ resolved, value ∉ root.getResults! ctx := by
  cases hget : replacement.resolveValues assignment with
  | none => simp [Replacement.resolve, hget] at h
  | some values =>
    by_cases hnum : root.getNumResults! ctx = values.size
    · by_cases hnotOwn : ∀ value ∈ values, value ∉ root.getResults! ctx
      · simp [Replacement.resolve, hget, hnum, _root_.guard, Alternative.failure,
          bind, pure, Option.bind] at h
        rw [if_pos hnotOwn] at h
        simp at h
        subst resolved
        exact ⟨hnum, rfl, hnotOwn⟩
      · simp [Replacement.resolve, hget, hnum, hnotOwn, _root_.guard, Alternative.failure,
          bind, pure, Option.bind] at h
    · simp [Replacement.resolve, hget, hnum, _root_.guard, Alternative.failure,
        bind, pure, Option.bind] at h

theorem MatchProg.root_mem_of_root?_eq_some
    {prog : MatchProg OpCode α} (hroot : prog.root? = some rootHandle) :
    ∃ opCode operands returnTypes property propertyHandle,
      .root opCode operands returnTypes property propertyHandle rootHandle ∈ prog.decls := by
  unfold MatchProg.root? at hroot
  have aux : ∀ decls : List (MatchDecl OpCode),
      decls.findSome? (fun | .root _ _ _ _ _ root => some root | _ => none) = some rootHandle →
      ∃ opCode operands returnTypes property propertyHandle,
        .root opCode operands returnTypes property propertyHandle rootHandle ∈ decls := by
    intro decls h
    induction decls with
    | nil => simp at h
    | cons decl decls ih =>
      cases decl with
      | root opCode operands returnTypes property propertyResult result =>
        simp at h
        subst result
        exact ⟨opCode, operands, returnTypes, property, propertyResult, by simp⟩
      | value _ _ => simp_all
      | type _ _ => simp_all
      | guard _ _ => simp_all
      | operation _ _ _ _ _ _ => simp_all
  exact aux prog.decls hroot

theorem Assignment.matchBindValue_get
    {assignment after : Assignment OpCode} {handle : Handle OpCode .value} {value : ValuePtr}
    (hbind : Assignment.matchBindValue assignment handle value = some after) :
    Assignment.getValue after handle = some value := by
  have h := Assignment.matchBind_get hbind
  simp [Assignment.getValue, Assignment.getBinding, h]


theorem MatchDecl.Occurred.root_getOp
    {opCode : OpCode} {operands : Array (Handle OpCode .value)}
    {returnTypes : Array (Handle OpCode .type)} {property : PropertyMatcher opCode}
    {propertyHandle : Handle OpCode (.prop opCode)}
    {handle : Handle OpCode .op} {ctx : IRContext OpCode} {rootOp : OperationPtr}
    {final : Assignment OpCode}
    (h : (MatchDecl.root opCode operands returnTypes property propertyHandle handle).Occurred
      ctx rootOp final) :
    Assignment.getOp final handle = some rootOp := by
  obtain ⟨before, after, hmatch, hext⟩ := h
  exact hext.getOp (Assignment.matchBindOp_get hmatch)

theorem MatchProg.supported_root_of_run
    {prog : MatchProg OpCode α} (hsupported : prog.Supported)
    {ctx : IRContext OpCode} {rootOp : OperationPtr} {assignment : Assignment OpCode}
    (hrootMem : .root opCode operands returnTypes property propertyHandle rootHandle ∈ prog.decls)
    (hrun : prog.run ctx rootOp = some assignment) :
    HasOpInfo.isTerminator (rootOp.getOpType! ctx) = false := by
  have hoperationMem :=
    hsupported.2.1 opCode operands returnTypes property propertyHandle rootHandle hrootMem
  have hoccurs := (MatchProg.matchDecls_postconditions hrun).2
  have hrootGet :=
    (hoccurs (.root opCode operands returnTypes property propertyHandle rootHandle)
      hrootMem).root_getOp
  obtain ⟨before, after, hmatch, hext⟩ :=
    hoccurs (.operation opCode operands returnTypes property propertyHandle rootHandle #[])
      hoperationMem
  have hbeforeExtendsFinal := (Assignment.Extends.matchDecl hmatch).trans hext
  simp [MatchDecl.match] at hmatch
  simp only [Option.bind_eq_some_iff] at hmatch
  obtain ⟨operation, hget, _, _, _, hopcode, _, _, _, hproperty, _, _, _, htypes,
    _, _, hvalues⟩ := hmatch
  have hoperationExtendsFinal :=
    (Assignment.Extends.bindProperty hproperty).trans
      ((Assignment.Extends.bindTypes htypes).trans
        ((Assignment.Extends.bindValues hvalues).trans hext))
  have hoperationGet := hoperationExtendsFinal.getOp
    (Assignment.matchGetOrBindOp_getOp hget)
  have hopEq : operation.1 = rootOp := by grind
  have hopcodeEq : rootOp.getOpType! ctx = opCode := by
    simpa [_root_.guard, hopEq] using hopcode
  rw [hopcodeEq]
  exact hsupported.2.2 opCode operands returnTypes property propertyHandle rootHandle hrootMem

theorem MatchProg.supported_operation_of_run
    {prog : MatchProg OpCode α} (hsupported : prog.Supported)
    {ctx : IRContext OpCode} {rootOp operation : OperationPtr}
    {assignment : Assignment OpCode} {handle : Handle OpCode .op}
    {opCode : OpCode} {operands : Array (Handle OpCode .value)}
    {returnTypes : Array (Handle OpCode .type)} {property : PropertyMatcher opCode}
    {propertyHandle : Handle OpCode (.prop opCode)}
    {results : Array (Handle OpCode .value)}
    (hoperationMem : .operation opCode operands returnTypes property propertyHandle handle results ∈
      prog.decls)
    (hrun : prog.run ctx rootOp = some assignment)
    (hfinalGet : Assignment.getOp assignment handle = some operation) :
    operation.Pure ctx := by
  obtain ⟨before, after, hmatch, hext⟩ :=
    (MatchProg.matchDecls_postconditions hrun).2
      (.operation opCode operands returnTypes property propertyHandle handle results) hoperationMem
  have hbeforeExtendsFinal := (Assignment.Extends.matchDecl hmatch).trans hext
  simp [MatchDecl.match] at hmatch
  simp only [Option.bind_eq_some_iff] at hmatch
  obtain ⟨concrete, hget, _, _hcheck, _, hopcode, _, hpropertyMatch,
    _, hproperty, _, _hresultSize, _, htypes, _, _hoperandSize, hvalues⟩ := hmatch
  have hconcreteExtendsFinal :=
    (Assignment.Extends.bindProperty hproperty).trans
      ((Assignment.Extends.bindTypes htypes).trans
        ((Assignment.Extends.bindValues hvalues).trans hext))
  have hconcreteGet := hconcreteExtendsFinal.getOp
    (Assignment.matchGetOrBindOp_getOp hget)
  have hEq : concrete.1 = operation := by grind
  have hopcodeEq : operation.getOpType! ctx = opCode := by
    simpa [_root_.guard, hEq] using hopcode
  have hpropertySupported :=
    hsupported.1
      (.operation opCode operands returnTypes property propertyHandle handle results) hoperationMem
  change property.Supported operands.size returnTypes.size ∧ _
    at hpropertySupported
  apply hpropertySupported.1.pure hopcodeEq
  simpa [_root_.guard, hEq] using hpropertyMatch


end

end Veir.Puddle
