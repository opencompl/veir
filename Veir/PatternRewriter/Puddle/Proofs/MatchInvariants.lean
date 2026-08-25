module

public import Veir.PatternRewriter.Puddle.Proofs.Validity
public import Veir.PatternRewriter.Puddle.Proofs.Assignment
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
        (value ∈ consumer.getOperands! ctx.raw ∨
          value ∈ consumer.getResults! ctx.raw))

theorem Assignment.bind_binding
    {assignment assignment' : Assignment OpCode} {handleType : HandleType OpCode}
    {handle : Handle OpCode handleType} {query : Nat} {binding existing : Binding OpCode}
    (hbind : Assignment.bind assignment handle binding = some assignment')
    (hget : assignment'.bindings[query]? = some (some existing)) :
    (query = handle.id ∧ existing = binding) ∨
      assignment.bindings[query]? = some (some existing) := by
  by_cases heq : query = handle.id
  · exact Or.inl ⟨heq, by
      subst query
      have hnew := Assignment.bind_get hbind
      rw [hnew] at hget
      simp_all⟩
  · apply Or.inr
    have hjoined : assignment'.bindings[query]?.join = some existing := by
      simp [hget]
    rw [Assignment.bind_get_of_ne hbind heq] at hjoined
    exact Option.join_eq_some_iff.mp hjoined

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
    {assignment assignment' : Assignment OpCode} {handleType : HandleType OpCode}
    {handle : Handle OpCode handleType} {binding : Binding OpCode}
    (h : Assignment.Extends assignment assignment')
    (hget : assignment.getBinding handle = some binding) :
    assignment'.getBinding handle = some binding := by
  rw [Assignment.getBinding_eq_some_iff] at hget ⊢
  exact h handle.id binding hget

theorem Assignment.Extends.bind
    {assignment assignment' : Assignment OpCode} {handleType : HandleType OpCode}
    {handle : Handle OpCode handleType} {binding : Binding OpCode}
    (hbind : Assignment.bind assignment handle binding = some assignment') :
    Assignment.Extends assignment assignment' := by
  intro query existing hget
  unfold Assignment.bind at hbind
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
  · rename_i hout
    simp only [Option.some.injEq] at hbind
    subst assignment'
    obtain ⟨hquery, hvalue⟩ := Array.getElem?_eq_some_iff.mp hget
    rw [Array.push_eq_append]
    simp [Array.getElem?_append, hquery, hvalue]

theorem Assignment.Extends.getOp
    {assignment assignment' : Assignment OpCode} {handle : Handle OpCode .op}
    {operation : OperationPtr}
    (h : Assignment.Extends assignment assignment')
    (hget : Assignment.getOp assignment handle = some operation) :
    Assignment.getOp assignment' handle = some operation := by
  have hbinding : assignment.getBinding handle = some (.op operation) := by
    unfold Assignment.getOp at hget
    split at hget <;> simp_all
  unfold Assignment.getOp
  rw [h.getBinding hbinding]

theorem Assignment.Extends.getValue
    {assignment assignment' : Assignment OpCode} {handle : Handle OpCode .value} {value : ValuePtr}
    (h : Assignment.Extends assignment assignment')
    (hget : Assignment.getValue assignment handle = some value) :
    Assignment.getValue assignment' handle = some value := by
  have hbinding : assignment.getBinding handle = some (.value value) := by
    unfold Assignment.getValue at hget
    split at hget <;> simp_all
  unfold Assignment.getValue
  rw [h.getBinding hbinding]

theorem Assignment.Extends.getType
    {assignment assignment' : Assignment OpCode} {handle : Handle OpCode .type} {type : TypeAttr}
    (h : Assignment.Extends assignment assignment')
    (hget : Assignment.getType assignment handle = some type) :
    Assignment.getType assignment' handle = some type := by
  have hbinding : assignment.getBinding handle = some (.type type) := by
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
  cases hslot : assignment.getBinding handle with
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
    {root : OperationPtr} {handleType : HandleType OpCode}
    {bound : Handle OpCode handleType} {binding : Binding OpCode}
    (h : Assignment.Rooted assignment ctx root)
    (hop : ∀ operation, binding = .op operation →
      operation.InBounds ctx.raw ∧
        (operation = root ∨ operation.ProperlyDominates root ctx true))
    (hvalue : ∀ value, binding = .value value →
      ∃ consumer,
        consumer.InBounds ctx.raw ∧
        (consumer = root ∨ consumer.ProperlyDominates root ctx true) ∧
        consumer.Pure ctx.raw ∧
        (value ∈ consumer.getOperands! ctx.raw ∨
          value ∈ consumer.getResults! ctx.raw))
    (hbind : Assignment.bind assignment bound binding = some assignment') :
    Assignment.Rooted assignment' ctx root := by
  constructor
  · intro handle operation hget
    have hgetBinding : assignment'.bindings[handle.id]? =
        some (some (.op operation)) := by
      apply (Assignment.getBinding_eq_some_iff _ _ _).mp
      unfold Assignment.getOp at hget
      split at hget <;> simp_all
    have hbinding := Assignment.bind_binding hbind hgetBinding
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
    have hbinding := Assignment.bind_binding hbind hgetBinding
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
    (hbind : Assignment.bindType assignment handle type = some assignment') :
    Assignment.Rooted assignment' ctx root := by
  exact h.bind (by simp) (by simp) hbind

theorem Assignment.Rooted.bindProperty
    {assignment assignment' : Assignment OpCode} {ctx : WfIRContext OpCode}
    {root : OperationPtr} {handle : Handle OpCode (.prop opCode)} {value : propertiesOf opCode}
    (h : Assignment.Rooted assignment ctx root)
    (hbind : Assignment.bindProperty assignment handle value = some assignment') :
    Assignment.Rooted assignment' ctx root := by
  exact h.bind (by simp) (by simp) hbind

theorem Assignment.Rooted.bindOp
    {assignment assignment' : Assignment OpCode} {ctx : WfIRContext OpCode}
    {root operation : OperationPtr} {handle : Handle OpCode .op}
    (h : Assignment.Rooted assignment ctx root)
    (hop : operation.InBounds ctx.raw ∧
      (operation = root ∨ operation.ProperlyDominates root ctx true))
    (hbind : Assignment.bindOp assignment handle operation = some assignment') :
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
      (value ∈ consumer.getOperands! ctx.raw ∨
        value ∈ consumer.getResults! ctx.raw))
    (hbind : Assignment.bindValue assignment handle value = some assignment') :
    Assignment.Rooted assignment' ctx root := by
  exact h.bind (by simp) (by simpa using hvalue) hbind

theorem Assignment.Rooted.bindTypes
    {assignment assignment' : Assignment OpCode} {ctx : WfIRContext OpCode}
    {root : OperationPtr} {handles : List (Handle OpCode .type)} {types : List TypeAttr}
    (h : Assignment.Rooted assignment ctx root)
    (hbind : Assignment.bindTypes assignment handles types = some assignment') :
    Assignment.Rooted assignment' ctx root := by
  induction handles generalizing assignment assignment' types with
  | nil => cases types <;> simp [Assignment.bindTypes] at hbind <;> subst_vars <;> assumption
  | cons handle handles ih =>
    cases types with
    | nil => simp [Assignment.bindTypes] at hbind
    | cons type types =>
      change (Assignment.bindType assignment handle type).bind
        (fun assignment => Assignment.bindTypes assignment handles types) = some assignment' at hbind
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
    (hvalues : ∀ value ∈ values,
      value ∈ operation.getOperands! ctx.raw ∨ value ∈ operation.getResults! ctx.raw)
    (hbind : Assignment.bindValues assignment handles values = some assignment') :
    Assignment.Rooted assignment' ctx root := by
  induction handles generalizing assignment assignment' values with
  | nil => cases values <;> simp [Assignment.bindValues] at hbind <;> subst_vars <;> assumption
  | cons handle handles ih =>
    cases values with
    | nil => simp [Assignment.bindValues] at hbind
    | cons value values =>
      change (Assignment.bindValue assignment handle value).bind
        (fun assignment => Assignment.bindValues assignment handles values) = some assignment' at hbind
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
    (h : Assignment.bindType assignment handle type = some assignment') :
    Assignment.Extends assignment assignment' :=
  .bind h

theorem Assignment.Extends.bindProperty
    {assignment assignment' : Assignment OpCode}
    {handle : Handle OpCode (.prop opCode)} {value : propertiesOf opCode}
    (h : Assignment.bindProperty assignment handle value = some assignment') :
    Assignment.Extends assignment assignment' :=
  .bind h

theorem Assignment.Extends.bindOp
    {assignment assignment' : Assignment OpCode} {handle : Handle OpCode .op}
    {operation : OperationPtr}
    (h : Assignment.bindOp assignment handle operation = some assignment') :
    Assignment.Extends assignment assignment' :=
  .bind h

theorem Assignment.Extends.bindValue
    {assignment assignment' : Assignment OpCode} {handle : Handle OpCode .value} {value : ValuePtr}
    (h : Assignment.bindValue assignment handle value = some assignment') :
    Assignment.Extends assignment assignment' := by
  exact .bind h

theorem Assignment.Extends.bindTypes
    {assignment assignment' : Assignment OpCode} {handles : List (Handle OpCode .type)}
    {types : List TypeAttr}
    (h : Assignment.bindTypes assignment handles types = some assignment') :
    Assignment.Extends assignment assignment' := by
  induction handles generalizing assignment assignment' types with
  | nil => cases types <;> simp [Assignment.bindTypes] at h <;> subst_vars <;> exact .refl
  | cons handle handles ih =>
    cases types with
    | nil => simp [Assignment.bindTypes] at h
    | cons type types =>
      change (Assignment.bindType assignment handle type).bind
        (fun assignment => Assignment.bindTypes assignment handles types) = some assignment' at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨assignment₁, htype, hrest⟩ := h
      exact (Assignment.Extends.bindType htype).trans (ih hrest)

theorem Assignment.Extends.bindValues
    {assignment assignment' : Assignment OpCode} {handles : List (Handle OpCode .value)}
    {values : List ValuePtr}
    (h : Assignment.bindValues assignment handles values = some assignment') :
    Assignment.Extends assignment assignment' := by
  induction handles generalizing assignment assignment' values with
  | nil => cases values <;> simp [Assignment.bindValues] at h <;> subst_vars <;> exact .refl
  | cons handle handles ih =>
    cases values with
    | nil => simp [Assignment.bindValues] at h
    | cons value values =>
      change (Assignment.bindValue assignment handle value).bind
        (fun assignment => Assignment.bindValues assignment handles values) = some assignment' at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨assignment₁, hvalue, hrest⟩ := h
      exact (Assignment.Extends.bindValue hvalue).trans (ih hrest)

theorem Assignment.bindOp_get
    {assignment after : Assignment OpCode} {handle : Handle OpCode .op} {operation : OperationPtr}
    (hbind : Assignment.bindOp assignment handle operation = some after) :
    Assignment.getOp after handle = some operation := by
  have h := Assignment.bind_get hbind
  simp [Assignment.getOp, Assignment.getBinding, h]

theorem Assignment.bindProperty_get
    {assignment after : Assignment OpCode}
    {handle : Handle OpCode (.prop opCode)} {value : propertiesOf opCode}
    (hbind : Assignment.bindProperty assignment handle value = some after) :
    Assignment.getProperty after handle = some value := by
  have h := Assignment.bind_get hbind
  simp [Assignment.getProperty, Assignment.getBinding, h]

theorem Assignment.Rooted.findOp
    {assignment : Assignment OpCode} {ctx : WfIRContext OpCode}
    {root : OperationPtr} {opHandle : Handle OpCode .op}
    {results : Array (Handle OpCode .value)} {found : OperationPtr}
    (ctxDom : ctx.Dom) (h : Assignment.Rooted assignment ctx root)
    (hfound : Assignment.findOp assignment opHandle results = some found) :
    found.InBounds ctx.raw ∧
      (found = root ∨ found.ProperlyDominates root ctx true) := by
  unfold Assignment.findOp at hfound
  cases hget : Assignment.getOp assignment opHandle with
  | some concrete =>
    simp [hget] at hfound
    subst found
    exact h.1 opHandle concrete hget
  | none =>
    rw [hget] at hfound
    cases hvalue : results.findSome? assignment.getValue with
    | none => simp [hvalue] at hfound
    | some value =>
      rw [hvalue] at hfound
      cases value with
      | blockArgument ptr => simp at hfound
      | opResult resultPtr =>
        simp at hfound
        subst found
        obtain ⟨pref, resultHandle, suffix, _, hresult, _⟩ :=
          Array.findSome?_eq_some_iff.mp hvalue
        obtain ⟨consumer, hconsumerIn, hconsumer, _, hmem⟩ :=
          h.2 resultHandle (.opResult resultPtr) hresult
        rcases hmem with hoperand | hresultMem
        · have hdefDom : resultPtr.op.ProperlyDominates consumer ctx true :=
            OperationPtr.properlyDominates_of_definingOp?_of_mem_getOperands!
              ctxDom ValuePtr.definingOp?_opResult hoperand
          have hdefIn : resultPtr.op.InBounds ctx.raw := by grind
          refine ⟨hdefIn, Or.inr ?_⟩
          rcases hconsumer with rfl | hconsumer
          · exact hdefDom
          · exact OperationPtr.properlyDominates_trans hdefDom hconsumer
        · simp only [OperationPtr.getResults!.mem_iff_exists_index] at hresultMem
          obtain ⟨index, hindex, hvalue⟩ := hresultMem
          have heq : resultPtr.op = consumer := by
            simpa using (congrArg ValuePtr.definingOp? hvalue).symm
          subst consumer
          exact ⟨hconsumerIn, hconsumer⟩



theorem Assignment.Rooted.runDecl
    {assignment assignment' : Assignment OpCode} {ctx : WfIRContext OpCode}
    {root : OperationPtr} {decl : MatchDecl OpCode} (ctxDom : ctx.Dom)
    (h : Assignment.Rooted assignment ctx root)
    (hsupported : decl.Supported)
    (hmatch : decl.run ctx.raw assignment = some assignment') :
    Assignment.Rooted assignment' ctx root := by
  cases decl with
  | type matcher handle =>
    cases hget : Assignment.getType assignment handle with
    | none => simp [MatchDecl.run, hget] at hmatch
    | some actual =>
      by_cases hmatcher : matcher actual = true <;>
        simp [MatchDecl.run, hget, hmatcher, _root_.guard, pure,
          Alternative.failure] at hmatch
      subst assignment'
      exact h
  | applyNative inputs predicate =>
    simp only [MatchDecl.run, Option.bind_eq_bind] at hmatch
    rw [Option.bind_eq_some_iff] at hmatch
    obtain ⟨_, _, hmatch⟩ := hmatch
    rw [Option.bind_eq_some_iff] at hmatch
    obtain ⟨_, _, hmatch⟩ := hmatch
    simp only [pure, Option.some.injEq] at hmatch
    subst assignment'
    exact h
  | operation opCode operands resultTypes property propertyHandle opHandle results _ =>
    simp [MatchDecl.run] at hmatch
    simp only [Option.bind_eq_some_iff] at hmatch
    obtain ⟨operation, hget, boundAssignment, hbind, resultAssignment, hresults,
      _, hopcode, _, hpropertyMatch, propertyAssignment, hproperty,
      _, _hresultSize, typedAssignment, htypes, _, _hoperandSize, hmatch⟩ := hmatch
    have hopRooted := h.findOp ctxDom hget
    have hboundRooted := h.bindOp hopRooted hbind
    have hopcodeEq : operation.getOpType! ctx.raw = opCode := by
      simpa [_root_.guard] using hopcode
    have hopPure : operation.Pure ctx.raw := by
      change SupportedOpCode opCode at hsupported
      apply hsupported.pure hopcodeEq
      simpa [_root_.guard] using hpropertyMatch
    have hresultRooted : Assignment.Rooted resultAssignment ctx root := by
      apply hboundRooted.bindValues hopRooted hopPure ?_ hresults
      intro value hvalue
      exact Or.inr (by simpa using hvalue)
    apply ((hresultRooted.bindProperty hproperty).bindTypes htypes).bindValues
      hopRooted hopPure ?_ hmatch
    intro value hvalue
    exact Or.inl (by simpa using hvalue)
  | value typeHandle handle =>
    simp [MatchDecl.run] at hmatch
    rw [Option.bind_eq_some_iff] at hmatch
    obtain ⟨_, _, htype⟩ := hmatch
    exact h.bindType htype

theorem Assignment.Extends.runDecl
    {assignment assignment' : Assignment OpCode} {ctx : IRContext OpCode}
    {decl : MatchDecl OpCode}
    (hmatch : decl.run ctx assignment = some assignment') :
    Assignment.Extends assignment assignment' := by
  cases decl with
  | type matcher handle =>
    cases hget : Assignment.getType assignment handle with
    | none => simp [MatchDecl.run, hget] at hmatch
    | some actual =>
      by_cases hmatcher : matcher actual = true <;>
        simp [MatchDecl.run, hget, hmatcher, _root_.guard, pure,
          Alternative.failure] at hmatch
      subst assignment'
      exact .refl
  | applyNative inputs predicate =>
    simp only [MatchDecl.run, Option.bind_eq_bind] at hmatch
    rw [Option.bind_eq_some_iff] at hmatch
    obtain ⟨_, _, hmatch⟩ := hmatch
    rw [Option.bind_eq_some_iff] at hmatch
    obtain ⟨_, _, hmatch⟩ := hmatch
    simp only [pure, Option.some.injEq] at hmatch
    subst assignment'
    exact .refl
  | operation opCode operands resultTypes property propertyHandle opHandle results _ =>
    simp [MatchDecl.run] at hmatch
    simp only [Option.bind_eq_some_iff] at hmatch
    obtain ⟨found, hfound, boundAssignment, hbind, resultAssignment, hresults,
      _, _, _, _, propertyAssignment, hproperty, _, _, assignment₁, htypes, _, _, hvalues⟩ := hmatch
    exact (Assignment.Extends.bindOp hbind).trans
      ((Assignment.Extends.bindValues hresults).trans
        ((Assignment.Extends.bindProperty hproperty).trans
          ((Assignment.Extends.bindTypes htypes).trans (.bindValues hvalues))))
  | value typeHandle handle =>
    simp [MatchDecl.run] at hmatch
    rw [Option.bind_eq_some_iff] at hmatch
    obtain ⟨_, _, htype⟩ := hmatch
    exact .bindType htype

theorem HandleContext.insert_unavailable
    {before after : HandleContext} {handle : Handle OpCode kind}
    (hinsert : before.insert handle = some after) :
    after.unavailable = before.unavailable := by
  unfold HandleContext.insert at hinsert
  split at hinsert
  · simp only [Option.some.injEq] at hinsert
    subst after
    rfl
  · split at hinsert <;> simp_all

theorem HandleContext.insertMany_unavailable
    {before after : HandleContext} {handles : List (Handle OpCode kind)}
    (hinsert : before.insertMany handles = some after) :
    after.unavailable = before.unavailable := by
  induction handles generalizing before with
  | nil =>
    simp [HandleContext.insertMany] at hinsert
    subst after
    rfl
  | cons handle handles ih =>
    change (before.insert handle).bind
      (fun middle => middle.insertMany handles) = some after at hinsert
    rw [Option.bind_eq_some_iff] at hinsert
    obtain ⟨middle, hhead, htail⟩ := hinsert
    exact (ih htail).trans (HandleContext.insert_unavailable hhead)

theorem HandleContext.mem_unavailable_forbidMany
    {defined : HandleContext} {handles : List (Handle OpCode kind)} {id : Nat}
    (hmem : id ∈ defined.unavailable) :
    id ∈ (defined.forbidMany handles).unavailable := by
  induction handles generalizing defined with
  | nil => simpa [HandleContext.forbidMany] using hmem
  | cons handle handles ih =>
    change id ∈ ((defined.forbid handle).forbidMany handles).unavailable
    exact ih (by simp [HandleContext.forbid, hmem])

theorem HandleContext.handle_mem_unavailable_forbidMany
    {defined : HandleContext} {handles : List (Handle OpCode kind)}
    (handle : Handle OpCode kind) (hmem : handle ∈ handles) :
    handle.id ∈ (defined.forbidMany handles).unavailable := by
  induction handles generalizing defined with
  | nil => simp at hmem
  | cons head tail ih =>
    simp only [List.mem_cons] at hmem
    rcases hmem with heq | hmem
    · have htail : handle.id ∈ ((defined.forbid head).forbidMany tail).unavailable := by
        apply HandleContext.mem_unavailable_forbidMany
        simp [HandleContext.forbid, heq]
      simpa only [HandleContext.forbidMany, List.foldl] using htail
    · have htail := ih (defined := defined.forbid head) hmem
      simpa only [HandleContext.forbidMany, List.foldl] using htail

theorem Assignment.bind_provenance
    {before after : Assignment OpCode} {boundType queryType : HandleType OpCode}
    {bound : Handle OpCode boundType} {query : Handle OpCode queryType}
    {binding existing : Binding OpCode}
    (hbind : before.bind bound binding = some after)
    (hget : after.getBinding query = some existing) :
    (query.id = bound.id ∧ existing = binding) ∨
      before.getBinding query = some existing := by
  rw [Assignment.getBinding_eq_some_iff] at hget ⊢
  exact Assignment.bind_binding hbind hget

theorem Assignment.bindValues_provenance
    {before after : Assignment OpCode}
    {handles : List (Handle OpCode .value)} {values : List ValuePtr}
    (hbind : before.bindValues handles values = some after)
    {queryType : HandleType OpCode} {query : Handle OpCode queryType}
    {binding : Binding OpCode} (hget : after.getBinding query = some binding) :
    before.getBinding query = some binding ∨
      ∃ handle ∈ handles, ∃ value ∈ values,
        query.id = handle.id ∧ binding = .value value := by
  induction handles generalizing before after values with
  | nil =>
    cases values <;> simp [Assignment.bindValues] at hbind
    subst after
    exact Or.inl hget
  | cons handle handles ih =>
    cases values with
    | nil => simp [Assignment.bindValues] at hbind
    | cons value values =>
      change (before.bindValue handle value).bind
        (fun middle => middle.bindValues handles values) = some after at hbind
      rw [Option.bind_eq_some_iff] at hbind
      obtain ⟨middle, hhead, htail⟩ := hbind
      rcases ih htail hget with hmiddle | hlater
      · rcases Assignment.bind_provenance hhead hmiddle with hnew | hbefore
        · right
          exact ⟨handle, by simp, value, by simp, hnew.1, hnew.2⟩
        · exact Or.inl hbefore
      · right
        obtain ⟨laterHandle, hhandle, laterValue, hvalue, heq, hbinding⟩ := hlater
        exact ⟨laterHandle, by simp [hhandle], laterValue, by simp [hvalue], heq, hbinding⟩

theorem Assignment.bindTypes_provenance
    {before after : Assignment OpCode}
    {handles : List (Handle OpCode .type)} {types : List TypeAttr}
    (hbind : before.bindTypes handles types = some after)
    {queryType : HandleType OpCode} {query : Handle OpCode queryType}
    {binding : Binding OpCode} (hget : after.getBinding query = some binding) :
    before.getBinding query = some binding ∨
      ∃ handle ∈ handles, ∃ type ∈ types,
        query.id = handle.id ∧ binding = .type type := by
  induction handles generalizing before after types with
  | nil =>
    cases types <;> simp [Assignment.bindTypes] at hbind
    subst after
    exact Or.inl hget
  | cons handle handles ih =>
    cases types with
    | nil => simp [Assignment.bindTypes] at hbind
    | cons type types =>
      change (before.bindType handle type).bind
        (fun middle => middle.bindTypes handles types) = some after at hbind
      rw [Option.bind_eq_some_iff] at hbind
      obtain ⟨middle, hhead, htail⟩ := hbind
      rcases ih htail hget with hmiddle | hlater
      · rcases Assignment.bind_provenance hhead hmiddle with hnew | hbefore
        · right
          exact ⟨handle, by simp, type, by simp, hnew.1, hnew.2⟩
        · exact Or.inl hbefore
      · right
        obtain ⟨laterHandle, hhandle, laterType, htype, heq, hbinding⟩ := hlater
        exact ⟨laterHandle, by simp [hhandle], laterType, by simp [htype], heq, hbinding⟩

/-- Every handle denoting the root operation or one of its results is marked unavailable. -/
@[expose]
def Assignment.RootAliasesUnavailable (assignment : Assignment OpCode)
    (defined : HandleContext) (root : OperationPtr) : Prop :=
  (∀ handle, assignment.getOp handle = some root →
      handle.id ∈ defined.unavailable) ∧
  (∀ handle result, assignment.getValue handle = some (.opResult result) →
      result.op = root → handle.id ∈ defined.unavailable)

theorem MatchDecl.collectBindings_unavailable_mono
    {decl : MatchDecl OpCode} {before after : HandleContext}
    (hcollect : decl.collectBindings before = some after) :
    ∀ id ∈ before.unavailable, id ∈ after.unavailable := by
  intro id hmem
  cases decl with
  | type matcher handle =>
    simp [MatchDecl.collectBindings] at hcollect
    subst after
    exact hmem
  | applyNative inputs predicate =>
    simp only [MatchDecl.collectBindings, Option.bind_eq_bind] at hcollect
    rw [Option.bind_eq_some_iff] at hcollect
    obtain ⟨_, _, hafter⟩ := hcollect
    have : before = after := Option.some.inj hafter
    subst after
    exact hmem
  | value typeHandle valueHandle =>
    exact (HandleContext.insert_unavailable hcollect) ▸ hmem
  | operation opCode operands resultTypes property propertyHandle opHandle results matchOp =>
    simp only [MatchDecl.collectBindings, Option.bind_eq_bind] at hcollect
    rw [Option.bind_eq_some_iff] at hcollect
    obtain ⟨opDefined, hop, hcollect⟩ := hcollect
    rw [Option.bind_eq_some_iff] at hcollect
    obtain ⟨resultDefined, hresults, hcollect⟩ := hcollect
    rw [Option.bind_eq_some_iff] at hcollect
    obtain ⟨propertyDefined, hproperty, hcollect⟩ := hcollect
    rw [Option.bind_eq_some_iff] at hcollect
    obtain ⟨typeDefined, htypes, hcollect⟩ := hcollect
    rw [Option.bind_eq_some_iff] at hcollect
    obtain ⟨operandDefined, hoperands, hcollect⟩ := hcollect
    have hunavailable : operandDefined.unavailable = before.unavailable :=
      (HandleContext.insertMany_unavailable hoperands).trans
        ((HandleContext.insertMany_unavailable htypes).trans
          ((HandleContext.insert_unavailable hproperty).trans
            ((HandleContext.insertMany_unavailable hresults).trans
              (HandleContext.insert_unavailable hop))))
    split at hcollect
    · simp only [Option.some.injEq] at hcollect
      subst after
      apply HandleContext.mem_unavailable_forbidMany
      simp [HandleContext.forbid, hunavailable, hmem]
    · simp only [Option.some.injEq] at hcollect
      subst after
      simpa [hunavailable] using hmem

theorem MatchDecl.operation_collectBindings_rootAlias
    {opCode : OpCode} {operands : Array (Handle OpCode .value)}
    {resultTypes : Array (Handle OpCode .type)} {property : PropertyMatcher opCode}
    {propertyHandle : Handle OpCode (.prop opCode)} {opHandle : Handle OpCode .op}
    {results : Array (Handle OpCode .value)}
    {resultsSize : results.size = resultTypes.size}
    {before after : HandleContext}
    (hcollect : (MatchDecl.operation opCode operands resultTypes property propertyHandle
      opHandle results resultsSize).collectBindings before = some after)
    (halias : opHandle.id ∈ before.unavailable ∨
      ∃ result ∈ results.toList, result.id ∈ before.unavailable) :
    opHandle.id ∈ after.unavailable ∧
      ∀ result ∈ results.toList, result.id ∈ after.unavailable := by
  simp only [MatchDecl.collectBindings, Option.bind_eq_bind] at hcollect
  rw [Option.bind_eq_some_iff] at hcollect
  obtain ⟨opDefined, hop, hcollect⟩ := hcollect
  rw [Option.bind_eq_some_iff] at hcollect
  obtain ⟨resultDefined, hresults, hcollect⟩ := hcollect
  rw [Option.bind_eq_some_iff] at hcollect
  obtain ⟨propertyDefined, hproperty, hcollect⟩ := hcollect
  rw [Option.bind_eq_some_iff] at hcollect
  obtain ⟨typeDefined, htypes, hcollect⟩ := hcollect
  rw [Option.bind_eq_some_iff] at hcollect
  obtain ⟨operandDefined, hoperands, hcollect⟩ := hcollect
  split at hcollect
  · simp only [Option.some.injEq] at hcollect
    subst after
    constructor
    · apply HandleContext.mem_unavailable_forbidMany
      simp [HandleContext.forbid]
    · intro result hmem
      exact HandleContext.handle_mem_unavailable_forbidMany result hmem
  · contradiction

theorem Assignment.RootAliasesUnavailable.findOp_root
    {assignment : Assignment OpCode} {defined : HandleContext}
    {root found : OperationPtr}
    {opHandle : Handle OpCode .op} {results : Array (Handle OpCode .value)}
    (h : assignment.RootAliasesUnavailable defined root)
    (hfind : assignment.findOp opHandle results = some found)
    (hroot : found = root) :
    opHandle.id ∈ defined.unavailable ∨
      ∃ result ∈ results.toList, result.id ∈ defined.unavailable := by
  subst found
  unfold Assignment.findOp at hfind
  cases hget : assignment.getOp opHandle with
  | some operation =>
    simp [hget] at hfind
    subst operation
    exact Or.inl (h.1 opHandle hget)
  | none =>
    rw [hget] at hfind
    cases hvalue : results.findSome? assignment.getValue with
    | none => simp [hvalue] at hfind
    | some value =>
      rw [hvalue] at hfind
      cases value with
      | blockArgument ptr => simp at hfind
      | opResult resultPtr =>
        simp at hfind
        obtain ⟨pref, resultHandle, suffix, _, hresult, _⟩ :=
          Array.findSome?_eq_some_iff.mp hvalue
        exact Or.inr ⟨resultHandle, by simp_all, h.2 resultHandle resultPtr hresult hfind⟩

theorem OperationPtr.eq_of_value_mem_getResults!
    {ctx : IRContext OpCode} {left right : OperationPtr} {value : ValuePtr}
    (hleft : value ∈ left.getResults! ctx) (hright : value ∈ right.getResults! ctx) :
    left = right := by
  simp only [OperationPtr.getResults!.mem_iff_exists_index] at hleft hright
  obtain ⟨i, hi, hvLeft⟩ := hleft
  obtain ⟨j, hj, hvRight⟩ := hright
  simp only [OperationPtr.getResult] at hvLeft hvRight
  grind

theorem Assignment.RootAliasesUnavailable.runDecl
    {before after : Assignment OpCode} {defined finalDefined : HandleContext}
    {ctx : WfIRContext OpCode} {root : OperationPtr} {decl : MatchDecl OpCode}
    (ctxDom : ctx.Dom) (hrooted : before.Rooted ctx root)
    (h : before.RootAliasesUnavailable defined root)
    (hrun : decl.run ctx.raw before = some after)
    (hcollect : decl.collectBindings defined = some finalDefined) :
    after.RootAliasesUnavailable finalDefined root := by
  have hmono := MatchDecl.collectBindings_unavailable_mono hcollect
  cases decl with
  | type matcher handle =>
    cases hget : before.getType handle with
    | none => simp [MatchDecl.run, hget] at hrun
    | some actual =>
      by_cases hmatcher : matcher actual = true <;>
        simp [MatchDecl.run, hget, hmatcher, _root_.guard, pure,
          Alternative.failure] at hrun
      subst after
      exact ⟨fun handle hget => hmono _ (h.1 handle hget),
        fun handle result hget hroot => hmono _ (h.2 handle result hget hroot)⟩
  | applyNative inputs predicate =>
    simp only [MatchDecl.run, Option.bind_eq_bind] at hrun
    rw [Option.bind_eq_some_iff] at hrun
    obtain ⟨_, _, hrun⟩ := hrun
    rw [Option.bind_eq_some_iff] at hrun
    obtain ⟨_, _, hrun⟩ := hrun
    simp only [pure, Option.some.injEq] at hrun
    subst after
    exact ⟨fun handle hget => hmono _ (h.1 handle hget),
      fun handle result hget hroot => hmono _ (h.2 handle result hget hroot)⟩
  | value typeHandle valueHandle =>
    simp [MatchDecl.run] at hrun
    rw [Option.bind_eq_some_iff] at hrun
    obtain ⟨_, _, htype⟩ := hrun
    constructor
    · intro query hget
      have hbinding : after.getBinding query = some (.op root) := by
        unfold Assignment.getOp at hget
        split at hget <;> simp_all
      rcases Assignment.bind_provenance htype hbinding with hnew | hbefore
      · cases hnew.2
      · apply hmono _ (h.1 query ?_)
        unfold Assignment.getOp
        rw [hbefore]
    · intro query result hget hroot
      have hbinding : after.getBinding query = some (.value (.opResult result)) := by
        unfold Assignment.getValue at hget
        split at hget <;> simp_all
      rcases Assignment.bind_provenance htype hbinding with hnew | hbefore
      · cases hnew.2
      · apply hmono _ (h.2 query result ?_ hroot)
        unfold Assignment.getValue
        rw [hbefore]
  | operation opCode operands resultTypes property propertyHandle opHandle results matchOp =>
    simp [MatchDecl.run] at hrun
    simp only [Option.bind_eq_some_iff] at hrun
    obtain ⟨found, hfind, opAssignment, hbindOp, resultAssignment, hbindResults,
      _, hopcode, _, hpropertyMatch, propertyAssignment, hbindProperty,
      _, hresultSize, typeAssignment, hbindTypes, _, hoperandSize, hbindOperands⟩ := hrun
    have hfoundRooted := hrooted.findOp ctxDom hfind
    have hrootAlias (hfoundRoot : found = root) :
        opHandle.id ∈ defined.unavailable ∨
          ∃ result ∈ results.toList, result.id ∈ defined.unavailable :=
      Assignment.RootAliasesUnavailable.findOp_root h hfind hfoundRoot
    have hforbidden (hfoundRoot : found = root) :=
      MatchDecl.operation_collectBindings_rootAlias hcollect (hrootAlias hfoundRoot)
    have hopenandsNotRoot :
        ∀ value ∈ found.getOperands! ctx.raw, ∀ result,
          value = .opResult result → result.op = root → False := by
      intro value hvalue result hvalueEq hresultRoot
      subst value
      subst root
      have hdom := OperationPtr.properlyDominates_of_definingOp?_of_mem_getOperands!
        ctxDom ValuePtr.definingOp?_opResult hvalue
      rcases hfoundRooted.2 with rfl | hfoundDom
      · exact (OperationPtr.properlyDominates_def.mp hdom).2 rfl
      · have hcycle := OperationPtr.properlyDominates_trans hdom hfoundDom
        exact (OperationPtr.properlyDominates_def.mp hcycle).2 rfl
    constructor
    · intro query hget
      have hbinding : after.getBinding query = some (.op root) := by
        unfold Assignment.getOp at hget
        split at hget <;> simp_all
      rcases Assignment.bindValues_provenance hbindOperands hbinding with htyped | hnew
      · rcases Assignment.bindTypes_provenance hbindTypes htyped with hproperty | hnew
        · rcases Assignment.bind_provenance hbindProperty hproperty with hnew | hresults
          · cases hnew.2
          · rcases Assignment.bindValues_provenance hbindResults hresults with hop | hnew
            · rcases Assignment.bind_provenance hbindOp hop with hnew | hbefore
              · have hfoundRoot : found = root := by cases hnew.2; rfl
                rw [hnew.1]
                exact (hforbidden hfoundRoot).1
              · apply hmono _ (h.1 query ?_)
                unfold Assignment.getOp
                rw [hbefore]
            · obtain ⟨_, _, _, _, _, hbad⟩ := hnew
              cases hbad
        · obtain ⟨_, _, _, _, _, hbad⟩ := hnew
          cases hbad
      · obtain ⟨_, _, _, _, _, hbad⟩ := hnew
        cases hbad
    · intro query targetResult hget htargetRoot
      have hbinding : after.getBinding query = some (.value (.opResult targetResult)) := by
        unfold Assignment.getValue at hget
        split at hget <;> simp_all
      rcases Assignment.bindValues_provenance hbindOperands hbinding with htyped | hoperand
      · rcases Assignment.bindTypes_provenance hbindTypes htyped with hproperty | hnew
        · rcases Assignment.bind_provenance hbindProperty hproperty with hnew | hresults
          · cases hnew.2
          · rcases Assignment.bindValues_provenance hbindResults hresults with hop | hresult
            · rcases Assignment.bind_provenance hbindOp hop with hnew | hbefore
              · cases hnew.2
              · apply hmono _ (h.2 query targetResult ?_ htargetRoot)
                unfold Assignment.getValue
                rw [hbefore]
            · obtain ⟨resultHandle, hhandle, resultValue, hresultMem, heq, hvalue⟩ := hresult
              have hvalueEq : resultValue = .opResult targetResult := by cases hvalue; rfl
              have hfoundRoot : found = root := by
                have harrayMem : resultValue ∈ found.getResults! ctx.raw := by
                  simpa using hresultMem
                simp only [OperationPtr.getResults!.mem_iff_exists_index] at harrayMem
                obtain ⟨index, hindex, hresultValue⟩ := harrayMem
                simp only [OperationPtr.getResult] at hresultValue
                grind
              rw [heq]
              exact (hforbidden hfoundRoot).2 resultHandle hhandle
        · obtain ⟨_, _, _, _, _, hbad⟩ := hnew
          cases hbad
      · obtain ⟨_, _, operandValue, hoperandMem, _, hvalue⟩ := hoperand
        have hvalueEq : operandValue = .opResult targetResult := by cases hvalue; rfl
        exact (hopenandsNotRoot operandValue (by simpa using hoperandMem)
          targetResult hvalueEq htargetRoot).elim

theorem Assignment.RootAliasesUnavailable.runDecls
    {decls : List (MatchDecl OpCode)}
    {before after : Assignment OpCode} {defined finalDefined : HandleContext}
    {ctx : WfIRContext OpCode} {root : OperationPtr}
    (ctxDom : ctx.Dom) (hsupported : ∀ decl ∈ decls, decl.Supported)
    (hrooted : before.Rooted ctx root)
    (h : before.RootAliasesUnavailable defined root)
    (hrun : MatchProg.runDecls decls ctx.raw before = some after)
    (hcollect : MatchProg.collectDeclBindings decls defined = some finalDefined) :
    after.RootAliasesUnavailable finalDefined root := by
  induction decls generalizing before defined with
  | nil =>
    simp [MatchProg.runDecls] at hrun
    simp [MatchProg.collectDeclBindings] at hcollect
    subst after
    subst finalDefined
    exact h
  | cons decl decls ih =>
    change (decl.run ctx.raw before).bind
      (fun middle => MatchProg.runDecls decls ctx.raw middle) = some after at hrun
    rw [Option.bind_eq_some_iff] at hrun
    obtain ⟨middle, hdecl, hrest⟩ := hrun
    change (decl.collectBindings defined).bind
      (fun nextDefined => MatchProg.collectDeclBindings decls nextDefined) =
        some finalDefined at hcollect
    rw [Option.bind_eq_some_iff] at hcollect
    obtain ⟨nextDefined, hdeclBindings, hrestBindings⟩ := hcollect
    have hdeclSupported : decl.Supported := hsupported decl (by simp)
    have hmiddleRooted := hrooted.runDecl ctxDom hdeclSupported hdecl
    have hmiddleAliases := h.runDecl ctxDom hrooted hdecl hdeclBindings
    exact ih (fun query hmem => hsupported query (by simp [hmem]))
      hmiddleRooted hmiddleAliases hrest hrestBindings

/-- A successful structurally checked match marks every handle denoting a root result unavailable. -/
theorem MatchProg.rootResult_handle_unavailable_of_run
    {prog : MatchProg OpCode α} {ctx : WfIRContext OpCode} {root : OperationPtr}
    {assignment : Assignment OpCode} {defined : HandleContext}
    (ctxDom : ctx.Dom) (rootIn : root.InBounds ctx.raw) (hsupported : prog.Supported)
    (hrun : prog.run ctx.raw root = some assignment)
    (hcollect : prog.collectBindings = some defined)
    {handle : Handle OpCode .value} {value : ValuePtr}
    (hget : assignment.getValue handle = some value)
    (hresult : value ∈ root.getResults! ctx.raw) :
    handle.id ∈ defined.unavailable := by
  unfold MatchProg.run at hrun
  simp only [Option.bind_eq_bind] at hrun
  rw [Option.bind_eq_some_iff] at hrun
  obtain ⟨initial, hbindRoot, hrun⟩ := hrun
  unfold MatchProg.collectBindings at hcollect
  simp only [Option.bind_eq_bind] at hcollect
  rw [Option.bind_eq_some_iff] at hcollect
  obtain ⟨rootResults, hrootResults, hcollect⟩ := hcollect
  rw [Option.bind_eq_some_iff] at hcollect
  obtain ⟨rootDefined, hrootDefined, hcollect⟩ := hcollect
  let initialDefined := rootDefined.forbid prog.rootHandle
  have hinitialRooted : initial.Rooted ctx root :=
    (Assignment.Rooted.empty prog.numHandles).bindOp
      ⟨rootIn, Or.inl rfl⟩ hbindRoot
  have hinitialAliases : initial.RootAliasesUnavailable initialDefined root := by
    constructor
    · intro query hquery
      have hbinding : initial.getBinding query = some (.op root) := by
        unfold Assignment.getOp at hquery
        split at hquery <;> simp_all
      rcases Assignment.bind_provenance hbindRoot hbinding with hnew | hempty
      · rw [hnew.1]
        simp [initialDefined, HandleContext.forbid]
      · have hnone :
            (Array.replicate prog.numHandles (none : Option (Binding OpCode)))[query.id]?.join =
              none := by
          by_cases hi : query.id < prog.numHandles <;>
            simp [hi]
        change (Array.replicate prog.numHandles (none : Option (Binding OpCode)))[query.id]?.join =
          some (.op root) at hempty
        rw [hnone] at hempty
        contradiction
    · intro query result hquery hresultRoot
      have hbinding : initial.getBinding query = some (.value (.opResult result)) := by
        unfold Assignment.getValue at hquery
        split at hquery <;> simp_all
      rcases Assignment.bind_provenance hbindRoot hbinding with hnew | hempty
      · cases hnew.2
      · have hnone :
            (Array.replicate prog.numHandles (none : Option (Binding OpCode)))[query.id]?.join =
              none := by
          by_cases hi : query.id < prog.numHandles <;>
            simp [hi]
        change (Array.replicate prog.numHandles (none : Option (Binding OpCode)))[query.id]?.join =
          some (.value (.opResult result)) at hempty
        rw [hnone] at hempty
        contradiction
  have hfinalAliases := hinitialAliases.runDecls ctxDom hsupported hinitialRooted
    hrun hcollect
  simp only [OperationPtr.getResults!.mem_iff_exists_index] at hresult
  obtain ⟨index, hindex, hvalue⟩ := hresult
  subst value
  apply hfinalAliases.2 handle ⟨root, index⟩ hget
  rfl

@[expose]
def MatchDecl.Occurred (decl : MatchDecl OpCode) (ctx : IRContext OpCode)
    (_root : OperationPtr) (final : Assignment OpCode) : Prop :=
  ∃ before after,
    decl.run ctx before = some after ∧ Assignment.Extends after final

theorem MatchProg.runDecls_postconditions
    {decls : List (MatchDecl OpCode)} {ctx : IRContext OpCode} {root : OperationPtr}
    {initial final : Assignment OpCode}
    (hmatch : MatchProg.runDecls decls ctx initial = some final) :
    Assignment.Extends initial final ∧
      ∀ decl ∈ decls, decl.Occurred ctx root final := by
  induction decls generalizing initial with
  | nil =>
    simp [MatchProg.runDecls] at hmatch
    subst final
    exact ⟨.refl, by simp⟩
  | cons decl decls ih =>
    change (decl.run ctx initial).bind
      (fun assignment => MatchProg.runDecls decls ctx assignment) = some final at hmatch
    rw [Option.bind_eq_some_iff] at hmatch
    obtain ⟨after, hdecl, hrest⟩ := hmatch
    obtain ⟨hext, hoccurs⟩ := ih hrest
    constructor
    · exact (Assignment.Extends.runDecl hdecl).trans hext
    · intro query hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with hEq | hmem
      · subst query
        exact ⟨initial, after, hdecl, hext⟩
      · exact hoccurs query hmem

/-- A successful complete match binds the distinguished root and executes every declaration. -/
theorem MatchProg.run_postconditions
    {prog : MatchProg OpCode α} {ctx : IRContext OpCode} {root : OperationPtr}
    {final : Assignment OpCode} (hmatch : prog.run ctx root = some final) :
    Assignment.getOp final prog.rootHandle = some root ∧
      ∀ decl ∈ prog.decls, decl.Occurred ctx root final := by
  unfold MatchProg.run at hmatch
  simp only [Option.bind_eq_bind] at hmatch
  rw [Option.bind_eq_some_iff] at hmatch
  obtain ⟨initial, hroot, hmatch⟩ := hmatch
  have hpost := MatchProg.runDecls_postconditions (root := root) hmatch
  exact ⟨hpost.1.getOp (Assignment.bindOp_get hroot), hpost.2⟩

theorem Assignment.Rooted.runDecls
    {assignment assignment' : Assignment OpCode} {ctx : WfIRContext OpCode}
    {root : OperationPtr} (ctxDom : ctx.Dom)
    (hsupported : ∀ decl ∈ decls, decl.Supported)
    (h : Assignment.Rooted assignment ctx root)
    (hmatch : MatchProg.runDecls decls ctx.raw assignment = some assignment') :
    Assignment.Rooted assignment' ctx root := by
  induction decls generalizing assignment with
  | nil =>
    simp [MatchProg.runDecls] at hmatch
    subst assignment'
    exact h
  | cons decl decls ih =>
    change (decl.run ctx.raw assignment).bind
      (fun assignment => MatchProg.runDecls decls ctx.raw assignment) =
        some assignment' at hmatch
    rw [Option.bind_eq_some_iff] at hmatch
    obtain ⟨assignment₁, hdecl, hrest⟩ := hmatch
    apply ih (fun query hmem => hsupported query (by simp [hmem]))
      (h.runDecl ctxDom (hsupported decl (by simp)) hdecl) hrest


theorem MatchProg.rooted_of_run
    {prog : MatchProg OpCode α} {ctx : WfIRContext OpCode} {root : OperationPtr}
    {assignment : Assignment OpCode} (ctxDom : ctx.Dom)
    (rootInBounds : root.InBounds ctx.raw)
    (hsupported : prog.Supported)
    (h : prog.run ctx.raw root = some assignment) :
    Assignment.Rooted assignment ctx root := by
  unfold MatchProg.run at h
  simp only [Option.bind_eq_bind] at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨initial, hroot, h⟩ := h
  have hinitialRooted :=
    (Assignment.Rooted.empty prog.numHandles).bindOp
      ⟨rootInBounds, Or.inl rfl⟩ hroot
  exact Assignment.Rooted.runDecls ctxDom hsupported hinitialRooted h

theorem Assignment.bindValue_get
    {assignment after : Assignment OpCode} {handle : Handle OpCode .value} {value : ValuePtr}
    (hbind : Assignment.bindValue assignment handle value = some after) :
    Assignment.getValue after handle = some value := by
  have h := Assignment.bind_get hbind
  simp [Assignment.getValue, Assignment.getBinding, h]

theorem MatchProg.operation_opCode_of_run
    {prog : MatchProg OpCode α} {ctx : IRContext OpCode}
    {rootOp operation : OperationPtr} {assignment : Assignment OpCode}
    {handle : Handle OpCode .op} {opCode : OpCode}
    {operands : Array (Handle OpCode .value)}
    {resultTypes : Array (Handle OpCode .type)} {property : PropertyMatcher opCode}
    {propertyHandle : Handle OpCode (.prop opCode)}
    {results : Array (Handle OpCode .value)}
    {resultsSize : results.size = resultTypes.size}
    (hoperationMem : .operation opCode operands resultTypes property propertyHandle handle results
      resultsSize ∈ prog.decls)
    (hrun : prog.run ctx rootOp = some assignment)
    (hfinalGet : Assignment.getOp assignment handle = some operation) :
    operation.getOpType! ctx = opCode := by
  obtain ⟨_, _, hmatch, hext⟩ :=
    (MatchProg.run_postconditions hrun).2
      (.operation opCode operands resultTypes property propertyHandle handle results resultsSize)
      hoperationMem
  simp [MatchDecl.run] at hmatch
  simp only [Option.bind_eq_some_iff] at hmatch
  obtain ⟨concrete, _, boundAssignment, hbind, resultAssignment, hresults,
    _, hopcode, _, _, propertyAssignment, hproperty,
    _, _, typedAssignment, htypes, _, _, hvalues⟩ := hmatch
  have hconcreteExtendsFinal :=
    (Assignment.Extends.bindValues hresults).trans
      ((Assignment.Extends.bindProperty hproperty).trans
        ((Assignment.Extends.bindTypes htypes).trans
          ((Assignment.Extends.bindValues hvalues).trans hext)))
  have hconcreteGet := hconcreteExtendsFinal.getOp (Assignment.bindOp_get hbind)
  have hEq : concrete = operation := by grind
  simpa [_root_.guard, hEq] using hopcode

theorem MatchProg.supported_operation_of_run
    {prog : MatchProg OpCode α} (hsupported : prog.Supported)
    {ctx : IRContext OpCode} {rootOp operation : OperationPtr}
    {assignment : Assignment OpCode} {handle : Handle OpCode .op}
    {opCode : OpCode} {operands : Array (Handle OpCode .value)}
    {resultTypes : Array (Handle OpCode .type)} {property : PropertyMatcher opCode}
    {propertyHandle : Handle OpCode (.prop opCode)}
    {results : Array (Handle OpCode .value)}
    {resultsSize : results.size = resultTypes.size}
    (hoperationMem : .operation opCode operands resultTypes property propertyHandle handle results
      resultsSize ∈ prog.decls)
    (hrun : prog.run ctx rootOp = some assignment)
    (hfinalGet : Assignment.getOp assignment handle = some operation) :
    operation.Pure ctx := by
  obtain ⟨before, after, hmatch, hext⟩ :=
    (MatchProg.run_postconditions hrun).2
      (.operation opCode operands resultTypes property propertyHandle handle results resultsSize)
      hoperationMem
  have hbeforeExtendsFinal := (Assignment.Extends.runDecl hmatch).trans hext
  simp [MatchDecl.run] at hmatch
  simp only [Option.bind_eq_some_iff] at hmatch
  obtain ⟨concrete, hget, boundAssignment, hbind, resultAssignment, hresults,
    _, hopcode, _, hpropertyMatch, _, hproperty,
    _, _hresultSize, _, htypes, _, _hoperandSize, hvalues⟩ := hmatch
  have hconcreteExtendsFinal :=
    (Assignment.Extends.bindValues hresults).trans
      ((Assignment.Extends.bindProperty hproperty).trans
        ((Assignment.Extends.bindTypes htypes).trans
          ((Assignment.Extends.bindValues hvalues).trans hext)))
  have hconcreteGet := hconcreteExtendsFinal.getOp
    (Assignment.bindOp_get hbind)
  have hEq : concrete = operation := by grind
  have hopcodeEq : operation.getOpType! ctx = opCode := by
    simpa [_root_.guard, hEq] using hopcode
  have hpropertySupported :=
    hsupported
      (.operation opCode operands resultTypes property propertyHandle handle results resultsSize)
      hoperationMem
  apply hpropertySupported.pure hopcodeEq
  simpa [_root_.guard, hEq] using hpropertyMatch

theorem MatchProg.supported_root_of_run
    {prog : MatchProg OpCode α} (hsupported : prog.Supported)
    (hconstrainsRoot : prog.ConstrainsRoot)
    {ctx : IRContext OpCode} {rootOp : OperationPtr} {assignment : Assignment OpCode}
    (hrun : prog.run ctx rootOp = some assignment) :
    HasOpInfo.isTerminator (rootOp.getOpType! ctx) = false := by
  cases hdecls : prog.decls with
  | nil =>
    exfalso
    simp [MatchProg.ConstrainsRoot, hdecls] at hconstrainsRoot
  | cons rootConstraint rest =>
    cases rootConstraint with
    | operation opCode operands resultTypes property propertyHandle handle results resultsSize =>
      have hhandle : handle = prog.rootHandle := by
        simpa [MatchProg.ConstrainsRoot, hdecls] using hconstrainsRoot
      have hsupportedDecl := hsupported
        (.operation opCode operands resultTypes property propertyHandle handle results resultsSize)
        (by simp [hdecls])
      unfold SupportedOpCode at hsupportedDecl
      subst handle
      have hopcode := MatchProg.operation_opCode_of_run
        (prog := prog) (operation := rootOp) (opCode := opCode)
        (operands := operands) (resultTypes := resultTypes) (property := property)
        (propertyHandle := propertyHandle) (handle := prog.rootHandle) (results := results)
        (resultsSize := resultsSize)
        (by simp [hdecls]) hrun (MatchProg.run_postconditions hrun).1
      rw [hopcode]
      exact hsupportedDecl.1
    | value =>
      exfalso
      simp [MatchProg.ConstrainsRoot, hdecls] at hconstrainsRoot
    | type =>
      exfalso
      simp [MatchProg.ConstrainsRoot, hdecls] at hconstrainsRoot
    | applyNative =>
      exfalso
      simp [MatchProg.ConstrainsRoot, hdecls] at hconstrainsRoot

/-- The structurally distinguished root is pure whenever a supported matcher succeeds. -/
theorem MatchProg.supported_root_pure_of_run
    {prog : MatchProg OpCode α} (hsupported : prog.Supported)
    (hconstrainsRoot : prog.ConstrainsRoot)
    {ctx : IRContext OpCode} {rootOp : OperationPtr} {assignment : Assignment OpCode}
    (hrun : prog.run ctx rootOp = some assignment) :
    rootOp.Pure ctx := by
  cases hdecls : prog.decls with
  | nil =>
    exfalso
    simp [MatchProg.ConstrainsRoot, hdecls] at hconstrainsRoot
  | cons rootConstraint rest =>
    cases rootConstraint with
    | operation opCode operands resultTypes property propertyHandle handle results resultsSize =>
      have hhandle : handle = prog.rootHandle := by
        simpa [MatchProg.ConstrainsRoot, hdecls] using hconstrainsRoot
      subst handle
      exact MatchProg.supported_operation_of_run
        (opCode := opCode) (operands := operands) (resultTypes := resultTypes)
        (property := property) (propertyHandle := propertyHandle)
        (handle := prog.rootHandle) (results := results) (resultsSize := resultsSize) hsupported
        (by simp [hdecls]) hrun (MatchProg.run_postconditions hrun).1
    | value =>
      exfalso
      simp [MatchProg.ConstrainsRoot, hdecls] at hconstrainsRoot
    | type =>
      exfalso
      simp [MatchProg.ConstrainsRoot, hdecls] at hconstrainsRoot
    | applyNative =>
      exfalso
      simp [MatchProg.ConstrainsRoot, hdecls] at hconstrainsRoot


end

end Veir.Puddle
