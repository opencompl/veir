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
  | guard inputs predicate =>
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
  | guard inputs predicate =>
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
    | guard =>
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
    | guard =>
      exfalso
      simp [MatchProg.ConstrainsRoot, hdecls] at hconstrainsRoot


end

end Veir.Puddle
