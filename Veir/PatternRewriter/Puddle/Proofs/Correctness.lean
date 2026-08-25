module

public import Veir.PatternRewriter.Puddle.Proofs.InterpreterLemmas
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

/-! The bridge from Puddle validity to semantic preservation of the compiled rewrite. -/

namespace Veir.Puddle

public section

variable {OpInfo : Type} [HasOpInfo OpInfo]

private noncomputable def SemanticAssignment.ofConcrete
    {ctx : WfIRContext OpCode}
    (assignment : Assignment OpCode) (state : InterpreterState ctx)
    (root : OperationPtr) (rootValues : Array RuntimeValue) : SemanticAssignment := by
  classical
  exact assignment.bindings.map fun binding =>
    match binding with
    | some (.type type) => some (.type type)
    | some (.property opCode value) => some (.property opCode value)
    | some (.value value) =>
      if value.dominatesIp (InsertPoint.before root) ctx ∧
          value ∉ root.getResults! ctx.raw then
        match state.variables.getVar? value with
        | some runtimeValue => some (.value runtimeValue)
        | none => none
      else
        none
    | some (.op operation) =>
      let runtimeValues :=
        if operation = root then some rootValues
        else (operation.getResults! ctx.raw).mapM state.variables.getVar?
      match runtimeValues with
      | some values => some (.op values)
      | none => none
    | _ => none

private theorem SemanticAssignment.ofConcrete_getType
    (hget : Assignment.getType assignment handle = some type) :
    (SemanticAssignment.ofConcrete assignment state root rootValues).getType handle =
      some type := by
  have hbinding : assignment.bindings[handle.id]? = some (some (.type type)) := by
    apply (Assignment.getBinding_eq_some_iff _ _ _).mp
    unfold Assignment.getType at hget
    split at hget <;> simp_all
  simp [SemanticAssignment.ofConcrete, SemanticAssignment.getType, hbinding]

private theorem SemanticAssignment.ofConcrete_getProperty
    {opCode : OpCode} {handle : Handle OpCode (.prop opCode)} {value : propertiesOf opCode}
    (hget : Assignment.getProperty assignment handle = some value) :
    (SemanticAssignment.ofConcrete assignment state root rootValues).getProperty handle =
      some value := by
  unfold Assignment.getProperty at hget
  unfold SemanticAssignment.getProperty
  simp only [SemanticAssignment.ofConcrete, Array.getElem?_map]
  cases hslot : assignment.bindings[handle.id]? with
  | none => simp [hslot] at hget
  | some slot =>
    cases slot with
    | none => simp [hslot] at hget
    | some binding =>
      cases binding <;> simp [Assignment.getBinding, hslot] at hget ⊢
      assumption

private theorem MetadataTuple.Atom.resolve_ofConcrete_of_extends
    {Handle : Type} (metadataAtom : MetadataTuple.Atom OpCode Handle)
    {before final : Assignment OpCode} (hext : Assignment.Extends before final)
    {ctx : WfIRContext OpCode} {state : InterpreterState ctx}
    {root : OperationPtr} {rootValues : Array RuntimeValue}
    (handle : Handle) (value : metadataAtom.Value)
    (hresolve : @MetadataTuple.Atom.resolve OpCode _ Handle (Assignment OpCode)
      (inferInstance : MetadataStore OpCode (Assignment OpCode)) metadataAtom before handle = some value) :
    metadataAtom.resolve (SemanticAssignment.ofConcrete final state root rootValues) handle =
      some value := by
  cases metadataAtom with
  | type =>
    have hget : Assignment.getType before handle = some value := by
      dsimp [MetadataTuple.Atom.resolve] at hresolve
      exact hresolve
    simpa [MetadataTuple.Atom.resolve] using
      SemanticAssignment.ofConcrete_getType (hext.getType hget)
  | property opCode =>
    have hget : Assignment.getProperty before handle = some value := by
      dsimp [MetadataTuple.Atom.resolve] at hresolve
      exact hresolve
    simpa [MetadataTuple.Atom.resolve] using
      SemanticAssignment.ofConcrete_getProperty (hext.getProperty hget)

private theorem MetadataTuple.Shape.resolve_ofConcrete_of_extends
    {Handles : Type} (shape : MetadataTuple.Shape OpCode Handles)
    {before final : Assignment OpCode} (hext : Assignment.Extends before final)
    {ctx : WfIRContext OpCode} {state : InterpreterState ctx}
    {root : OperationPtr} {rootValues : Array RuntimeValue}
    (handles : Handles) (values : shape.Values)
    (hresolve : @MetadataTuple.Shape.resolve OpCode _ Handles (Assignment OpCode)
      (inferInstance : MetadataStore OpCode (Assignment OpCode)) shape before handles = some values) :
    shape.resolve (SemanticAssignment.ofConcrete final state root rootValues) handles =
      some values := by
  induction shape with
  | unit => rfl
  | atom metadataAtom =>
    exact metadataAtom.resolve_ofConcrete_of_extends hext handles values hresolve
  | cons head tail tailIH =>
    rcases handles with ⟨headHandle, tailHandles⟩
    cases hhead : @MetadataTuple.Atom.resolve OpCode _ _ (Assignment OpCode)
        (inferInstance : MetadataStore OpCode (Assignment OpCode)) head before headHandle with
    | none => simp [MetadataTuple.Shape.resolve, hhead] at hresolve
    | some headValue =>
      cases htail : @MetadataTuple.Shape.resolve OpCode _ _ (Assignment OpCode)
          (inferInstance : MetadataStore OpCode (Assignment OpCode)) tail before tailHandles with
      | none => simp [MetadataTuple.Shape.resolve, hhead, htail] at hresolve
      | some tailValues =>
        simp [MetadataTuple.Shape.resolve, hhead, htail] at hresolve
        subst values
        simp [MetadataTuple.Shape.resolve,
          head.resolve_ofConcrete_of_extends hext headHandle headValue hhead,
          tailIH tailHandles tailValues htail]

private theorem MetadataTuple.resolve_ofConcrete_of_extends
    {Handles : Type} [bundle : IsMetadataTuple OpCode Handles]
    {before final : Assignment OpCode} (hext : Assignment.Extends before final)
    {ctx : WfIRContext OpCode} {state : InterpreterState ctx}
    {root : OperationPtr} {rootValues : Array RuntimeValue}
    (handles : Handles) (values : MetadataValues OpCode Handles)
    (hresolve : @MetadataTuple.resolve OpCode _ Handles (Assignment OpCode) bundle
      (inferInstance : MetadataStore OpCode (Assignment OpCode)) before handles = some values) :
    MetadataTuple.resolve (SemanticAssignment.ofConcrete final state root rootValues) handles =
      some values := by
  exact bundle.shape.resolve_ofConcrete_of_extends hext handles values hresolve

private theorem SemanticAssignment.ofConcrete_getValue
    {ctx : WfIRContext OpCode}
    {assignment : Assignment OpCode} {state : InterpreterState ctx}
    {root : OperationPtr} {rootValues : Array RuntimeValue}
    {handle : Handle OpCode .value} {value : ValuePtr}
    {runtimeValue : RuntimeValue}
    (hget : Assignment.getValue assignment handle = some value)
    (hdominates : value.dominatesIp (InsertPoint.before root) ctx)
    (hnotRootResult : value ∉ root.getResults! ctx.raw)
    (hvalue : state.variables.getVar? value = some runtimeValue) :
    (SemanticAssignment.ofConcrete assignment state root rootValues).getValue handle =
      some runtimeValue := by
  have hbinding : assignment.bindings[handle.id]? = some (some (.value value)) := by
    apply (Assignment.getBinding_eq_some_iff _ _ _).mp
    unfold Assignment.getValue at hget
    split at hget <;> simp_all
  simp [SemanticAssignment.ofConcrete, SemanticAssignment.getValue, hbinding,
    hdominates, hnotRootResult, hvalue]

private theorem SemanticAssignment.ofConcrete_getValue_eq_some
    {ctx : WfIRContext OpCode}
    {assignment : Assignment OpCode} {state : InterpreterState ctx}
    {root : OperationPtr} {rootValues : Array RuntimeValue}
    {handle : Handle OpCode .value} {runtimeValue : RuntimeValue}
    (hget : (SemanticAssignment.ofConcrete assignment state root rootValues).getValue handle =
      some runtimeValue) :
    ∃ value, Assignment.getValue assignment handle = some value ∧
      value.dominatesIp (InsertPoint.before root) ctx ∧ value ∉ root.getResults! ctx.raw ∧
      state.variables.getVar? value = some runtimeValue := by
  have hslot : (SemanticAssignment.ofConcrete assignment state root rootValues)[handle.id]? =
      some (some (.value runtimeValue)) := by
    unfold SemanticAssignment.getValue at hget
    split at hget <;> simp_all
  simp only [SemanticAssignment.ofConcrete, Array.getElem?_map] at hslot
  cases hbinding : assignment.bindings[handle.id]? with
  | none => simp [hbinding] at hslot
  | some binding =>
    simp [hbinding] at hslot
    rcases binding with _ | binding
    · simp at hslot
    · cases binding with
      | value value =>
        by_cases husable : value.dominatesIp (InsertPoint.before root) ctx ∧
            value ∉ root.getResults! ctx.raw
        · cases hRuntime : state.variables.getVar? value with
          | none => simp [husable, hRuntime] at hslot
          | some runtime =>
            simp [husable, hRuntime] at hslot
            subst runtimeValue
            refine ⟨value, ?_, husable.1, husable.2, hRuntime⟩
            simp [Assignment.getValue, Assignment.getBinding, hbinding]
        · simp [husable] at hslot
      | type type =>
        rcases type with ⟨type, property⟩
        cases type <;> simp_all
      | property opCode value => simp_all
      | op operation =>
        split at hslot <;> simp_all
        split at hslot <;> simp_all

private theorem SemanticAssignment.ofConcrete_getOp_root
    (hget : Assignment.getOp assignment handle = some root) :
    (SemanticAssignment.ofConcrete assignment state root rootValues).getOp handle =
      some rootValues := by
  have hbinding : assignment.bindings[handle.id]? = some (some (.op root)) := by
    unfold Assignment.getOp at hget
    split at hget <;> simp_all
  simp [SemanticAssignment.ofConcrete, SemanticAssignment.getOp, hbinding]

private theorem SemanticAssignment.ofConcrete_getOp_other
    {ctx : WfIRContext OpCode}
    {assignment : Assignment OpCode} {state : InterpreterState ctx}
    {root operation : OperationPtr} {rootValues : Array RuntimeValue}
    {handle : Handle OpCode .op} {runtimeValues : Array RuntimeValue}
    (hget : Assignment.getOp assignment handle = some operation)
    (hne : operation ≠ root)
    (hvalues : (operation.getResults! ctx.raw).mapM state.variables.getVar? =
      some runtimeValues) :
    (SemanticAssignment.ofConcrete assignment state root rootValues).getOp handle =
      some runtimeValues := by
  have hbinding : assignment.bindings[handle.id]? = some (some (.op operation)) := by
    unfold Assignment.getOp at hget
    split at hget <;> simp_all
  simp [SemanticAssignment.ofConcrete, SemanticAssignment.getOp, hbinding, hne, hvalues]


private theorem SemanticAssignment.ofConcrete_getValues_of_bindValues
    {ctx : WfIRContext OpCode} {state : InterpreterState ctx}
    {root : OperationPtr} {rootValues : Array RuntimeValue}
    {before after final : Assignment OpCode}
    {handles : List (Handle OpCode .value)} {values : List ValuePtr}
    {runtimeValues : List RuntimeValue}
    (hbind : Assignment.bindValues before handles values = some after)
    (hext : Assignment.Extends after final)
    (hdominates : ∀ value ∈ values,
      value.dominatesIp (InsertPoint.before root) ctx)
    (hnotRoots : ∀ value ∈ values, value ∉ root.getResults! ctx.raw)
    (hvalues : values.mapM state.variables.getVar? = some runtimeValues) :
    handles.mapM (SemanticAssignment.ofConcrete final state root rootValues).getValue =
      some runtimeValues := by
  induction handles generalizing before after values runtimeValues with
  | nil =>
    cases values <;> simp [Assignment.bindValues] at hbind hvalues
    subst after
    simpa using hvalues
  | cons handle handles ih =>
    cases values with
    | nil => simp [Assignment.bindValues] at hbind
    | cons value values =>
      change (Assignment.bindValue before handle value).bind
        (fun assignment => Assignment.bindValues assignment handles values) = some after at hbind
      rw [Option.bind_eq_some_iff] at hbind
      obtain ⟨valueAssignment, hvalue, hrest⟩ := hbind
      cases hRuntimeValue : state.variables.getVar? value with
      | none => simp [List.mapM_cons, hRuntimeValue] at hvalues
      | some runtimeValue =>
        cases hRuntimeValues : values.mapM state.variables.getVar? with
        | none => simp [List.mapM_cons, hRuntimeValue, hRuntimeValues] at hvalues
        | some tailRuntimeValues =>
          simp [List.mapM_cons, hRuntimeValue, hRuntimeValues] at hvalues
          subst runtimeValues
          have hfinalValue := hext.getValue
            ((Assignment.Extends.bindValues hrest).getValue
              (Assignment.bindValue_get hvalue))
          have hsemanticValue := SemanticAssignment.ofConcrete_getValue
            (root := root) (rootValues := rootValues) hfinalValue
              (hdominates value (by simp)) (hnotRoots value (by simp)) hRuntimeValue
          have hsemanticValues := ih hrest hext
            (by intro tail hmem; exact hdominates tail (by simp [hmem]))
            (by intro tail hmem; exact hnotRoots tail (by simp [hmem])) hRuntimeValues
          simp [hsemanticValue, hsemanticValues]

private theorem SemanticAssignment.ofConcrete_getValues_eq_of_bindValues
    {ctx : WfIRContext OpCode} {state : InterpreterState ctx}
    {root : OperationPtr} {rootValues : Array RuntimeValue}
    {before after final : Assignment OpCode}
    {handles : List (Handle OpCode .value)} {values : List ValuePtr}
    {runtimeValues expected : List RuntimeValue}
    (hbind : Assignment.bindValues before handles values = some after)
    (hext : Assignment.Extends after final)
    (hsemantic : handles.mapM
      (SemanticAssignment.ofConcrete final state root rootValues).getValue = some runtimeValues)
    (hvalues : values.mapM state.variables.getVar? = some expected) :
    runtimeValues = expected := by
  induction handles generalizing before after values runtimeValues expected with
  | nil =>
    cases values <;> simp [Assignment.bindValues] at hbind hsemantic hvalues <;> subst_vars <;> rfl
  | cons handle handles ih =>
    cases values with
    | nil => simp [Assignment.bindValues] at hbind
    | cons value values =>
      change (Assignment.bindValue before handle value).bind
        (fun assignment => Assignment.bindValues assignment handles values) = some after at hbind
      rw [Option.bind_eq_some_iff] at hbind
      obtain ⟨middle, hheadBind, htailBind⟩ := hbind
      cases hsemanticHead :
          (SemanticAssignment.ofConcrete final state root rootValues).getValue handle with
      | none => simp [List.mapM_cons, hsemanticHead] at hsemantic
      | some runtime =>
        cases hsemanticTail : handles.mapM
            (SemanticAssignment.ofConcrete final state root rootValues).getValue with
        | none => simp [List.mapM_cons, hsemanticHead, hsemanticTail] at hsemantic
        | some runtimes =>
          simp [List.mapM_cons, hsemanticHead, hsemanticTail] at hsemantic
          subst runtimeValues
          cases hvalue : state.variables.getVar? value with
          | none => simp [List.mapM_cons, hvalue] at hvalues
          | some actual =>
            cases htailValues : values.mapM state.variables.getVar? with
            | none => simp [List.mapM_cons, hvalue, htailValues] at hvalues
            | some actuals =>
              simp [List.mapM_cons, hvalue, htailValues] at hvalues
              subst expected
              obtain ⟨concreteValue, hconcrete, _, _, hsemanticRuntime⟩ :=
                SemanticAssignment.ofConcrete_getValue_eq_some hsemanticHead
              have hfinalValue := hext.getValue
                ((Assignment.Extends.bindValues htailBind).getValue
                  (Assignment.bindValue_get hheadBind))
              rw [hfinalValue] at hconcrete
              simp only [Option.some.injEq] at hconcrete
              subst concreteValue
              rw [hvalue] at hsemanticRuntime
              simp only [Option.some.injEq] at hsemanticRuntime
              subst runtime
              simp [ih htailBind hext hsemanticTail htailValues]

private theorem SemanticAssignment.ofConcrete_rootValues_absent_of_bindValues
    {ctx : WfIRContext OpCode} {state : InterpreterState ctx}
    {root : OperationPtr} {rootValues : Array RuntimeValue}
    {before after final : Assignment OpCode}
    {handles : List (Handle OpCode .value)} {values : List ValuePtr}
    {runtimeValues : List RuntimeValue}
    (hbind : Assignment.bindValues before handles values = some after)
    (hext : Assignment.Extends after final)
    (hroots : ∀ value ∈ values, value ∈ root.getResults! ctx.raw)
    (hsemantic : handles.mapM
      (SemanticAssignment.ofConcrete final state root rootValues).getValue = some runtimeValues) :
    values = [] ∧ runtimeValues = [] := by
  induction handles generalizing before after values runtimeValues with
  | nil =>
    cases values <;> simp [Assignment.bindValues] at hbind hsemantic <;> subst_vars <;> simp
  | cons handle handles ih =>
    cases values with
    | nil => simp [Assignment.bindValues] at hbind
    | cons value values =>
      change (Assignment.bindValue before handle value).bind
        (fun assignment => Assignment.bindValues assignment handles values) = some after at hbind
      rw [Option.bind_eq_some_iff] at hbind
      obtain ⟨middle, hheadBind, htailBind⟩ := hbind
      cases hsemanticHead :
          (SemanticAssignment.ofConcrete final state root rootValues).getValue handle with
      | none => simp [List.mapM_cons, hsemanticHead] at hsemantic
      | some runtime =>
        obtain ⟨concreteValue, hconcrete, _, hnotRoot, _⟩ :=
          SemanticAssignment.ofConcrete_getValue_eq_some hsemanticHead
        have hfinalValue := hext.getValue
          ((Assignment.Extends.bindValues htailBind).getValue
            (Assignment.bindValue_get hheadBind))
        rw [hfinalValue] at hconcrete
        simp only [Option.some.injEq] at hconcrete
        subst concreteValue
        exact (hnotRoot (hroots value (by simp))).elim

private theorem Assignment.bindType_get
    {assignment after : Assignment OpCode} {handle : Handle OpCode .type} {type : TypeAttr}
    (hbind : Assignment.bindType assignment handle type = some after) :
    Assignment.getType after handle = some type := by
  have h := Assignment.bind_get hbind
  simp [Assignment.getType, Assignment.getBinding, h]

private theorem SemanticAssignment.ofConcrete_getTypes_of_bindTypes
    {ctx : WfIRContext OpCode} {state : InterpreterState ctx}
    {root : OperationPtr} {rootValues : Array RuntimeValue}
    {before after final : Assignment OpCode}
    {handles : List (Handle OpCode .type)} {types : List TypeAttr}
    (hbind : Assignment.bindTypes before handles types = some after)
    (hext : Assignment.Extends after final) :
    handles.mapM (SemanticAssignment.ofConcrete final state root rootValues).getType =
      some types := by
  induction handles generalizing before after types with
  | nil =>
    cases types <;> simp [Assignment.bindTypes] at hbind
    subst after
    simp
  | cons handle handles ih =>
    cases types with
    | nil => simp [Assignment.bindTypes] at hbind
    | cons type types =>
      change (Assignment.bindType before handle type).bind
        (fun assignment => Assignment.bindTypes assignment handles types) = some after at hbind
      rw [Option.bind_eq_some_iff] at hbind
      obtain ⟨typeAssignment, htype, hrest⟩ := hbind
      have hfinalType := hext.getType
        ((Assignment.Extends.bindTypes hrest).getType
          (Assignment.bindType_get htype))
      have hsemanticType := SemanticAssignment.ofConcrete_getType
        (state := state) (root := root) (rootValues := rootValues) hfinalType
      have hsemanticTypes := ih hrest hext
      simp [hsemanticType, hsemanticTypes]

private theorem VariableState.mapM_getResults_of_setResultValues_early
    {ctx : WfIRContext OpCode} {state state' : VariableState ctx}
    {op : OperationPtr} {resultValues : Array RuntimeValue}
    {inBounds : op.InBounds ctx.raw}
    (hset : state.setResultValues? op resultValues inBounds = some state') :
    (op.getResults! ctx.raw).mapM state'.getVar? = some resultValues := by
  have hnumResults : op.getNumResults! ctx.raw = resultValues.size :=
    VariableState.setResultValues?.getNumRseults!_eq_size hset
  rw [Array.mapM_eq_some_iff_of_size_eq (by
    simpa [OperationPtr.getResults!.size_eq_getNumResults!] using hnumResults)]
  intro i hi
  have hiNum : i < op.getNumResults! ctx.raw := by
    simpa [hnumResults] using hi
  rw [OperationPtr.getResults!.getElem!_eq_getResult hiNum]
  exact VariableState.getVar?_getResult_of_setResultValues?
    (inBounds := inBounds) hiNum hset

private theorem MatchProg.models_of_run
    {prog : MatchProg OpCode α} (hsupported : prog.Supported)
    {ctx : WfIRContext OpCode} {verificationRoot root : OperationPtr}
    (ctxDom : ctx.Dom) (_ctxVerif : ctx.Verified verificationRoot)
    (rootIn : root.InBounds ctx.raw)
    {assignment : Assignment OpCode}
    (hrun : prog.run ctx.raw root = some assignment)
    {state rootState : InterpreterState ctx} {rootCf}
    (stateWf : state.EquationLemmaAt (InsertPoint.before root) (by grind))
    (rootInterp : interpretOp root state rootIn = .ok (rootState, rootCf))
    {sourceValues : Array RuntimeValue}
    (hsourceValues : (root.getResults ctx.raw).mapM rootState.variables.getVar? =
      some sourceValues) :
    prog.Models (SemanticAssignment.ofConcrete assignment state root sourceValues) := by
  constructor
  · have hrootGet := (MatchProg.run_postconditions hrun).1
    have hsemanticRoot := SemanticAssignment.ofConcrete_getOp_root
      (state := state) (rootValues := sourceValues) hrootGet
    exact Option.isSome_iff_exists.mpr ⟨sourceValues, hsemanticRoot⟩
  intro decl hmem
  have hdeclSupported : decl.Supported := hsupported decl hmem
  have hoccurs : decl.Occurred ctx.raw root assignment :=
    (MatchProg.run_postconditions hrun).2 decl hmem
  cases decl with
  | type matcher handle =>
    obtain ⟨before, after, hmatch, hext⟩ := hoccurs
    simp [MatchDecl.run, Option.bind_eq_some_iff] at hmatch
    rcases hmatch with ⟨actual, hget, hguard, rfl⟩
    have hfinalType := hext.getType hget
    have hsemanticType := SemanticAssignment.ofConcrete_getType
      (state := state) (root := root) (rootValues := sourceValues) hfinalType
    refine ⟨actual, hsemanticType, ?_⟩
    rcases hguard with ⟨_, hguard⟩
    simpa [_root_.guard] using hguard
  | guard inputs predicate =>
    obtain ⟨before, after, hmatch, hext⟩ := hoccurs
    simp only [MatchDecl.run, Option.bind_eq_bind] at hmatch
    rw [Option.bind_eq_some_iff] at hmatch
    obtain ⟨values, hresolve, hmatch⟩ := hmatch
    rw [Option.bind_eq_some_iff] at hmatch
    obtain ⟨_, hpredicate, hsame⟩ := hmatch
    simp only [pure, Option.some.injEq] at hsame
    subst after
    refine ⟨values, MetadataTuple.resolve_ofConcrete_of_extends
      hext inputs values hresolve, ?_⟩
    simpa [_root_.guard] using hpredicate
  | value typeHandle handle =>
    obtain ⟨before, after, hmatch, hext⟩ := hoccurs
    simp [MatchDecl.run, Option.bind_eq_some_iff] at hmatch
    obtain ⟨value, hget, htype⟩ := hmatch
    have hfinalGet := hext.getValue
      ((Assignment.Extends.bindType htype).getValue hget)
    have hfinalType := hext.getType (Assignment.bindType_get htype)
    have hsemanticType := SemanticAssignment.ofConcrete_getType
      (state := state) (root := root) (rootValues := sourceValues) hfinalType
    refine ⟨value.getType! ctx.raw, hsemanticType, ?_⟩
    intro runtimeValue hsemanticValue
    obtain ⟨concreteValue, hconcreteValue, _, _, hRuntime⟩ :=
      SemanticAssignment.ofConcrete_getValue_eq_some hsemanticValue
    rw [hfinalGet] at hconcreteValue
    simp only [Option.some.injEq] at hconcreteValue
    subst concreteValue
    exact VariableState.getVar?_conforms hRuntime
  | operation opCode operands resultTypes property propertyHandle handle results _ =>
    obtain ⟨before, after, hmatchOriginal, hext⟩ := hoccurs
    have hmatch := hmatchOriginal
    simp [MatchDecl.run] at hmatch
    simp only [Option.bind_eq_some_iff] at hmatch
    obtain ⟨operation, hget, baseAssignment, hbindOp, resultAssignment, hbindResults,
      _, hopcode, _, hproperty, propertyAssignment, hbindProperty, _, hresultSize,
      typedAssignment, htypes, _, hoperandSize, hvalues⟩ := hmatch
    have hbaseExtendsFinal :=
      ((Assignment.Extends.bindValues hbindResults).trans
        ((Assignment.Extends.bindProperty hbindProperty).trans
          ((Assignment.Extends.bindTypes htypes).trans
            (Assignment.Extends.bindValues hvalues)))).trans hext
    have hresultExtendsFinal :=
      ((Assignment.Extends.bindProperty hbindProperty).trans
        ((Assignment.Extends.bindTypes htypes).trans
          (Assignment.Extends.bindValues hvalues))).trans hext
    have hfinalOp := hbaseExtendsFinal.getOp (Assignment.bindOp_get hbindOp)
    have hopcodeEq : operation.getOpType! ctx.raw = opCode := by
      simpa [_root_.guard] using hopcode
    have hpropertyMatch : property (operation.getProperties! ctx.raw opCode) = true := by
      simpa [_root_.guard] using hproperty
    have hpropertyExtendsFinal :=
      ((Assignment.Extends.bindTypes htypes).trans
        (Assignment.Extends.bindValues hvalues)).trans hext
    have hfinalProperty := hpropertyExtendsFinal.getProperty
      (Assignment.bindProperty_get hbindProperty)
    have hsemanticProperty := SemanticAssignment.ofConcrete_getProperty
      (state := state) (root := root) (rootValues := sourceValues) hfinalProperty
    have hrooted := MatchProg.rooted_of_run ctxDom rootIn hsupported hrun
    have hopRooted := hrooted.1 handle operation hfinalOp
    have hopPure : operation.Pure ctx.raw :=
      hdeclSupported.pure hopcodeEq hpropertyMatch
    subst opCode
    have hopIn := hopRooted.1
    obtain ⟨operationState, operationCf, hoperationInterp⟩ :
        ∃ operationState operationCf,
          interpretOp operation state hopIn = .ok (operationState, operationCf) := by
      rcases hopRooted.2 with rfl | hdominates
      · exact ⟨rootState, rootCf, rootInterp⟩
      · have hdomIp : operation.dominatesIp (InsertPoint.before root) ctx := by grind
        obtain ⟨operationCf, hoperationInterp⟩ :=
          stateWf operation hopIn hopPure hdomIp
        exact ⟨state, operationCf, hoperationInterp⟩
    obtain ⟨operandValues, resultValues, memory, variables,
        hoperandValues, hinterpret, hset, hoperationState⟩ :=
      interpretOp_some_iff.mp hoperationInterp
    have hoperandValueList :
        (operation.getOperands! ctx.raw).toList.mapM state.variables.getVar? =
          some operandValues.toList := by
      simpa [VariableState.getOperandValues, Array.mapM_eq_mapM_toList] using
        congrArg (Option.map Array.toList) hoperandValues
    have hopDominatesRoot : operation.Dominates root ctx := by
      rcases hopRooted.2 with rfl | hproper
      · exact OperationPtr.dominates_refl
      · exact OperationPtr.dominates_of_properlyDominates hproper
    have hoperandsDom : ∀ value ∈ operation.getOperands! ctx.raw,
        value.dominatesIp (InsertPoint.before root) ctx := by
      intro value hvalue
      rcases hopRooted.2 with rfl | hproper
      · exact ctxDom.operand_dominates_op hopIn hvalue
      · exact ValuePtr.dominatesIp_before_of_properlyDominates
          (ctxDom.operand_dominates_op hopIn hvalue) hproper
    have hoperandsNotRoot : ∀ value ∈ operation.getOperands! ctx.raw,
        value ∉ root.getResults! ctx.raw :=
      IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates
        ctxDom hopDominatesRoot
    have hsemanticOperandsList :=
      SemanticAssignment.ofConcrete_getValues_of_bindValues
        (root := root) (rootValues := sourceValues) hvalues hext
        (by intro value hmem; exact hoperandsDom value (by simpa using hmem))
        (by intro value hmem; exact hoperandsNotRoot value (by simpa using hmem))
        hoperandValueList
    have hsemanticOperands :
        (SemanticAssignment.ofConcrete assignment state root sourceValues).getValues operands =
          some operandValues := by
      unfold SemanticAssignment.getValues
      rw [Array.mapM_eq_mapM_toList, hsemanticOperandsList]
      simp
    have hsemanticResultTypesList :=
      SemanticAssignment.ofConcrete_getTypes_of_bindTypes
        (state := state) (root := root) (rootValues := sourceValues) htypes
        ((Assignment.Extends.bindValues hvalues).trans hext)
    have hsemanticResultTypes :
        (SemanticAssignment.ofConcrete assignment state root sourceValues).getTypes resultTypes =
          some (operation.getResultTypes! ctx.raw) := by
      unfold SemanticAssignment.getTypes
      rw [Array.mapM_eq_mapM_toList, hsemanticResultTypesList]
      simp
    have hoperationEq_of_ne : operation ≠ root → operationState = state := by
      intro hopEq
      have hproper := hopRooted.2.resolve_left hopEq
      have hdomIp : operation.dominatesIp (InsertPoint.before root) ctx := by grind
      obtain ⟨equationCf, hequation⟩ := stateWf operation hopIn hopPure hdomIp
      rw [hoperationInterp] at hequation
      grind
    have hsourceEq_of_eq : operation = root → sourceValues = resultValues := by
      intro hopEq
      subst operation
      have hstateEq : operationState = rootState := by
        rw [rootInterp] at hoperationInterp
        grind
      have hresultsLookup :
          (root.getResults! ctx.raw).mapM rootState.variables.getVar? =
            some resultValues := by
        rw [← hstateEq, hoperationState]
        exact VariableState.mapM_getResults_of_setResultValues_early hset
      rw [OperationPtr.getResults!_eq_getResults rootIn] at hresultsLookup
      rw [hsourceValues] at hresultsLookup
      exact Option.some.inj hresultsLookup
    have hsemanticResult :
        (SemanticAssignment.ofConcrete assignment state root sourceValues).getOp handle =
          some resultValues := by
      by_cases hopEq : operation = root
      · subst operation
        have hsourceEq := hsourceEq_of_eq rfl
        subst sourceValues
        exact SemanticAssignment.ofConcrete_getOp_root
          (state := state) (rootValues := resultValues) hfinalOp
      · apply SemanticAssignment.ofConcrete_getOp_other
          (rootValues := sourceValues) (runtimeValues := resultValues) hfinalOp hopEq
        have hoperationEq := hoperationEq_of_ne hopEq
        have hvariables : state.variables = variables :=
          congrArg InterpreterState.variables (hoperationEq.symm.trans hoperationState)
        rw [hvariables]
        exact VariableState.mapM_getResults_of_setResultValues_early hset
    have hresultConsistency :
        ∀ boundResults,
          (SemanticAssignment.ofConcrete assignment state root sourceValues).getValues results =
              some boundResults →
            boundResults = resultValues := by
      intro boundResults hbound
      have hboundList : results.toList.mapM
          (SemanticAssignment.ofConcrete assignment state root sourceValues).getValue =
            some boundResults.toList := by
        simpa [SemanticAssignment.getValues, Array.mapM_eq_mapM_toList] using
          congrArg (Option.map Array.toList) hbound
      by_cases hopEq : operation = root
      · subst operation
        have habsent := SemanticAssignment.ofConcrete_rootValues_absent_of_bindValues
          hbindResults hresultExtendsFinal
          (by intro value hmem; simpa using hmem) hboundList
        have hopResultsNil : (root.getResults! ctx.raw).toList = [] := habsent.1
        have hboundNil : boundResults.toList = [] := habsent.2
        have hnumResults : root.getNumResults! ctx.raw = resultValues.size :=
          VariableState.setResultValues?.getNumRseults!_eq_size hset
        have hopSize : (root.getResults! ctx.raw).size = 0 := by
          simpa using congrArg List.length hopResultsNil
        have hresultSize : resultValues.size = 0 := by
          rw [← hnumResults, ← OperationPtr.getResults!.size_eq_getNumResults!]
          exact hopSize
        have hresultNil : resultValues.toList = [] := by
          simpa using hresultSize
        simpa using congrArg List.toArray (hboundNil.trans hresultNil.symm)
      · have hoperationEq := hoperationEq_of_ne hopEq
        have hvariables : state.variables = variables :=
          congrArg InterpreterState.variables (hoperationEq.symm.trans hoperationState)
        have hresultRuntimeList :
            (operation.getResults! ctx.raw).toList.mapM state.variables.getVar? =
              some resultValues.toList := by
          rw [hvariables]
          simpa [Array.mapM_eq_mapM_toList] using congrArg (Option.map Array.toList)
            (VariableState.mapM_getResults_of_setResultValues_early hset)
        have hlists := SemanticAssignment.ofConcrete_getValues_eq_of_bindValues
          hbindResults hresultExtendsFinal hboundList hresultRuntimeList
        simpa using congrArg List.toArray hlists
    have hmemory : state.memory = memory :=
      OperationPtr.Pure.interpretOp'_eq_ok_implies_memory_eq hopPure (by
        simpa [OperationPtr.interpret] using hinterpret)
    refine ⟨operandValues, operation.getResultTypes! ctx.raw, resultValues,
      operation.getProperties! ctx.raw (operation.getOpType! ctx.raw),
      hsemanticOperands, hsemanticResultTypes, hsemanticResult, hsemanticProperty,
      hresultConsistency, hpropertyMatch, ?_⟩
    refine ⟨operation.getSuccessors! ctx.raw, state.memory, operationCf, ?_⟩
    subst memory
    simpa [OperationPtr.interpret] using hinterpret

private theorem Array.eq_pair_of_size_eq_two {values : Array α} (h : values.size = 2) :
    ∃ first second, values = #[first, second] := by
  rcases values with ⟨values⟩
  simp only [List.size_toArray] at h
  match values, h with
  | [first, second], _ => exact ⟨first, second, rfl⟩

private theorem Array.eq_singleton_of_size_eq_one {values : Array α} (h : values.size = 1) :
    ∃ value, values = #[value] := by
  rcases values with ⟨values⟩
  simp only [List.size_toArray] at h
  match values, h with
  | [value], _ => exact ⟨value, rfl⟩

private theorem RuntimeValue.int_conforms_of_int_conforms
    {width : Nat} {source target : Data.LLVM.Int width} {type : TypeAttr}
    (h : RuntimeValue.Conforms (.int width source) type) :
    RuntimeValue.Conforms (.int width target) type := by
  rcases type with ⟨type, property⟩
  cases type <;> simp_all [RuntimeValue.Conforms]

private theorem Assignment.Rooted.exists_target_value
    {assignment : Assignment OpCode} {ctx : WfIRContext OpCode} {root : OperationPtr}
    (hrooted : Assignment.Rooted assignment ctx root) (_ctxDom : ctx.Dom)
    {handle : Handle OpCode .value} {value : ValuePtr}
    (hget : Assignment.getValue assignment handle = some value)
    {state : InterpreterState ctx} {runtimeValue : RuntimeValue}
    (hRuntime : state.variables.getVar? value = some runtimeValue)
    (hvalueDom : value.dominatesIp (InsertPoint.before root) ctx)
    (hnotResult : value ∉ root.getResults! ctx.raw)
    {pattern : LocalRewritePattern OpCode} {newCtx : WfIRContext OpCode}
    {newOps : Array OperationPtr} {newValues : Array ValuePtr}
    {hpattern : pattern ctx root = some (newCtx, some (newOps, newValues))}
    {hreturn : pattern.ReturnValuesInBounds} {hreturn₂ : pattern.ReturnValues}
    {hreturn₃ : pattern.ReturnCtxChanges}
    {targetState : InterpreterState newCtx}
    (rootIn : root.InBounds ctx.raw)
    (rootInNew : root.InBounds newCtx.raw)
    (valueRefinement : state.variables.isRefinedByAt targetState.variables
      (LocalRewritePattern.mapping hpattern hreturn hreturn₂ hreturn₃)
      (.at (.before root)) (.at (.before root)))
    (targetStateDom : targetState.DefinesDominating (InsertPoint.before root)) :
    ∃ targetRuntime, targetState.variables.getVar? value = some targetRuntime ∧
      runtimeValue ⊒ targetRuntime := by
  obtain ⟨consumer, consumerIn, _, _, hmem⟩ := hrooted.2 handle value hget
  have hvalueIn : value.InBounds ctx.raw := by
    rcases hmem with hoperand | hresult <;> grind
  have hcreated := hreturn₃ ctx root newCtx newOps newValues hpattern
  have hvalueDomNew : value.dominatesIp (InsertPoint.before root) newCtx :=
    hcreated.value_dominatesIp_mono hvalueDom
  exact LocalRewritePattern.exists_refined_getVar?
    (ipIn := by grind) (ipIn' := by grind) valueRefinement targetStateDom
    hvalueIn hRuntime hvalueDom hvalueDomNew hnotResult

/-- Every semantically-created value has a refining concrete value in the target state. -/
private def Assignment.Refines
    {ctx : WfIRContext OpCode}
    (concrete : Assignment OpCode) (semantic : SemanticAssignment)
    (targetState : InterpreterState ctx) : Prop :=
  ∀ handle value sourceRuntime,
    Assignment.getValue concrete handle = some value →
    semantic.getValue handle = some sourceRuntime →
    ∃ targetRuntime, targetState.variables.getVar? value = some targetRuntime ∧
      sourceRuntime ⊒ targetRuntime

private def Assignment.MatchRefines
    {ctx : WfIRContext OpCode}
    (concrete : Assignment OpCode) (semantic : SemanticAssignment)
    (targetState : InterpreterState ctx) : Prop :=
  ∀ handle value sourceRuntime,
    Assignment.getValue concrete handle = some value →
    semantic.getValue handle = some sourceRuntime →
    ∃ targetRuntime, targetState.variables.getVar? value = some targetRuntime ∧
      sourceRuntime ⊒ targetRuntime

private theorem Assignment.getValue_bindType_eq
    {assignment after : Assignment OpCode} (bound : Handle OpCode .type)
    (query : Handle OpCode .value) (value : TypeAttr)
    (hbind : Assignment.bindType assignment bound value = some after)
    (heq : query.id = bound.id) :
    Assignment.getValue after query = none := by
  unfold Assignment.bindType at hbind
  unfold Assignment.getValue Assignment.getBinding
  rw [heq, Assignment.bind_get hbind]
  rfl

private theorem Assignment.getValue_bindType_ne
    {assignment after : Assignment OpCode} (bound : Handle OpCode .type)
    (query : Handle OpCode .value) (value : TypeAttr)
    (hbind : Assignment.bindType assignment bound value = some after)
    (hne : query.id ≠ bound.id) :
    Assignment.getValue after query = Assignment.getValue assignment query := by
  unfold Assignment.bindType at hbind
  unfold Assignment.getValue Assignment.getBinding
  rw [Assignment.bind_get_of_ne hbind hne]

private theorem Assignment.getValue_bindProperty_eq
    {assignment after : Assignment OpCode} (bound : Handle OpCode (.prop opCode))
    (query : Handle OpCode .value) (value : propertiesOf opCode)
    (hbind : Assignment.bindProperty assignment bound value = some after)
    (heq : query.id = bound.id) :
    Assignment.getValue after query = none := by
  unfold Assignment.bindProperty at hbind
  unfold Assignment.getValue Assignment.getBinding
  rw [heq, Assignment.bind_get hbind]
  rfl

private theorem Assignment.getValue_bindProperty_ne
    {assignment after : Assignment OpCode} (bound : Handle OpCode (.prop opCode))
    (query : Handle OpCode .value) (value : propertiesOf opCode)
    (hbind : Assignment.bindProperty assignment bound value = some after)
    (hne : query.id ≠ bound.id) :
    Assignment.getValue after query = Assignment.getValue assignment query := by
  unfold Assignment.bindProperty at hbind
  unfold Assignment.getValue Assignment.getBinding
  rw [Assignment.bind_get_of_ne hbind hne]

/-- Concrete and semantic creation assignments carry identical metadata. -/
private def Assignment.MetadataAgrees
    (concrete : Assignment OpCode) (semantic : SemanticAssignment) : Prop :=
  (∀ handle, (Assignment.getType concrete) handle = semantic.getType handle) ∧
  (∀ opCode (handle : Handle OpCode (.prop opCode)),
    (Assignment.getProperty concrete) handle = semantic.getProperty handle)

private theorem SemanticAssignment.getElem?_bind_eq
    (assignment : SemanticAssignment) (id : Nat) (binding : SemanticBinding) :
    (assignment.bind id binding)[id]? = some (some binding) := by
  unfold SemanticAssignment.bind
  split
  · rename_i h
    rw [Array.getElem?_set]
    simp
  · rename_i h
    have hle : assignment.size ≤ id := Nat.le_of_not_gt h
    simpa [Array.getElem?_append, hle] using
      (@Array.getElem?_push_size (Option SemanticBinding)
        (Array.replicate (id - assignment.size) none) (some binding))

private theorem SemanticAssignment.read_bind_ne
    (assignment : SemanticAssignment) (id query : Nat) (binding : SemanticBinding)
    (read : SemanticBinding → Option α)
    (hne : query ≠ id) :
    (match (assignment.bind id binding)[query]? with
      | some (some value) => read value
      | _ => none) =
    (match assignment[query]? with
      | some (some value) => read value
      | _ => none) := by
  by_cases hid : id < assignment.size
  · simp only [SemanticAssignment.bind, dif_pos hid]
    rw [Array.getElem?_set_ne hid hne.symm]
  · simp only [SemanticAssignment.bind, dif_neg hid]
    have hle : assignment.size ≤ id := Nat.le_of_not_gt hid
    have hsize : assignment.size + (id - assignment.size) = id := Nat.add_sub_of_le hle
    simp only [Array.getElem?_append, Array.size_append, Array.size_replicate,
      Array.getElem?_replicate]
    rw [hsize]
    by_cases hquery : query < assignment.size
    · have hqid : query < id := Nat.lt_of_lt_of_le hquery hle
      simp [hquery, hqid]
    · have hqs : assignment.size ≤ query := Nat.le_of_not_gt hquery
      by_cases hqid : query < id
      · have hgap := Nat.sub_lt_sub_right hqs hqid
        simp [hquery, hqid, hgap]
      · have hidq : id < query := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hqid) hne.symm
        have hdiff : query - id ≠ 0 := by omega
        simp [hquery, hqid, hdiff]

private theorem SemanticAssignment.getValue_bind_ne
    (assignment : SemanticAssignment) (id : Nat) (binding : SemanticBinding)
    (query : Handle OpCode .value) (hne : query.id ≠ id) :
    (assignment.bind id binding).getValue query = assignment.getValue query := by
  unfold SemanticAssignment.getValue
  by_cases hid : id < assignment.size
  · simp only [SemanticAssignment.bind, dif_pos hid]
    rw [Array.getElem?_set_ne hid hne.symm]
  · simp only [SemanticAssignment.bind, dif_neg hid, Array.getElem?_append,
      Array.size_append, Array.size_replicate, Array.getElem?_replicate]
    have hle : assignment.size ≤ id := Nat.le_of_not_gt hid
    have hsize : assignment.size + (id - assignment.size) = id := Nat.add_sub_of_le hle
    rw [hsize]
    by_cases hquery : query.id < assignment.size
    · have hqid : query.id < id := Nat.lt_of_lt_of_le hquery hle
      simp [hquery, hqid]
    · have hqs : assignment.size ≤ query.id := Nat.le_of_not_gt hquery
      by_cases hqid : query.id < id
      · have hgap := Nat.sub_lt_sub_right hqs hqid
        simp [hquery, hqid, hgap]
      · have hdiff : query.id - id ≠ 0 := by omega
        simp [hquery, hqid, hdiff]

private theorem SemanticAssignment.getType_bind_ne
    (assignment : SemanticAssignment) (id : Nat) (binding : SemanticBinding)
    (query : Handle OpCode .type) (hne : query.id ≠ id) :
    (assignment.bind id binding).getType query = assignment.getType query := by
  unfold SemanticAssignment.getType
  by_cases hid : id < assignment.size
  · simp only [SemanticAssignment.bind, dif_pos hid]
    rw [Array.getElem?_set_ne hid hne.symm]
  · simp only [SemanticAssignment.bind, dif_neg hid, Array.getElem?_append,
      Array.size_append, Array.size_replicate, Array.getElem?_replicate]
    have hle : assignment.size ≤ id := Nat.le_of_not_gt hid
    have hsize : assignment.size + (id - assignment.size) = id := Nat.add_sub_of_le hle
    rw [hsize]
    by_cases hquery : query.id < assignment.size
    · have hqid : query.id < id := Nat.lt_of_lt_of_le hquery hle
      simp [hquery, hqid]
    · have hqs : assignment.size ≤ query.id := Nat.le_of_not_gt hquery
      by_cases hqid : query.id < id
      · have hgap := Nat.sub_lt_sub_right hqs hqid
        simp [hquery, hqid, hgap]
      · have hdiff : query.id - id ≠ 0 := by omega
        simp [hquery, hqid, hdiff]

private theorem SemanticAssignment.getProperty_bind_ne
    (assignment : SemanticAssignment) (id : Nat) (binding : SemanticBinding)
    (query : Handle OpCode (.prop opCode)) (hne : query.id ≠ id) :
    (assignment.bind id binding).getProperty query = assignment.getProperty query := by
  unfold SemanticAssignment.getProperty
  by_cases hid : id < assignment.size
  · simp only [SemanticAssignment.bind, dif_pos hid]
    rw [Array.getElem?_set_ne hid hne.symm]
  · simp only [SemanticAssignment.bind, dif_neg hid, Array.getElem?_append,
      Array.size_append, Array.size_replicate, Array.getElem?_replicate]
    have hle : assignment.size ≤ id := Nat.le_of_not_gt hid
    have hsize : assignment.size + (id - assignment.size) = id := Nat.add_sub_of_le hle
    rw [hsize]
    by_cases hquery : query.id < assignment.size
    · have hqid : query.id < id := Nat.lt_of_lt_of_le hquery hle
      simp [hquery, hqid]
    · have hqs : assignment.size ≤ query.id := Nat.le_of_not_gt hquery
      by_cases hqid : query.id < id
      · have hgap := Nat.sub_lt_sub_right hqs hqid
        simp [hquery, hqid, hgap]
      · have hdiff : query.id - id ≠ 0 := by omega
        simp [hquery, hqid, hdiff]

private theorem SemanticAssignment.getOp_bind_ne
    (assignment : SemanticAssignment) (id : Nat) (binding : SemanticBinding)
    (query : Handle OpCode .op) (hne : query.id ≠ id) :
    (assignment.bind id binding).getOp query = assignment.getOp query := by
  unfold SemanticAssignment.getOp
  by_cases hid : id < assignment.size
  · simp only [SemanticAssignment.bind, dif_pos hid]
    rw [Array.getElem?_set_ne hid hne.symm]
  · simp only [SemanticAssignment.bind, dif_neg hid, Array.getElem?_append,
      Array.size_append, Array.size_replicate, Array.getElem?_replicate]
    have hle : assignment.size ≤ id := Nat.le_of_not_gt hid
    have hsize : assignment.size + (id - assignment.size) = id := Nat.add_sub_of_le hle
    rw [hsize]
    by_cases hquery : query.id < assignment.size
    · have hqid : query.id < id := Nat.lt_of_lt_of_le hquery hle
      simp [hquery, hqid]
    · have hqs : assignment.size ≤ query.id := Nat.le_of_not_gt hquery
      by_cases hqid : query.id < id
      · have hgap := Nat.sub_lt_sub_right hqs hqid
        simp [hquery, hqid, hgap]
      · have hdiff : query.id - id ≠ 0 := by omega
        simp [hquery, hqid, hdiff]

private theorem SemanticAssignment.ofConcrete_metadataAgrees
    {ctx : WfIRContext OpCode} {assignment : Assignment OpCode}
    {state : InterpreterState ctx} {root : OperationPtr} {rootValues : Array RuntimeValue} :
    Assignment.MetadataAgrees assignment
      (SemanticAssignment.ofConcrete assignment state root rootValues) := by
  constructor
  · intro handle
    unfold Assignment.getType Assignment.getBinding SemanticAssignment.getType SemanticAssignment.ofConcrete
    simp only [Array.getElem?_map]
    cases hslot : assignment.bindings[handle.id]? with
    | none => simp
    | some slot =>
      cases slot with
      | none => simp
      | some binding =>
        cases binding with
        | op operation =>
          simp
          by_cases hroot : operation = root
          · simp [hroot]
          · cases (operation.getResults! ctx.raw).mapM state.variables.getVar?
            <;> simp [hroot]
        | value value =>
          simp
          cases state.variables.getVar? value <;> simp
        | type type => simp
        | property actualOpCode value => simp
  · intro opCode handle
    unfold Assignment.getProperty Assignment.getBinding SemanticAssignment.getProperty SemanticAssignment.ofConcrete
    simp only [Array.getElem?_map]
    cases hslot : assignment.bindings[handle.id]? with
    | none => simp
    | some slot =>
      cases slot with
      | none => simp
      | some binding =>
        cases binding with
        | op operation =>
          simp
          by_cases hroot : operation = root
          · simp [hroot]
          · cases (operation.getResults! ctx.raw).mapM state.variables.getVar?
            <;> simp [hroot]
        | value value =>
          simp
          cases state.variables.getVar? value <;> simp
        | type type => simp
        | property actualOpCode value =>
          simp
          by_cases hop : actualOpCode = opCode <;> simp [hop]

private theorem Assignment.MetadataAgrees.bindOp
    {concrete after : Assignment OpCode} {semantic : SemanticAssignment}
    (hagrees : Assignment.MetadataAgrees concrete semantic)
    (bound : Handle OpCode .op) (operation : OperationPtr) (results : Array RuntimeValue)
    (hbind : Assignment.bindOp concrete bound operation = some after) :
    Assignment.MetadataAgrees after (semantic.bindOp bound results) := by
  constructor
  · intro query
    by_cases heq : query.id = bound.id
    · have hc : Assignment.getType after query = none := by
        unfold Assignment.bindOp at hbind
        unfold Assignment.getType Assignment.getBinding
        rw [heq, Assignment.bind_get hbind]
        rfl
      have hs : (semantic.bindOp bound results).getType query = none := by
        simp only [SemanticAssignment.bindOp, SemanticAssignment.getType]
        rw [heq, SemanticAssignment.getElem?_bind_eq]
      rw [hc, hs]
    · have hc : Assignment.getType after query = Assignment.getType concrete query := by
        unfold Assignment.bindOp at hbind
        unfold Assignment.getType Assignment.getBinding
        rw [Assignment.bind_get_of_ne hbind heq]
      rw [hc, SemanticAssignment.bindOp,
        SemanticAssignment.getType_bind_ne semantic bound.id (.op results) query heq]
      exact hagrees.1 query
  · intro queryOpCode query
    by_cases heq : query.id = bound.id
    · have hc : Assignment.getProperty after query = none := by
        unfold Assignment.bindOp at hbind
        unfold Assignment.getProperty Assignment.getBinding
        rw [heq, Assignment.bind_get hbind]
        rfl
      have hs : (semantic.bindOp bound results).getProperty query = none := by
        simp only [SemanticAssignment.bindOp, SemanticAssignment.getProperty]
        rw [heq, SemanticAssignment.getElem?_bind_eq]
      rw [hc, hs]
    · have hc := Assignment.bind_get_of_ne hbind heq
      unfold Assignment.bindOp at hbind
      unfold Assignment.getProperty Assignment.getBinding
      rw [Assignment.bind_get_of_ne hbind heq,
        SemanticAssignment.bindOp,
        SemanticAssignment.getProperty_bind_ne semantic bound.id (.op results) query heq]
      exact hagrees.2 queryOpCode query

private theorem Assignment.MetadataAgrees.bindValue
    {concrete after : Assignment OpCode} {semantic : SemanticAssignment}
    (hagrees : Assignment.MetadataAgrees concrete semantic)
    (bound : Handle OpCode .value) (value : ValuePtr) (runtime : RuntimeValue)
    (hbind : Assignment.bindValue concrete bound value = some after) :
    Assignment.MetadataAgrees after (semantic.bindValue bound runtime) := by
  constructor
  · intro query
    by_cases heq : query.id = bound.id
    · unfold Assignment.bindValue at hbind
      unfold Assignment.getType Assignment.getBinding SemanticAssignment.bindValue
        SemanticAssignment.getType
      rw [heq, Assignment.bind_get hbind, SemanticAssignment.getElem?_bind_eq]
      rfl
    · unfold Assignment.bindValue at hbind
      unfold Assignment.getType Assignment.getBinding
      rw [Assignment.bind_get_of_ne hbind heq, SemanticAssignment.bindValue,
        SemanticAssignment.getType_bind_ne semantic bound.id (.value runtime) query heq]
      exact hagrees.1 query
  · intro queryOpCode query
    by_cases heq : query.id = bound.id
    · unfold Assignment.bindValue at hbind
      unfold Assignment.getProperty Assignment.getBinding SemanticAssignment.bindValue
        SemanticAssignment.getProperty
      rw [heq, Assignment.bind_get hbind, SemanticAssignment.getElem?_bind_eq]
      rfl
    · unfold Assignment.bindValue at hbind
      unfold Assignment.getProperty Assignment.getBinding
      rw [Assignment.bind_get_of_ne hbind heq, SemanticAssignment.bindValue,
        SemanticAssignment.getProperty_bind_ne semantic bound.id (.value runtime) query heq]
      exact hagrees.2 queryOpCode query

private theorem Assignment.MetadataAgrees.bindType
    {concrete after : Assignment OpCode} {semantic : SemanticAssignment}
    (hagrees : Assignment.MetadataAgrees concrete semantic)
    (bound : Handle OpCode .type) (type : TypeAttr)
    (hbind : Assignment.bindType concrete bound type = some after) :
    Assignment.MetadataAgrees after (semantic.bindType bound type) := by
  constructor
  · intro query
    by_cases heq : query.id = bound.id
    · unfold Assignment.bindType at hbind
      unfold Assignment.getType Assignment.getBinding SemanticAssignment.bindType
        SemanticAssignment.getType
      rw [heq, Assignment.bind_get hbind, SemanticAssignment.getElem?_bind_eq]
      rfl
    · unfold Assignment.bindType at hbind
      unfold Assignment.getType Assignment.getBinding
      rw [Assignment.bind_get_of_ne hbind heq, SemanticAssignment.bindType,
        SemanticAssignment.getType_bind_ne semantic bound.id (.type type) query heq]
      exact hagrees.1 query
  · intro queryOpCode query
    by_cases heq : query.id = bound.id
    · unfold Assignment.bindType at hbind
      unfold Assignment.getProperty Assignment.getBinding SemanticAssignment.bindType
        SemanticAssignment.getProperty
      rw [heq, Assignment.bind_get hbind, SemanticAssignment.getElem?_bind_eq]
      rfl
    · unfold Assignment.bindType at hbind
      unfold Assignment.getProperty Assignment.getBinding
      rw [Assignment.bind_get_of_ne hbind heq, SemanticAssignment.bindType,
        SemanticAssignment.getProperty_bind_ne semantic bound.id (.type type) query heq]
      exact hagrees.2 queryOpCode query

private theorem Assignment.MetadataAgrees.bindProperty
    {concrete after : Assignment OpCode} {semantic : SemanticAssignment}
    (hagrees : Assignment.MetadataAgrees concrete semantic)
    (bound : Handle OpCode (.prop opCode)) (property : propertiesOf opCode)
    (hbind : Assignment.bindProperty concrete bound property = some after) :
    Assignment.MetadataAgrees after (semantic.bindProperty bound property) := by
  constructor
  · intro query
    by_cases heq : query.id = bound.id
    · unfold Assignment.bindProperty at hbind
      unfold Assignment.getType Assignment.getBinding SemanticAssignment.bindProperty
        SemanticAssignment.getType
      rw [heq, Assignment.bind_get hbind, SemanticAssignment.getElem?_bind_eq]
      rfl
    · unfold Assignment.bindProperty at hbind
      unfold Assignment.getType Assignment.getBinding
      rw [Assignment.bind_get_of_ne hbind heq, SemanticAssignment.bindProperty,
        SemanticAssignment.getType_bind_ne semantic bound.id (.property opCode property) query heq]
      exact hagrees.1 query
  · intro queryOpCode query
    by_cases heq : query.id = bound.id
    · unfold Assignment.bindProperty at hbind
      unfold Assignment.getProperty Assignment.getBinding SemanticAssignment.bindProperty
        SemanticAssignment.getProperty
      rw [heq, Assignment.bind_get hbind, SemanticAssignment.getElem?_bind_eq]
      by_cases hop : opCode = queryOpCode <;> simp [hop]
    · unfold Assignment.bindProperty at hbind
      unfold Assignment.getProperty Assignment.getBinding
      rw [Assignment.bind_get_of_ne hbind heq, SemanticAssignment.bindProperty,
        SemanticAssignment.getProperty_bind_ne semantic bound.id
          (.property opCode property) query heq]
      exact hagrees.2 queryOpCode query

private theorem Assignment.MetadataAgrees.bindValues
    {concrete after : Assignment OpCode} {semantic : SemanticAssignment}
    (hagrees : Assignment.MetadataAgrees concrete semantic)
    {handles : List (Handle OpCode .value)} {values : List ValuePtr}
    {runtimes : List RuntimeValue}
    (hvalues : values.length = handles.length)
    (hruntimes : runtimes.length = handles.length)
    (hbind : Assignment.bindValues concrete handles values = some after) :
    Assignment.MetadataAgrees after (semantic.bindValues handles runtimes) := by
  induction handles generalizing concrete semantic after values runtimes with
  | nil =>
    cases values <;> cases runtimes <;>
      simp_all [Assignment.bindValues, SemanticAssignment.bindValues]
  | cons handle handles ih =>
    cases values with
    | nil => simp at hvalues
    | cons value values =>
      cases runtimes with
      | nil => simp at hruntimes
      | cons runtime runtimes =>
        simp only [Assignment.bindValues, Option.bind_eq_bind] at hbind
        rw [Option.bind_eq_some_iff] at hbind
        obtain ⟨middle, hhead, htail⟩ := hbind
        simp only [SemanticAssignment.bindValues]
        exact ih (hagrees.bindValue handle value runtime hhead)
          (by simpa using hvalues) (by simpa using hruntimes) htail

private theorem MetadataTuple.Atom.resolve_agrees
    {Handle : Type} (atom : MetadataTuple.Atom OpCode Handle)
    {concrete : Assignment OpCode} {semantic : SemanticAssignment}
    (hagrees : Assignment.MetadataAgrees concrete semantic) (handle : Handle) :
    atom.resolve concrete handle = atom.resolve semantic handle := by
  cases atom with
  | type => exact hagrees.1 handle
  | property opCode => exact hagrees.2 opCode handle

private theorem MetadataTuple.Shape.resolve_agrees
    {Handles : Type} (shape : MetadataTuple.Shape OpCode Handles)
    {concrete : Assignment OpCode} {semantic : SemanticAssignment}
    (hagrees : Assignment.MetadataAgrees concrete semantic) (handles : Handles) :
    shape.resolve concrete handles = shape.resolve semantic handles := by
  induction shape generalizing concrete semantic with
  | unit => rfl
  | atom metadataAtom => exact metadataAtom.resolve_agrees hagrees handles
  | cons head tail tailIH =>
    simp only [MetadataTuple.Shape.resolve, Option.bind_eq_bind]
    rw [head.resolve_agrees hagrees]
    cases hhead : head.resolve semantic handles.1 with
    | none => rfl
    | some headValue => rw [tailIH hagrees]

private theorem Assignment.MetadataAgrees.resolve
    {Handles : Type} [bundle : IsMetadataTuple OpCode Handles]
    {concrete : Assignment OpCode} {semantic : SemanticAssignment}
    (hagrees : Assignment.MetadataAgrees concrete semantic) (handles : Handles) :
    MetadataTuple.resolve (self := bundle) concrete handles =
      MetadataTuple.resolve (self := bundle) semantic handles :=
  MetadataTuple.Shape.resolve_agrees bundle.shape hagrees handles

private theorem MetadataTuple.Atom.bind_agrees
    {Handle : Type} (atom : MetadataTuple.Atom OpCode Handle)
    {concrete concrete' : Assignment OpCode} {semantic semantic' : SemanticAssignment}
    (hagrees : Assignment.MetadataAgrees concrete semantic) (handle : Handle)
    (value : atom.Value)
    (hconcrete : atom.bind concrete handle value = some concrete')
    (hsemantic : atom.bind semantic handle value = some semantic') :
    Assignment.MetadataAgrees concrete' semantic' := by
  cases atom with
  | type =>
    change Assignment.bindType concrete handle value = some concrete' at hconcrete
    change some (semantic.bindType handle value) = some semantic' at hsemantic
    simp only [Option.some.injEq] at hsemantic
    subst semantic'
    exact hagrees.bindType handle value hconcrete
  | property opCode =>
    change Assignment.bindProperty concrete handle value = some concrete' at hconcrete
    change some (semantic.bindProperty handle value) = some semantic' at hsemantic
    simp only [Option.some.injEq] at hsemantic
    subst semantic'
    exact hagrees.bindProperty handle value hconcrete

private theorem MetadataTuple.Shape.bind_agrees
    {Handles : Type} (shape : MetadataTuple.Shape OpCode Handles)
    {concrete concrete' : Assignment OpCode} {semantic semantic' : SemanticAssignment}
    (hagrees : Assignment.MetadataAgrees concrete semantic) (handles : Handles)
    (values : shape.Values)
    (hconcrete : shape.bind concrete handles values = some concrete')
    (hsemantic : shape.bind semantic handles values = some semantic') :
    Assignment.MetadataAgrees concrete' semantic' := by
  induction shape generalizing concrete semantic concrete' semantic' with
  | unit =>
    change some concrete = some concrete' at hconcrete
    change some semantic = some semantic' at hsemantic
    simp at hconcrete hsemantic
    subst concrete'; subst semantic'
    exact hagrees
  | atom metadataAtom =>
    exact metadataAtom.bind_agrees hagrees handles values hconcrete hsemantic
  | cons head tail tailIH =>
    simp only [MetadataTuple.Shape.bind, Option.bind_eq_bind] at hconcrete hsemantic
    rw [Option.bind_eq_some_iff] at hconcrete hsemantic
    obtain ⟨concreteMiddle, hcHead, hcTail⟩ := hconcrete
    obtain ⟨semanticMiddle, hsHead, hsTail⟩ := hsemantic
    exact tailIH (head.bind_agrees hagrees handles.1 values.1 hcHead hsHead)
      handles.2 values.2 hcTail hsTail

private theorem Assignment.Refines.bindOp
    {ctx : WfIRContext OpCode} {targetState : InterpreterState ctx}
    {concrete after : Assignment OpCode} {semantic : SemanticAssignment}
    (hrefines : Assignment.Refines concrete semantic targetState)
    (bound : Handle OpCode .op) (operation : OperationPtr) (results : Array RuntimeValue)
    (hbind : Assignment.bindOp concrete bound operation = some after) :
    Assignment.Refines after (semantic.bindOp bound results) targetState := by
  intro query value sourceRuntime hconcrete hsemantic
  by_cases heq : query.id = bound.id
  · rw [Assignment.getValue_bindOp_of_eq bound query operation hbind heq] at hconcrete
    simp at hconcrete
  · rw [Assignment.getValue_bindOp_of_ne bound query operation hbind heq] at hconcrete
    rw [SemanticAssignment.bindOp,
      SemanticAssignment.getValue_bind_ne semantic bound.id (.op results) query heq] at hsemantic
    exact hrefines query value sourceRuntime hconcrete hsemantic

private theorem Assignment.Refines.bindType
    {ctx : WfIRContext OpCode} {targetState : InterpreterState ctx}
    {concrete after : Assignment OpCode} {semantic : SemanticAssignment}
    (hrefines : Assignment.Refines concrete semantic targetState)
    (bound : Handle OpCode .type) (type : TypeAttr)
    (hbind : Assignment.bindType concrete bound type = some after) :
    Assignment.Refines after (semantic.bindType bound type) targetState := by
  intro query value sourceRuntime hconcrete hsemantic
  by_cases heq : query.id = bound.id
  · rw [Assignment.getValue_bindType_eq bound query type hbind heq] at hconcrete
    simp at hconcrete
  · rw [Assignment.getValue_bindType_ne bound query type hbind heq] at hconcrete
    rw [SemanticAssignment.bindType,
      SemanticAssignment.getValue_bind_ne semantic bound.id (.type type) query heq] at hsemantic
    exact hrefines query value sourceRuntime hconcrete hsemantic

private theorem Assignment.Refines.bindProperty
    {ctx : WfIRContext OpCode} {targetState : InterpreterState ctx}
    {concrete after : Assignment OpCode} {semantic : SemanticAssignment}
    (hrefines : Assignment.Refines concrete semantic targetState)
    (bound : Handle OpCode (.prop opCode)) (property : propertiesOf opCode)
    (hbind : Assignment.bindProperty concrete bound property = some after) :
    Assignment.Refines after (semantic.bindProperty bound property) targetState := by
  intro query value sourceRuntime hconcrete hsemantic
  by_cases heq : query.id = bound.id
  · rw [Assignment.getValue_bindProperty_eq bound query property hbind heq] at hconcrete
    simp at hconcrete
  · rw [Assignment.getValue_bindProperty_ne bound query property hbind heq] at hconcrete
    rw [SemanticAssignment.bindProperty,
      SemanticAssignment.getValue_bind_ne semantic bound.id
        (.property opCode property) query heq] at hsemantic
    exact hrefines query value sourceRuntime hconcrete hsemantic

private theorem Assignment.Refines.bindValue
    {ctx : WfIRContext OpCode} {targetState : InterpreterState ctx}
    {concrete after : Assignment OpCode} {semantic : SemanticAssignment}
    (hrefines : Assignment.Refines concrete semantic targetState)
    (bound : Handle OpCode .value) (value : ValuePtr)
    (sourceRuntime targetRuntime : RuntimeValue)
    (htarget : targetState.variables.getVar? value = some targetRuntime)
    (hrefinement : sourceRuntime ⊒ targetRuntime)
    (hbind : Assignment.bindValue concrete bound value = some after) :
    Assignment.Refines after (semantic.bindValue bound sourceRuntime) targetState := by
  intro query queryValue queryRuntime hconcrete hsemantic
  by_cases heq : query.id = bound.id
  · rw [Assignment.getValue_bindValue_of_eq bound query value hbind heq] at hconcrete
    have hs : (semantic.bindValue bound sourceRuntime).getValue query = some sourceRuntime := by
      simp only [SemanticAssignment.bindValue, SemanticAssignment.getValue]
      rw [heq, SemanticAssignment.getElem?_bind_eq]
    rw [hs] at hsemantic
    simp only [Option.some.injEq] at hconcrete hsemantic
    subst queryValue
    subst queryRuntime
    exact ⟨targetRuntime, htarget, hrefinement⟩
  · rw [Assignment.getValue_bindValue_of_ne bound query value hbind heq] at hconcrete
    rw [SemanticAssignment.bindValue,
      SemanticAssignment.getValue_bind_ne semantic bound.id (.value sourceRuntime) query heq]
      at hsemantic
    exact hrefines query queryValue queryRuntime hconcrete hsemantic

private theorem Assignment.Refines.bindValues
    {ctx : WfIRContext OpCode} {targetState : InterpreterState ctx}
    {concrete after : Assignment OpCode} {semantic : SemanticAssignment}
    (hrefines : Assignment.Refines concrete semantic targetState)
    (handles : List (Handle OpCode .value)) (values : List ValuePtr)
    (sourceRuntimes targetRuntimes : List RuntimeValue)
    (hvalues : values.length = handles.length)
    (hsources : sourceRuntimes.length = handles.length)
    (htargets : targetRuntimes.length = handles.length)
    (hlookup : values.mapM targetState.variables.getVar? = some targetRuntimes)
    (hrefinement : sourceRuntimes.toArray ⊒ targetRuntimes.toArray)
    (hbind : Assignment.bindValues concrete handles values = some after) :
    Assignment.Refines after (semantic.bindValues handles sourceRuntimes) targetState := by
  induction handles generalizing concrete semantic after values sourceRuntimes targetRuntimes with
  | nil =>
    have hvalues' : values = [] := List.eq_nil_of_length_eq_zero (by simpa using hvalues)
    have hsources' : sourceRuntimes = [] := List.eq_nil_of_length_eq_zero (by simpa using hsources)
    have htargets' : targetRuntimes = [] := List.eq_nil_of_length_eq_zero (by simpa using htargets)
    subst values
    subst sourceRuntimes
    subst targetRuntimes
    simp [Assignment.bindValues] at hbind
    subst after
    exact hrefines
  | cons handle handles ih =>
    cases values with
    | nil => simp at hvalues
    | cons value values =>
      cases sourceRuntimes with
      | nil => simp at hsources
      | cons source sources =>
        cases hhead : targetState.variables.getVar? value with
        | none => simp [List.mapM_cons, hhead] at hlookup
        | some target =>
          cases htail : values.mapM targetState.variables.getVar? with
          | none => simp [List.mapM_cons, hhead, htail] at hlookup
          | some targets =>
            simp [List.mapM_cons, hhead, htail] at hlookup
            subst targetRuntimes
            have hrefinement' :=
              RuntimeValue.arrayIsRefinedBy_cons.mp (by simpa using hrefinement)
            simp only [Assignment.bindValues, Option.bind_eq_bind] at hbind
            rw [Option.bind_eq_some_iff] at hbind
            obtain ⟨middle, hbindHead, hbindTail⟩ := hbind
            simp only [SemanticAssignment.bindValues]
            exact ih
              (hrefines.bindValue handle value source target hhead hrefinement'.1 hbindHead)
              values sources targets (by simpa using hvalues) (by simpa using hsources)
              (by simpa using htargets) htail hrefinement'.2 hbindTail

private theorem MetadataTuple.Atom.bind_refines
    {Handle : Type} (atom : MetadataTuple.Atom OpCode Handle)
    {ctx : WfIRContext OpCode} {targetState : InterpreterState ctx}
    {concrete concrete' : Assignment OpCode} {semantic semantic' : SemanticAssignment}
    (hrefines : Assignment.Refines concrete semantic targetState) (handle : Handle)
    (value : atom.Value)
    (hconcrete : atom.bind concrete handle value = some concrete')
    (hsemantic : atom.bind semantic handle value = some semantic') :
    Assignment.Refines concrete' semantic' targetState := by
  cases atom with
  | type =>
    change Assignment.bindType concrete handle value = some concrete' at hconcrete
    change some (semantic.bindType handle value) = some semantic' at hsemantic
    simp only [Option.some.injEq] at hsemantic
    subst semantic'
    exact hrefines.bindType handle value hconcrete
  | property opCode =>
    change Assignment.bindProperty concrete handle value = some concrete' at hconcrete
    change some (semantic.bindProperty handle value) = some semantic' at hsemantic
    simp only [Option.some.injEq] at hsemantic
    subst semantic'
    exact hrefines.bindProperty handle value hconcrete

private theorem MetadataTuple.Shape.bind_refines
    {Handles : Type} (shape : MetadataTuple.Shape OpCode Handles)
    {ctx : WfIRContext OpCode} {targetState : InterpreterState ctx}
    {concrete concrete' : Assignment OpCode} {semantic semantic' : SemanticAssignment}
    (hrefines : Assignment.Refines concrete semantic targetState) (handles : Handles)
    (values : shape.Values)
    (hconcrete : shape.bind concrete handles values = some concrete')
    (hsemantic : shape.bind semantic handles values = some semantic') :
    Assignment.Refines concrete' semantic' targetState := by
  induction shape generalizing concrete semantic concrete' semantic' with
  | unit =>
    change some concrete = some concrete' at hconcrete
    change some semantic = some semantic' at hsemantic
    simp at hconcrete hsemantic
    subst concrete'; subst semantic'
    exact hrefines
  | atom metadataAtom =>
    exact metadataAtom.bind_refines hrefines handles values hconcrete hsemantic
  | cons head tail tailIH =>
    simp only [MetadataTuple.Shape.bind, Option.bind_eq_bind] at hconcrete hsemantic
    rw [Option.bind_eq_some_iff] at hconcrete hsemantic
    obtain ⟨concreteMiddle, hcHead, hcTail⟩ := hconcrete
    obtain ⟨semanticMiddle, hsHead, hsTail⟩ := hsemantic
    exact tailIH (head.bind_refines hrefines handles.1 values.1 hcHead hsHead)
      handles.2 values.2 hcTail hsTail

private theorem VariableState.mapM_getResults_of_setResultValues
    {ctx : WfIRContext OpCode} {state state' : VariableState ctx}
    {op : OperationPtr} {resultValues : Array RuntimeValue}
    {inBounds : op.InBounds ctx.raw}
    (hset : state.setResultValues? op resultValues inBounds = some state') :
    (op.getResults! ctx.raw).toList.mapM state'.getVar? = some resultValues.toList := by
  have hnumResults : op.getNumResults! ctx.raw = resultValues.size :=
    VariableState.setResultValues?.getNumRseults!_eq_size hset
  have hsize : (op.getResults! ctx.raw).size = resultValues.size := by
    rw [OperationPtr.getResults!.size_eq_getNumResults!]
    exact hnumResults
  have harray : (op.getResults! ctx.raw).mapM state'.getVar? = some resultValues := by
    rw [Array.mapM_eq_some_iff_of_size_eq hsize]
    intro i hi
    have hiNum : i < op.getNumResults! ctx.raw := by
      rw [hnumResults]
      simpa [hsize] using hi
    rw [OperationPtr.getResults!.getElem!_eq_getResult hiNum]
    exact VariableState.getVar?_getResult_of_setResultValues?
      (inBounds := inBounds) hiNum hset
  simpa [Array.mapM_eq_mapM_toList] using congrArg (Option.map Array.toList) harray

private theorem Assignment.Refines.getValuesList
    {ctx : WfIRContext OpCode}
    {concrete : Assignment OpCode} {semantic : SemanticAssignment}
    {targetState : InterpreterState ctx}
    (hrefines : (Assignment.Refines concrete) semantic targetState)
    {handles : List (Handle OpCode .value)} {values : List ValuePtr}
    {sourceRuntimes : List RuntimeValue}
    (hconcrete : handles.mapM (Assignment.getValue concrete) = some values)
    (hsemantic : handles.mapM (SemanticAssignment.getValue semantic) = some sourceRuntimes) :
    ∃ targetRuntimes,
      values.mapM targetState.variables.getVar? = some targetRuntimes ∧
      sourceRuntimes.toArray ⊒ targetRuntimes.toArray := by
  induction handles generalizing values sourceRuntimes with
  | nil =>
    simp at hconcrete hsemantic
    subst values
    subst sourceRuntimes
    exact ⟨[], by simp, RuntimeValue.arrayIsRefinedBy_nil⟩
  | cons handle handles ih =>
    cases hvalue : (Assignment.getValue concrete) handle with
    | none => simp [hvalue] at hconcrete
    | some value =>
      cases hvalues : handles.mapM (Assignment.getValue concrete) with
      | none => simp [hvalue, hvalues] at hconcrete
      | some valuesTail =>
        simp [hvalue, hvalues] at hconcrete
        subst values
        cases hsource : SemanticAssignment.getValue semantic handle with
        | none => simp [hsource] at hsemantic
        | some sourceRuntime =>
          cases hsources : handles.mapM (SemanticAssignment.getValue semantic) with
          | none => simp [hsource, hsources] at hsemantic
          | some sourceTail =>
            simp [hsource, hsources] at hsemantic
            subst sourceRuntimes
            obtain ⟨targetRuntime, htarget, hrefinement⟩ :=
              hrefines handle value sourceRuntime hvalue hsource
            obtain ⟨targetTail, htargetTail, hrefinementTail⟩ :=
              ih hvalues hsources
            refine ⟨targetRuntime :: targetTail, ?_, ?_⟩
            · simp [htarget, htargetTail]
            · exact RuntimeValue.arrayIsRefinedBy_cons.mpr
                ⟨hrefinement, hrefinementTail⟩

private theorem Assignment.Refines.getValues
    {ctx : WfIRContext OpCode}
    {concrete : Assignment OpCode} {semantic : SemanticAssignment}
    {targetState : InterpreterState ctx}
    (hrefines : (Assignment.Refines concrete) semantic targetState)
    {handles : Array (Handle OpCode .value)} {values : Array ValuePtr}
    {sourceRuntimes : Array RuntimeValue}
    (hconcrete : Assignment.getValues concrete handles = some values)
    (hsemantic : SemanticAssignment.getValues semantic handles = some sourceRuntimes) :
    ∃ targetRuntimes,
      values.mapM targetState.variables.getVar? = some targetRuntimes ∧
      sourceRuntimes ⊒ targetRuntimes := by
  have hconcreteList : handles.toList.mapM (Assignment.getValue concrete) = some values.toList := by
    simpa [Assignment.getValues, Array.mapM_eq_mapM_toList] using
      congrArg (Option.map Array.toList) hconcrete
  have hsemanticList : handles.toList.mapM (SemanticAssignment.getValue semantic) =
      some sourceRuntimes.toList := by
    simpa [SemanticAssignment.getValues, Array.mapM_eq_mapM_toList] using
      congrArg (Option.map Array.toList) hsemantic
  obtain ⟨targetRuntimes, htarget, hrefinement⟩ :=
    hrefines.getValuesList hconcreteList hsemanticList
  refine ⟨targetRuntimes.toArray, ?_, ?_⟩
  · simp [Array.mapM_eq_mapM_toList, htarget]
  · simpa using hrefinement

private def Assignment.MatchValuesInBounds
    (assignment : Assignment OpCode) (ctx : WfIRContext OpCode) : Prop :=
  ∀ handle value, Assignment.getValue assignment handle = some value → value.InBounds ctx.raw

private theorem Assignment.Rooted.valuesInBounds
    {assignment : Assignment OpCode} {ctx : WfIRContext OpCode} {root : OperationPtr}
    (hrooted : Assignment.Rooted assignment ctx root) :
    Assignment.MatchValuesInBounds assignment ctx := by
  intro handle value hget
  obtain ⟨consumer, hconsumerIn, _, _, hoperand⟩ := hrooted.2 handle value hget
  grind

private theorem WfIRContext.WithCreatedOps.getOpType!_eq
    {ctx ctx' : WfIRContext OpCode} {op : OperationPtr}
    (h : WfIRContext.WithCreatedOps ctx ctx') (hop : op.InBounds ctx.raw) :
    op.getOpType! ctx'.raw = op.getOpType! ctx.raw := by
  induction h with
  | Nil => rfl
  | CreatedOp ctx₁ ctx₂ ctx₃ hprefix hcreate ih =>
    rename_i newOp
    rcases hcreate with
      ⟨opType, resultTypes, operands, successors, regions, properties,
        h₁, h₂, h₃, h₄, hcreate⟩
    have hop₂ : op.InBounds ctx₂.raw := hprefix.inBounds_mono (.operation op) hop
    have hne : op ≠ newOp := by
      intro heq
      subst op
      exact (WfRewriter.createOp_new_not_inBounds newOp hcreate hop₂).elim
    rw [OperationPtr.getOpType!_WfRewriter_createOp hcreate]
    simp [hne, ih hop]

private theorem WfIRContext.WithCreatedOps.getOperands!_eq
    {ctx ctx' : WfIRContext OpCode} {op : OperationPtr}
    (h : WfIRContext.WithCreatedOps ctx ctx') (hop : op.InBounds ctx.raw) :
    op.getOperands! ctx'.raw = op.getOperands! ctx.raw := by
  induction h with
  | Nil => rfl
  | CreatedOp ctx₁ ctx₂ ctx₃ hprefix hcreate ih =>
    rename_i newOp
    rcases hcreate with
      ⟨opType, resultTypes, operands, successors, regions, properties,
        h₁, h₂, h₃, h₄, hcreate⟩
    have hop₂ : op.InBounds ctx₂.raw := hprefix.inBounds_mono (.operation op) hop
    have hne : op ≠ newOp := by
      intro heq
      subst op
      exact (WfRewriter.createOp_new_not_inBounds newOp hcreate hop₂).elim
    rw [OperationPtr.getOperands!_WfRewriter_createOp hcreate]
    simp [hne, ih hop]

private theorem WfIRContext.WithCreatedOps.getNumOperands!_eq
    {ctx ctx' : WfIRContext OpCode} {op : OperationPtr}
    (h : WfIRContext.WithCreatedOps ctx ctx') (hop : op.InBounds ctx.raw) :
    op.getNumOperands! ctx'.raw = op.getNumOperands! ctx.raw := by
  induction h with
  | Nil => rfl
  | CreatedOp ctx₁ ctx₂ ctx₃ hprefix hcreate ih =>
    rename_i newOp
    rcases hcreate with
      ⟨opType, resultTypes, operands, successors, regions, properties,
        h₁, h₂, h₃, h₄, hcreate⟩
    have hop₂ : op.InBounds ctx₂.raw := hprefix.inBounds_mono (.operation op) hop
    have hne : op ≠ newOp := by
      intro heq
      subst op
      exact (WfRewriter.createOp_new_not_inBounds newOp hcreate hop₂).elim
    rw [OperationPtr.getNumOperands!_WfRewriter_createOp hcreate]
    simp [hne, ih hop]

private theorem WfIRContext.WithCreatedOps.getResultTypes!_eq
    {ctx ctx' : WfIRContext OpCode} {op : OperationPtr}
    (h : WfIRContext.WithCreatedOps ctx ctx') (hop : op.InBounds ctx.raw) :
    op.getResultTypes! ctx'.raw = op.getResultTypes! ctx.raw := by
  induction h with
  | Nil => rfl
  | CreatedOp ctx₁ ctx₂ ctx₃ hprefix hcreate ih =>
    rename_i newOp
    rcases hcreate with
      ⟨opType, resultTypes, operands, successors, regions, properties,
        h₁, h₂, h₃, h₄, hcreate⟩
    have hop₂ : op.InBounds ctx₂.raw := hprefix.inBounds_mono (.operation op) hop
    have hne : op ≠ newOp := by
      intro heq
      subst op
      exact (WfRewriter.createOp_new_not_inBounds newOp hcreate hop₂).elim
    rw [OperationPtr.getResultTypes!_WfRewriter_createOp hcreate]
    simp [hne, ih hop]

private theorem WfIRContext.WithCreatedOps.getNumResults!_eq
    {ctx ctx' : WfIRContext OpCode} {op : OperationPtr}
    (h : WfIRContext.WithCreatedOps ctx ctx') (hop : op.InBounds ctx.raw) :
    op.getNumResults! ctx'.raw = op.getNumResults! ctx.raw := by
  induction h with
  | Nil => rfl
  | CreatedOp ctx₁ ctx₂ ctx₃ hprefix hcreate ih =>
    rename_i newOp
    rcases hcreate with
      ⟨opType, resultTypes, operands, successors, regions, properties,
        h₁, h₂, h₃, h₄, hcreate⟩
    have hop₂ : op.InBounds ctx₂.raw := hprefix.inBounds_mono (.operation op) hop
    have hne : op ≠ newOp := by
      intro heq
      subst op
      exact (WfRewriter.createOp_new_not_inBounds newOp hcreate hop₂).elim
    rw [OperationPtr.getNumResults!_WfRewriter_createOp hcreate]
    simp [hne, ih hop]

private theorem WfIRContext.WithCreatedOps.getSuccessors!_eq
    {ctx ctx' : WfIRContext OpCode} {op : OperationPtr}
    (h : WfIRContext.WithCreatedOps ctx ctx') (hop : op.InBounds ctx.raw) :
    op.getSuccessors! ctx'.raw = op.getSuccessors! ctx.raw := by
  induction h with
  | Nil => rfl
  | CreatedOp ctx₁ ctx₂ ctx₃ hprefix hcreate ih =>
    rename_i newOp
    rcases hcreate with
      ⟨opType, resultTypes, operands, successors, regions, properties,
        h₁, h₂, h₃, h₄, hcreate⟩
    have hop₂ : op.InBounds ctx₂.raw := hprefix.inBounds_mono (.operation op) hop
    have hne : op ≠ newOp := by
      intro heq
      subst op
      exact (WfRewriter.createOp_new_not_inBounds newOp hcreate hop₂).elim
    rw [OperationPtr.getSuccessors!_WfRewriter_createOp hcreate]
    simp [hne, ih hop]

private theorem WfIRContext.WithCreatedOps.getProperties!_eq
    {ctx ctx' : WfIRContext OpCode} {op : OperationPtr} {opCode : OpCode}
    (h : WfIRContext.WithCreatedOps ctx ctx') (hop : op.InBounds ctx.raw) :
    op.getProperties! ctx'.raw opCode = op.getProperties! ctx.raw opCode := by
  induction h with
  | Nil => rfl
  | CreatedOp ctx₁ ctx₂ ctx₃ hprefix hcreate ih =>
    rename_i newOp
    rcases hcreate with
      ⟨createdCode, resultTypes, operands, successors, regions, properties,
        h₁, h₂, h₃, h₄, hcreate⟩
    have hop₂ : op.InBounds ctx₂.raw := hprefix.inBounds_mono (.operation op) hop
    have hne : op ≠ newOp := by
      intro heq
      subst op
      exact (WfRewriter.createOp_new_not_inBounds newOp hcreate hop₂).elim
    rw [OperationPtr.getProperties!_WfRewriter_createOp hcreate]
    simp [hne, ih hop]

theorem WfIRContext.WithCreatedOps.valueType_eq
    {ctx ctx' : WfIRContext OpCode} {value : ValuePtr}
    (h : WfIRContext.WithCreatedOps ctx ctx') (hvalue : value.InBounds ctx.raw) :
    value.getType! ctx'.raw = value.getType! ctx.raw := by
  induction h with
  | Nil => rfl
  | CreatedOp ctx₁ ctx₂ ctx₃ hprefix hcreate ih =>
    rename_i newOp
    rcases hcreate with
      ⟨createdCode, resultTypes, operands, successors, regions, properties,
        h₁, h₂, h₃, h₄, hcreate⟩
    have hvalue₂ : value.InBounds ctx₂.raw := hprefix.inBounds_mono (.value value) hvalue
    rw [ValuePtr.getType!_WfRewriter_createOp hcreate]
    cases value with
    | blockArgument => simp [ih hvalue]
    | opResult result =>
      have hne : result.op ≠ newOp := by
        intro heq
        subst newOp
        have : result.op.InBounds ctx₂.raw := by grind
        exact (WfRewriter.createOp_new_not_inBounds result.op hcreate this).elim
      simp [hne, ih hvalue]

/-- Every concrete created-value binding names a value present in the context built so far. -/
private def Assignment.ValuesInBounds
    (created : Assignment OpCode) (ctx : WfIRContext OpCode) : Prop :=
  ∀ handle value, (Assignment.getValue created) handle = some value → value.InBounds ctx.raw

private theorem Assignment.ValuesInBounds.bindOp
    {created after : Assignment OpCode} {ctx : WfIRContext OpCode}
    (hinBounds : Assignment.ValuesInBounds created ctx) (bound : Handle OpCode .op)
    (operation : OperationPtr) (hbind : Assignment.bindOp created bound operation = some after) :
    Assignment.ValuesInBounds after ctx := by
  intro query value hget
  by_cases heq : query.id = bound.id
  · rw [Assignment.getValue_bindOp_of_eq bound query operation hbind heq] at hget
    simp at hget
  · apply hinBounds query value
    rwa [Assignment.getValue_bindOp_of_ne bound query operation hbind heq] at hget

private theorem Assignment.ValuesInBounds.bindValue
    {created after : Assignment OpCode} {ctx : WfIRContext OpCode}
    (hinBounds : Assignment.ValuesInBounds created ctx) (bound : Handle OpCode .value)
    (value : ValuePtr) (hvalue : value.InBounds ctx.raw)
    (hbind : Assignment.bindValue created bound value = some after) :
    Assignment.ValuesInBounds after ctx := by
  intro query queried hget
  by_cases heq : query.id = bound.id
  · rw [Assignment.getValue_bindValue_of_eq bound query value hbind heq] at hget
    simp only [Option.some.injEq] at hget
    simpa [hget] using hvalue
  · apply hinBounds query queried
    rwa [Assignment.getValue_bindValue_of_ne bound query value hbind heq] at hget

private theorem Assignment.ValuesInBounds.bindValues
    {created after : Assignment OpCode} {ctx : WfIRContext OpCode}
    (hinBounds : Assignment.ValuesInBounds created ctx)
    (handles : List (Handle OpCode .value)) (values : List ValuePtr)
    (hvalues : ∀ value ∈ values, value.InBounds ctx.raw)
    (hbind : Assignment.bindValues created handles values = some after) :
    Assignment.ValuesInBounds after ctx := by
  induction handles generalizing created after values with
  | nil =>
    cases values <;> simp [Assignment.bindValues] at hbind
    subst after
    exact hinBounds
  | cons handle handles ih =>
    cases values with
    | nil => simp [Assignment.bindValues] at hbind
    | cons value values =>
      simp only [Assignment.bindValues, Option.bind_eq_bind] at hbind
      rw [Option.bind_eq_some_iff] at hbind
      obtain ⟨middle, hhead, htail⟩ := hbind
      exact ih (hinBounds.bindValue handle value (hvalues value (by simp)) hhead)
        values (by intro tail hmem; exact hvalues tail (by simp [hmem])) htail

private theorem Assignment.ValuesInBounds.bindType
    {created after : Assignment OpCode} {ctx : WfIRContext OpCode}
    (hinBounds : (Assignment.ValuesInBounds created) ctx) (bound : Handle OpCode .type)
    (type : TypeAttr) (hbind : Assignment.bindType created bound type = some after) :
    (Assignment.ValuesInBounds after) ctx := by
  intro query value hget
  by_cases heq : query.id = bound.id
  · rw [Assignment.getValue_bindType_eq _ _ _ hbind heq] at hget
    simp at hget
  · apply hinBounds query value
    rw [Assignment.getValue_bindType_ne _ _ _ hbind heq] at hget
    exact hget

private theorem Assignment.ValuesInBounds.bindProperty
    {created after : Assignment OpCode} {ctx : WfIRContext OpCode}
    (hinBounds : (Assignment.ValuesInBounds created) ctx) (bound : Handle OpCode (.prop opCode))
    (property : propertiesOf opCode)
    (hbind : Assignment.bindProperty created bound property = some after) :
    (Assignment.ValuesInBounds after) ctx := by
  intro query value hget
  by_cases heq : query.id = bound.id
  · rw [Assignment.getValue_bindProperty_eq _ _ _ hbind heq] at hget
    simp at hget
  · apply hinBounds query value
    rw [Assignment.getValue_bindProperty_ne _ _ _ hbind heq] at hget
    exact hget

private theorem MetadataTuple.Atom.bind_valuesInBounds
    {Handle : Type} (metadataAtom : MetadataTuple.Atom OpCode Handle)
    {created created' : Assignment OpCode} {ctx : WfIRContext OpCode}
    (hinBounds : (Assignment.ValuesInBounds created) ctx) (handle : Handle) (value : metadataAtom.Value)
    (hbind : metadataAtom.bind created handle value = some created') :
    (Assignment.ValuesInBounds created') ctx := by
  cases metadataAtom with
  | type =>
    change Assignment.bindType created handle value = some created' at hbind
    exact hinBounds.bindType handle value hbind
  | property opCode =>
    change Assignment.bindProperty created handle value = some created' at hbind
    exact hinBounds.bindProperty handle value hbind

private theorem MetadataTuple.Shape.bind_valuesInBounds
    {Handles : Type} (shape : MetadataTuple.Shape OpCode Handles)
    {created created' : Assignment OpCode} {ctx : WfIRContext OpCode}
    (hinBounds : (Assignment.ValuesInBounds created) ctx) (handles : Handles) (values : shape.Values)
    (hbind : shape.bind created handles values = some created') :
    (Assignment.ValuesInBounds created') ctx := by
  induction shape generalizing created created' with
  | unit =>
    change some created = some created' at hbind
    simp at hbind; subst created'; exact hinBounds
  | atom metadataAtom =>
    exact metadataAtom.bind_valuesInBounds hinBounds handles values hbind
  | cons head tail tailIH =>
    simp only [MetadataTuple.Shape.bind, Option.bind_eq_bind] at hbind
    rw [Option.bind_eq_some_iff] at hbind
    obtain ⟨middle, hhead, htail⟩ := hbind
    exact tailIH (head.bind_valuesInBounds hinBounds handles.1 values.1 hhead)
      handles.2 values.2 htail

private theorem CreateProg.runDecls_type_eq_some_iff
    {decls : List (CreateDecl OpCode)} {ctx ctx' : WfIRContext OpCode}
    {created created' : Assignment OpCode} {operations : Array OperationPtr}
    {value : TypeAttr} {result : Handle OpCode .type} :
    CreateProg.runDecls (.type value result :: decls) ctx created =
        some (ctx', operations, created') ↔
      ∃ bound,
        Assignment.bindType created result value = some bound ∧
        CreateProg.runDecls decls ctx bound = some (ctx', operations, created') := by
  simp [CreateProg.runDecls, CreateDecl.run, Option.bind_eq_some_iff]
  grind

private theorem CreateDecl.run_withCreatedOp
    {decl : CreateDecl OpCode} {created created' : Assignment OpCode}
    {ctx ctx' : WfIRContext OpCode} {operations : Array OperationPtr}
    (hrun : decl.run created ctx = some (ctx', operations, created')) :
    WfIRContext.WithCreatedOps ctx ctx' := by
  cases decl with
  | type value result =>
    simp only [CreateDecl.run, Option.bind_eq_bind] at hrun
    rw [Option.bind_eq_some_iff] at hrun
    obtain ⟨bound, _, hrun⟩ := hrun
    simp only [pure, Option.some.injEq] at hrun
    rcases hrun with ⟨rfl, rfl, rfl⟩
    exact .Nil _
  | property opCode value result =>
    simp only [CreateDecl.run, Option.bind_eq_bind] at hrun
    rw [Option.bind_eq_some_iff] at hrun
    obtain ⟨bound, _, hrun⟩ := hrun
    simp only [pure, Option.some.injEq] at hrun
    rcases hrun with ⟨rfl, rfl, rfl⟩
    exact .Nil _
  | operation opCode operands resultTypes property opHandle results =>
    simp only [CreateDecl.run, Option.bind_eq_bind] at hrun
    rw [Option.bind_eq_some_iff] at hrun
    obtain ⟨resolvedOperands, _, hrun⟩ := hrun
    rw [Option.bind_eq_some_iff] at hrun
    obtain ⟨resolvedTypes, _, hrun⟩ := hrun
    rw [Option.bind_eq_some_iff] at hrun
    obtain ⟨resolvedProperty, _, hrun⟩ := hrun
    rw [Option.bind_eq_some_iff] at hrun
    obtain ⟨_, _, hrun⟩ := hrun
    split at hrun
    · rename_i hoper
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨createdPair, hcreate, hrun⟩ := hrun
      rcases createdPair with ⟨newCtx, newOp⟩
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨withOp, _, hrun⟩ := hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨withResults, _, hrun⟩ := hrun
      simp only [pure, Option.some.injEq] at hrun
      rcases hrun with ⟨rfl, rfl, rfl⟩
      exact .CreatedOp ctx ctx ctx' (.Nil ctx)
        ⟨opCode, resolvedTypes, resolvedOperands, #[], #[], resolvedProperty,
          hoper, by simp, by simp, by simp, hcreate⟩
    · simp at hrun
  | applyNative => simp [CreateDecl.run] at hrun

private theorem CreateDecl.run_operationInBounds
    {decl : CreateDecl OpCode} {created created' : Assignment OpCode}
    {ctx ctx' : WfIRContext OpCode} {operations : Array OperationPtr}
    (hrun : decl.run created ctx = some (ctx', operations, created')) :
    ∀ operation ∈ operations, operation.InBounds ctx'.raw := by
  cases decl with
  | type value result =>
    simp [CreateDecl.run, Option.bind_eq_some_iff] at hrun
    rcases hrun with ⟨_, _, rfl, rfl, rfl⟩
    simp
  | property opCode value result =>
    simp [CreateDecl.run, Option.bind_eq_some_iff] at hrun
    rcases hrun with ⟨_, _, rfl, rfl, rfl⟩
    simp
  | operation opCode operands resultTypes property opHandle results =>
    simp only [CreateDecl.run, Option.bind_eq_bind] at hrun
    rw [Option.bind_eq_some_iff] at hrun
    obtain ⟨resolvedOperands, _, hrun⟩ := hrun
    rw [Option.bind_eq_some_iff] at hrun
    obtain ⟨resolvedTypes, _, hrun⟩ := hrun
    rw [Option.bind_eq_some_iff] at hrun
    obtain ⟨resolvedProperty, _, hrun⟩ := hrun
    rw [Option.bind_eq_some_iff] at hrun
    obtain ⟨_, _, hrun⟩ := hrun
    split at hrun
    · rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨createdPair, hcreate, hrun⟩ := hrun
      rcases createdPair with ⟨newCtx, newOp⟩
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨withOp, _, hrun⟩ := hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨withResults, _, hrun⟩ := hrun
      simp only [pure, Option.some.injEq] at hrun
      rcases hrun with ⟨rfl, rfl, rfl⟩
      intro operation hmem
      simp only [Array.mem_singleton] at hmem
      subst operation
      exact WfRewriter.createOp_new_inBounds newOp hcreate
    · simp at hrun
  | applyNative => simp [CreateDecl.run] at hrun

private theorem CreateDecl.run_valuesInBounds
    {decl : CreateDecl OpCode} {created created' : Assignment OpCode}
    {ctx ctx' : WfIRContext OpCode} {operations : Array OperationPtr}
    (hcreated : Assignment.ValuesInBounds created ctx)
    (hrun : decl.run created ctx = some (ctx', operations, created')) :
    Assignment.ValuesInBounds created' ctx' := by
  cases decl with
  | type value result =>
    simp only [CreateDecl.run, Option.bind_eq_bind] at hrun
    rw [Option.bind_eq_some_iff] at hrun
    obtain ⟨bound, hbind, hrun⟩ := hrun
    simp only [pure, Option.some.injEq] at hrun
    rcases hrun with ⟨rfl, rfl, rfl⟩
    exact hcreated.bindType result value hbind
  | property opCode value result =>
    simp only [CreateDecl.run, Option.bind_eq_bind] at hrun
    rw [Option.bind_eq_some_iff] at hrun
    obtain ⟨bound, hbind, hrun⟩ := hrun
    simp only [pure, Option.some.injEq] at hrun
    rcases hrun with ⟨rfl, rfl, rfl⟩
    exact hcreated.bindProperty result value hbind
  | operation opCode operands resultTypes property opHandle results =>
    have hctxChange := CreateDecl.run_withCreatedOp hrun
    simp only [CreateDecl.run, Option.bind_eq_bind] at hrun
    rw [Option.bind_eq_some_iff] at hrun
    obtain ⟨resolvedOperands, _, hrun⟩ := hrun
    rw [Option.bind_eq_some_iff] at hrun
    obtain ⟨resolvedTypes, _, hrun⟩ := hrun
    rw [Option.bind_eq_some_iff] at hrun
    obtain ⟨resolvedProperty, _, hrun⟩ := hrun
    rw [Option.bind_eq_some_iff] at hrun
    obtain ⟨_, _, hrun⟩ := hrun
    split at hrun
    · rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨createdPair, hcreate, hrun⟩ := hrun
      rcases createdPair with ⟨newCtx, newOp⟩
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨withOp, hbindOp, hrun⟩ := hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨withResults, hbindResults, hrun⟩ := hrun
      simp only [pure, Option.some.injEq] at hrun
      rcases hrun with ⟨rfl, rfl, rfl⟩
      have hbase : Assignment.ValuesInBounds created ctx' := by
        intro handle value hget
        exact hctxChange.inBounds_mono (.value value) (hcreated handle value hget)
      apply (hbase.bindOp opHandle newOp hbindOp).bindValues
        results.toList (newOp.getResults! ctx'.raw).toList
      · intro value hmem
        grind
      · exact hbindResults
    · simp at hrun
  | applyNative => simp [CreateDecl.run] at hrun

private theorem WfIRContext.WithCreatedOps.trans
    {ctx₁ ctx₂ ctx₃ : WfIRContext OpCode}
    (h₁ : WfIRContext.WithCreatedOps ctx₁ ctx₂)
    (h₂ : WfIRContext.WithCreatedOps ctx₂ ctx₃) :
    WfIRContext.WithCreatedOps ctx₁ ctx₃ := by
  induction h₂ with
  | Nil => exact h₁
  | CreatedOp ctx₂ ctx₃ ctx₄ hprefix hcreate ih =>
    exact .CreatedOp ctx₁ ctx₃ ctx₄ (ih h₁) hcreate

private theorem CreateProg.runDecls_withCreatedOps
    {decls : List (CreateDecl OpCode)}
    {ctx ctx' : WfIRContext OpCode} {created created' : Assignment OpCode}
    {operations : Array OperationPtr}
    (hrun : CreateProg.runDecls decls ctx created =
      some (ctx', operations, created')) :
    WfIRContext.WithCreatedOps ctx ctx' := by
  induction decls generalizing ctx created ctx' operations created' with
  | nil =>
    simp [CreateProg.runDecls] at hrun
    rcases hrun with ⟨rfl, rfl, rfl⟩
    exact .Nil _
  | cons decl decls ih =>
    cases decl with
    | type value result =>
      rw [CreateProg.runDecls_type_eq_some_iff] at hrun
      obtain ⟨bound, _, htail⟩ := hrun
      exact ih htail
    | property opCode value result =>
      simp only [CreateProg.runDecls, Option.bind_eq_bind] at hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨bound, _, htail⟩ := hrun
      exact ih htail
    | @applyNative Inputs Outputs inputBundle outputBundle inputs rewrite outputs =>
      simp only [CreateProg.runDecls, Option.bind_eq_bind] at hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨inputValues, _, hrun⟩ := hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨outputValues, _, hrun⟩ := hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨bound, _, htail⟩ := hrun
      exact ih htail
    | operation opCode operands resultTypes property opHandle results =>
      simp only [CreateProg.runDecls, Option.bind_eq_bind] at hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨createdHead, hhead, hrun⟩ := hrun
      rcases createdHead with ⟨headCtx, headOps, headCreated⟩
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨createdTail, htail, hrun⟩ := hrun
      rcases createdTail with ⟨tailCtx, tailOps, tailCreated⟩
      simp only [pure, Option.some.injEq] at hrun
      rcases hrun with ⟨rfl, rfl, rfl⟩
      exact WfIRContext.WithCreatedOps.trans
        (CreateDecl.run_withCreatedOp hhead) (ih htail)

private theorem CreateProg.runDecls_valuesInBounds
    {decls : List (CreateDecl OpCode)}
    {ctx ctx' : WfIRContext OpCode} {created created' : Assignment OpCode}
    {operations : Array OperationPtr}
    (hcreated : Assignment.ValuesInBounds created ctx)
    (hrun : CreateProg.runDecls decls ctx created =
      some (ctx', operations, created')) :
    Assignment.ValuesInBounds created' ctx' := by
  induction decls generalizing ctx created ctx' operations created' with
  | nil =>
    simp [CreateProg.runDecls] at hrun
    rcases hrun with ⟨rfl, rfl, rfl⟩
    exact hcreated
  | cons decl decls ih =>
    cases decl with
    | type value result =>
      rw [CreateProg.runDecls_type_eq_some_iff] at hrun
      obtain ⟨bound, hbind, htail⟩ := hrun
      exact ih (hcreated.bindType result value hbind) htail
    | property opCode value result =>
      simp only [CreateProg.runDecls, Option.bind_eq_bind] at hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨bound, hbind, htail⟩ := hrun
      exact ih (hcreated.bindProperty result value hbind) htail
    | @applyNative Inputs Outputs inputBundle outputBundle inputs rewrite outputs =>
      simp only [CreateProg.runDecls, Option.bind_eq_bind] at hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨inputValues, _, hrun⟩ := hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨outputValues, _, hrun⟩ := hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨bound, hbind, htail⟩ := hrun
      exact ih
        (MetadataTuple.Shape.bind_valuesInBounds
          (@IsMetadataTuple.shape OpCode inferInstance Outputs outputBundle)
          hcreated outputs outputValues hbind)
        htail
    | operation opCode operands resultTypes property opHandle results =>
      simp only [CreateProg.runDecls, Option.bind_eq_bind] at hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨createdHead, hhead, hrun⟩ := hrun
      rcases createdHead with ⟨headCtx, headOps, headCreated⟩
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨createdTail, htail, hrun⟩ := hrun
      rcases createdTail with ⟨tailCtx, tailOps, tailCreated⟩
      simp only [pure, Option.some.injEq] at hrun
      rcases hrun with ⟨rfl, rfl, rfl⟩
      exact ih (CreateDecl.run_valuesInBounds hcreated hhead) htail

private theorem CreateProg.runDecls_operationsInBounds
    {decls : List (CreateDecl OpCode)}
    {ctx ctx' : WfIRContext OpCode} {created created' : Assignment OpCode}
    {operations : Array OperationPtr}
    (hrun : CreateProg.runDecls decls ctx created =
      some (ctx', operations, created')) :
    ∀ operation ∈ operations, operation.InBounds ctx'.raw := by
  induction decls generalizing ctx created ctx' operations created' with
  | nil =>
    simp [CreateProg.runDecls] at hrun
    rcases hrun with ⟨rfl, rfl, rfl⟩
    simp
  | cons decl decls ih =>
    cases decl with
    | type value result =>
      rw [CreateProg.runDecls_type_eq_some_iff] at hrun
      obtain ⟨bound, _, htail⟩ := hrun
      exact ih htail
    | property opCode value result =>
      simp only [CreateProg.runDecls, Option.bind_eq_bind] at hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨bound, _, htail⟩ := hrun
      exact ih htail
    | @applyNative Inputs Outputs inputBundle outputBundle inputs rewrite outputs =>
      simp only [CreateProg.runDecls, Option.bind_eq_bind] at hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨inputValues, _, hrun⟩ := hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨outputValues, _, hrun⟩ := hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨bound, _, htail⟩ := hrun
      exact ih htail
    | operation opCode operands resultTypes property opHandle results =>
      simp only [CreateProg.runDecls, Option.bind_eq_bind] at hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨createdHead, hhead, hrun⟩ := hrun
      rcases createdHead with ⟨headCtx, headOps, headCreated⟩
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨createdTail, htail, hrun⟩ := hrun
      rcases createdTail with ⟨tailCtx, tailOps, tailCreated⟩
      simp only [pure, Option.some.injEq] at hrun
      rcases hrun with ⟨rfl, rfl, rfl⟩
      intro operation hopen
      simp only [Array.mem_append] at hopen
      rcases hopen with hopen | hopen
      · have hheadIn := CreateDecl.run_operationInBounds hhead operation hopen
        exact (CreateProg.runDecls_withCreatedOps htail).inBounds_mono
          (.operation operation) hheadIn
      · exact ih htail operation hopen

private theorem CreateDecl.interpret
    {decl : CreateDecl OpCode} {matched : Assignment OpCode}
    {semanticMatched : SemanticAssignment}
    {created created' : Assignment OpCode}
    {semanticCreated semanticCreated' : SemanticAssignment}
    {ctx ctx' finalCtx : WfIRContext OpCode} {operations : Array OperationPtr}
    {targetState : InterpreterState finalCtx}
    (hsupported : decl.Supported)
    (hrun : decl.run created ctx = some (ctx', operations, created'))
    (heval : decl.eval semanticCreated = some semanticCreated')
    (hsuffix : WfIRContext.WithCreatedOps ctx' finalCtx)
    (hmatchedBounds : Assignment.MatchValuesInBounds matched ctx)
    (hcreatedBounds : Assignment.ValuesInBounds created ctx)
    (hmatched : Assignment.MatchRefines matched semanticMatched targetState)
    (hcreated : Assignment.Refines created semanticCreated targetState)
    (hmetadata : Assignment.MetadataAgrees created semanticCreated) :
    ∃ afterCreation,
      interpretOpList operations.toList targetState
          (by
            intro operation hmem
            exact hsuffix.inBounds_mono (.operation operation)
              (CreateDecl.run_operationInBounds hrun operation (by simpa using hmem))) =
        .ok (afterCreation, none) ∧
      afterCreation.memory = targetState.memory ∧
      Assignment.MatchRefines matched semanticMatched afterCreation ∧
      Assignment.Refines created' semanticCreated' afterCreation ∧
      Assignment.MetadataAgrees created' semanticCreated' := by
  cases decl with
  | type value result =>
    simp only [CreateDecl.run, Option.bind_eq_bind] at hrun
    rw [Option.bind_eq_some_iff] at hrun
    obtain ⟨bound, hbind, hrun⟩ := hrun
    simp only [pure, Option.some.injEq] at hrun
    rcases hrun with ⟨rfl, rfl, rfl⟩
    simp only [CreateDecl.eval, Option.some.injEq] at heval
    subst semanticCreated'
    exact ⟨targetState, by simp [interpretOpList], rfl, hmatched,
      hcreated.bindType result value hbind,
      hmetadata.bindType result value hbind⟩
  | property opCode property result =>
    simp only [CreateDecl.run, Option.bind_eq_bind] at hrun
    rw [Option.bind_eq_some_iff] at hrun
    obtain ⟨bound, hbind, hrun⟩ := hrun
    simp only [pure, Option.some.injEq] at hrun
    rcases hrun with ⟨rfl, rfl, rfl⟩
    simp only [CreateDecl.eval, Option.some.injEq] at heval
    subst semanticCreated'
    exact ⟨targetState, by simp [interpretOpList], rfl, hmatched,
      hcreated.bindProperty result property hbind,
      hmetadata.bindProperty result property hbind⟩
  | operation opCode operands resultTypes propertySource opHandle results =>
    rcases hsupported with ⟨hterminator, heffects⟩
    simp only [CreateDecl.run, Option.bind_eq_bind] at hrun
    rw [Option.bind_eq_some_iff] at hrun
    obtain ⟨concreteOperands, hconcreteOperands, hrun⟩ := hrun
    rw [Option.bind_eq_some_iff] at hrun
    obtain ⟨concreteResultTypes, hconcreteResultTypes, hrun⟩ := hrun
    rw [Option.bind_eq_some_iff] at hrun
    obtain ⟨properties, hconcreteProperties, hrun⟩ := hrun
    rw [Option.bind_eq_some_iff] at hrun
    obtain ⟨_, hresultGuard, hrun⟩ := hrun
    have hresultSize : results.size = concreteResultTypes.size := by
      simpa [_root_.guard] using hresultGuard
    split at hrun
    · rename_i hoper
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨createdPair, hcreate, hrun⟩ := hrun
      rcases createdPair with ⟨newCtx, newOp⟩
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨createdWithOp, hbindOp, hrun⟩ := hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨createdWithResults, hbindResults, hrun⟩ := hrun
      simp only [pure, Option.some.injEq] at hrun
      rcases hrun with ⟨rfl, rfl, rfl⟩
      simp only [CreateDecl.eval, Option.bind_eq_bind] at heval
      rw [Option.bind_eq_some_iff] at heval
      obtain ⟨sourceResults, hsourceResults, hsemanticFinal⟩ := heval
      simp only [pure, Option.some.injEq] at hsemanticFinal
      subst semanticCreated'
      simp [CreateDecl.evalResults, Option.bind_eq_some_iff] at hsourceResults
      obtain ⟨sourceOperands, hsemanticOperands, sourceResultTypes,
        hsourceResultTypes, sourceProperties, hsourceProperties,
        hsourceResults⟩ := hsourceResults
      have hsemanticProperties :
          semanticCreated.getProperty propertySource = some properties := by
        rw [← hmetadata.2 opCode propertySource]
        exact hconcreteProperties
      have hsemanticResultTypes :
          semanticCreated.getTypes resultTypes = some concreteResultTypes := by
        have hgetType : Assignment.getType created = SemanticAssignment.getType semanticCreated :=
          funext hmetadata.1
        unfold Assignment.getTypes at hconcreteResultTypes
        unfold SemanticAssignment.getTypes
        rw [← hgetType]
        exact hconcreteResultTypes
      rw [hsemanticResultTypes] at hsourceResultTypes
      simp only [Option.some.injEq] at hsourceResultTypes
      subst sourceResultTypes
      rw [hsemanticProperties] at hsourceProperties
      simp only [Option.some.injEq] at hsourceProperties
      subst sourceProperties
      cases hsourceInterpret :
          interpretOp' opCode properties concreteResultTypes sourceOperands #[] .empty with
      | fail => simp [hsourceInterpret] at hsourceResults
      | ub => simp [hsourceInterpret] at hsourceResults
      | ok output =>
        rcases output with ⟨interpretedResults, sourceMemory, sourceControlFlow⟩
        cases sourceControlFlow with
        | some sourceControlFlow => simp [hsourceInterpret] at hsourceResults
        | none =>
          simp [hsourceInterpret] at hsourceResults
          subst interpretedResults
          obtain ⟨targetOperands, htargetOperands, hrefineOperands⟩ :=
            hcreated.getValues hconcreteOperands hsemanticOperands
          have hnewOpIn : newOp.InBounds finalCtx.raw :=
            hsuffix.inBounds_mono (.operation newOp)
              (WfRewriter.createOp_new_inBounds newOp hcreate)
          have hnewOpType : newOp.getOpType! finalCtx.raw = opCode := by
            rw [WfIRContext.WithCreatedOps.getOpType!_eq hsuffix
              (WfRewriter.createOp_new_inBounds newOp hcreate)]
            simpa using OperationPtr.getOpType!_WfRewriter_createOp
              (operation := newOp) hcreate
          have hnewOperands : newOp.getOperands! finalCtx.raw = concreteOperands := by
            rw [WfIRContext.WithCreatedOps.getOperands!_eq hsuffix
              (WfRewriter.createOp_new_inBounds newOp hcreate)]
            simpa using OperationPtr.getOperands!_WfRewriter_createOp
              (operation := newOp) hcreate
          have hnewResultTypes :
              newOp.getResultTypes! finalCtx.raw = concreteResultTypes := by
            rw [WfIRContext.WithCreatedOps.getResultTypes!_eq hsuffix
              (WfRewriter.createOp_new_inBounds newOp hcreate)]
            simpa using OperationPtr.getResultTypes!_WfRewriter_createOp
              (operation := newOp) hcreate
          have hnewSuccessors : newOp.getSuccessors! finalCtx.raw = #[] := by
            rw [WfIRContext.WithCreatedOps.getSuccessors!_eq hsuffix
              (WfRewriter.createOp_new_inBounds newOp hcreate)]
            simpa using OperationPtr.getSuccessors!_WfRewriter_createOp
              (operation := newOp) hcreate
          have hnewProperties : newOp.getProperties! finalCtx.raw opCode = properties := by
            rw [WfIRContext.WithCreatedOps.getProperties!_eq hsuffix
              (WfRewriter.createOp_new_inBounds newOp hcreate)]
            simpa using OperationPtr.getProperties!_WfRewriter_createOp
              (operation := newOp) (dialectOpType := opCode) hcreate
          have htargetOperandValues :
              targetState.variables.getOperandValues newOp = some targetOperands := by
            simpa [VariableState.getOperandValues, hnewOperands] using htargetOperands
          have hnewPure : newOp.Pure finalCtx.raw := by
            apply OperationPtr.Pure.of_getEffects_eq_none
            rw [hnewOpType]
            change HasOpInfo.getEffects opCode
              (newOp.getProperties! finalCtx.raw opCode) == .none
            rw [hnewProperties]
            simp [heffects properties]
          have hmonotone := interpretOp'_monotone opCode properties concreteResultTypes
            sourceOperands targetOperands #[] .empty hrefineOperands
          rw [hsourceInterpret] at hmonotone
          simp only [Interp.isRefinedBy_ok_target_iff, Prod.exists] at hmonotone
          obtain ⟨targetResults, targetMemory, targetControlFlow, htargetInterpret,
              hrefineResults, htargetMemory, htargetControlFlow⟩ := hmonotone
          have htargetControlFlowNone : targetControlFlow = none :=
            controlFlow_eq_none_of_isTerminator_eq_false hterminator htargetInterpret
          subst targetControlFlow
          have htargetEmptyRaw : newOp.interpret finalCtx.raw targetOperands .empty =
              .ok (targetResults, targetMemory, none) := by
            simp only [OperationPtr.interpret]
            rw [hnewOpType]
            change interpretOp' opCode (newOp.getProperties! finalCtx.raw opCode)
              (newOp.getResultTypes! finalCtx.raw) targetOperands
              (newOp.getSuccessors! finalCtx.raw) .empty = _
            simpa [hnewProperties, hnewResultTypes, hnewSuccessors] using htargetInterpret
          have htargetMemoryEmpty : targetMemory = .empty :=
            (hnewPure.interpretOp'_eq_ok_implies_memory_eq htargetEmptyRaw).symm
          subst targetMemory
          have htargetRaw : newOp.interpret finalCtx.raw targetOperands targetState.memory =
              .ok (targetResults, targetState.memory, none) := by
            simp only [OperationPtr.interpret] at htargetEmptyRaw ⊢
            rw [hnewPure targetOperands targetState.memory MemoryState.empty]
            simp [htargetEmptyRaw, Interp.map]
          have htargetConforms : RuntimeValue.ArrayConforms targetResults
              (newOp.getResultTypes! finalCtx.raw) := by
            rw [hnewResultTypes]
            exact interpretOp'_results_conform_of_eq_some htargetInterpret
          obtain ⟨afterCreation, hinterpretCreated, hmemoryCreated, hsetCreated⟩ :=
            interpretOp_forward (inBounds := hnewOpIn)
              htargetOperandValues htargetRaw htargetConforms
          have hmatchedAfter : Assignment.MatchRefines matched semanticMatched afterCreation := by
            intro handle value sourceRuntime hconcrete hsemantic
            obtain ⟨targetRuntime, htarget, hrefines⟩ :=
              hmatched handle value sourceRuntime hconcrete hsemantic
            have hvalueIn := hmatchedBounds handle value hconcrete
            have hnotMem : value ∉ newOp.getResults! finalCtx.raw := by
              intro hmem
              simp only [OperationPtr.getResults!.mem_iff_exists_index] at hmem
              obtain ⟨index, hindex, hvalue⟩ := hmem
              subst value
              have hopOld : newOp.InBounds ctx.raw := by grind
              exact (WfRewriter.createOp_new_not_inBounds newOp hcreate hopOld).elim
            exact ⟨targetRuntime,
              (VariableState.getVar?_setResultValues?_of_notMem_getResults!
                (inBounds := hnewOpIn) hnotMem hsetCreated).trans htarget, hrefines⟩
          have hnewNumResults :
              newOp.getNumResults! ctx'.raw = concreteResultTypes.size := by
            simpa using OperationPtr.getNumResults!_WfRewriter_createOp
              (operation := newOp) hcreate
          have hnewResultsEq : newOp.getResults! finalCtx.raw =
              newOp.getResults! ctx'.raw := by
            apply Array.ext
            · simp only [OperationPtr.getResults!.size_eq_getNumResults!]
              exact WfIRContext.WithCreatedOps.getNumResults!_eq hsuffix
                (WfRewriter.createOp_new_inBounds newOp hcreate)
            · intro i hiFinal hiNew
              rw [OperationPtr.getResults!.getElem_eq_getResult (by simpa using hiFinal),
                OperationPtr.getResults!.getElem_eq_getResult (by simpa using hiNew)]
          have htargetResultValues :
              (newOp.getResults! ctx'.raw).toList.mapM afterCreation.variables.getVar? =
                some targetResults.toList := by
            rw [← hnewResultsEq]
            exact VariableState.mapM_getResults_of_setResultValues
              (inBounds := hnewOpIn) hsetCreated
          have hcreatedBaseAfter : Assignment.Refines created semanticCreated afterCreation := by
            intro handle value sourceRuntime hconcrete hsemantic
            obtain ⟨targetRuntime, htarget, hrefines⟩ :=
              hcreated handle value sourceRuntime hconcrete hsemantic
            have hvalueIn := hcreatedBounds handle value hconcrete
            have hnotMem : value ∉ newOp.getResults! finalCtx.raw := by
              intro hmem
              simp only [OperationPtr.getResults!.mem_iff_exists_index] at hmem
              obtain ⟨index, hindex, hvalue⟩ := hmem
              subst value
              have hopOld : newOp.InBounds ctx.raw := by grind
              exact (WfRewriter.createOp_new_not_inBounds newOp hcreate hopOld).elim
            exact ⟨targetRuntime,
              (VariableState.getVar?_setResultValues?_of_notMem_getResults!
                (inBounds := hnewOpIn) hnotMem hsetCreated).trans htarget, hrefines⟩
          have hcreatedAfter :
              Assignment.Refines created'
                ((semanticCreated.bindOp opHandle sourceResults).bindValues
                  results.toList sourceResults.toList) afterCreation := by
            rw [hnewResultTypes] at htargetConforms
            apply (hcreatedBaseAfter.bindOp opHandle newOp sourceResults hbindOp).bindValues
              results.toList (newOp.getResults! ctx'.raw).toList
              sourceResults.toList targetResults.toList
            · simp only [Array.length_toList, OperationPtr.getResults!.size_eq_getNumResults!]
              omega
            · simp only [Array.length_toList]
              unfold RuntimeValue.arrayIsRefinedBy at hrefineResults
              unfold RuntimeValue.ArrayConforms at htargetConforms
              omega
            · simp only [Array.length_toList]
              unfold RuntimeValue.ArrayConforms at htargetConforms
              omega
            · exact htargetResultValues
            · simpa using hrefineResults
            · exact hbindResults
          have hmetadataAfter :
              Assignment.MetadataAgrees created'
                ((semanticCreated.bindOp opHandle sourceResults).bindValues
                  results.toList sourceResults.toList) := by
            apply Assignment.MetadataAgrees.bindValues
              (hmetadata.bindOp opHandle newOp sourceResults hbindOp)
              (handles := results.toList)
              (values := (newOp.getResults! ctx'.raw).toList)
              (runtimes := sourceResults.toList)
            · simp only [Array.length_toList, OperationPtr.getResults!.size_eq_getNumResults!]
              omega
            · simp only [Array.length_toList]
              rw [hnewResultTypes] at htargetConforms
              unfold RuntimeValue.arrayIsRefinedBy at hrefineResults
              unfold RuntimeValue.ArrayConforms at htargetConforms
              omega
            · exact hbindResults
          refine ⟨afterCreation, ?_, hmemoryCreated, hmatchedAfter,
            hcreatedAfter, hmetadataAfter⟩
          have hsingleton :
              interpretOpList [newOp] targetState
                  (by intro operation hmem; simp at hmem; subst operation; exact hnewOpIn) =
                .ok (afterCreation, none) := by
            rw [interpretOpList_cons, hinterpretCreated]
            exact interpretOpList_nil
          exact hsingleton
    · simp at hrun
  | applyNative => simp [CreateDecl.run] at hrun


private theorem CreateProg.interpret_runDecls
    {decls : List (CreateDecl OpCode)} {matched : Assignment OpCode}
    {semanticMatched : SemanticAssignment}
    {ctx finalCtx : WfIRContext OpCode} {created finalCreated : Assignment OpCode}
    {semanticCreated finalSemanticCreated : SemanticAssignment}
    {initialDefined finalDefined : HandleContext}
    {operations : Array OperationPtr} {targetState : InterpreterState finalCtx}
    (hsupported : ∀ decl ∈ decls, decl.Supported)
    (hrun : CreateProg.runDecls decls ctx created =
      some (finalCtx, operations, finalCreated))
    (heval : CreateProg.evalDecls decls semanticCreated = some finalSemanticCreated)
    (hwellformed : CreateProg.checkBindingsDecls decls initialDefined = some finalDefined)
    (hmatchedBounds : (Assignment.MatchValuesInBounds matched) ctx)
    (hcreatedBounds : Assignment.ValuesInBounds created ctx)
    (hmatched : Assignment.MatchRefines matched semanticMatched targetState)
    (hcreated : Assignment.Refines created semanticCreated targetState)
    (hmetadata : (Assignment.MetadataAgrees created) semanticCreated) :
    ∃ afterCreation,
      interpretOpList operations.toList targetState
          (by
            intro operation hmem
            exact CreateProg.runDecls_operationsInBounds hrun operation (by simpa using hmem)) =
        .ok (afterCreation, none) ∧
      afterCreation.memory = targetState.memory ∧
      Assignment.MatchRefines matched semanticMatched afterCreation ∧
      Assignment.Refines finalCreated finalSemanticCreated afterCreation := by
  induction decls generalizing ctx created semanticCreated initialDefined finalCtx operations
      finalCreated finalSemanticCreated targetState with
  | nil =>
    simp [CreateProg.runDecls, CreateProg.evalDecls] at hrun heval
    rcases hrun with ⟨rfl, rfl, rfl⟩
    subst finalSemanticCreated
    exact ⟨targetState, by simp, rfl, hmatched, hcreated⟩
  | cons decl decls ih =>
    cases decl with
    | type value result =>
      rw [CreateProg.runDecls_type_eq_some_iff] at hrun
      obtain ⟨bound, hbind, htailRun⟩ := hrun
      simp only [CreateProg.evalDecls, CreateDecl.eval, Option.bind_eq_bind] at heval
      rw [Option.bind_eq_some_iff] at heval
      obtain ⟨semanticBound, hsemanticBound, htailEval⟩ := heval
      simp only [Option.some.injEq] at hsemanticBound
      subst semanticBound
      simp only [CreateProg.checkBindingsDecls, Option.bind_eq_bind] at hwellformed
      rw [Option.bind_eq_some_iff] at hwellformed
      obtain ⟨nextDefined, _, htailWellformed⟩ := hwellformed
      exact ih (by intro tail hmem; exact hsupported tail (by simp [hmem]))
        htailRun htailEval htailWellformed hmatchedBounds
        (hcreatedBounds.bindType result value hbind) hmatched
        (hcreated.bindType result value hbind)
        (hmetadata.bindType result value hbind)
    | property opCode property result =>
      simp only [CreateProg.runDecls, Option.bind_eq_bind] at hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨bound, hbind, htailRun⟩ := hrun
      simp only [CreateProg.evalDecls, CreateDecl.eval, Option.bind_eq_bind] at heval
      rw [Option.bind_eq_some_iff] at heval
      obtain ⟨semanticBound, hsemanticBound, htailEval⟩ := heval
      simp only [Option.some.injEq] at hsemanticBound
      subst semanticBound
      simp only [CreateProg.checkBindingsDecls, Option.bind_eq_bind] at hwellformed
      rw [Option.bind_eq_some_iff] at hwellformed
      obtain ⟨nextDefined, _, htailWellformed⟩ := hwellformed
      exact ih (by intro tail hmem; exact hsupported tail (by simp [hmem]))
        htailRun htailEval htailWellformed hmatchedBounds
        (hcreatedBounds.bindProperty result property hbind) hmatched
        (hcreated.bindProperty result property hbind)
        (hmetadata.bindProperty result property hbind)
    | @applyNative Inputs Outputs inputBundle outputBundle inputs rewrite outputs =>
      simp only [CreateProg.runDecls, Option.bind_eq_bind] at hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨inputValues, hinput, hrun⟩ := hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨outputValues, hrewrite, hrun⟩ := hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨bound, hbind, htailRun⟩ := hrun
      simp only [CreateProg.evalDecls, CreateDecl.eval, Option.bind_eq_bind] at heval
      have hinputSemantic :
          MetadataTuple.resolve (self := inputBundle) semanticCreated inputs =
            some inputValues := by
        rw [← hmetadata.resolve inputs]
        exact hinput
      rw [hinputSemantic, Option.bind_some, hrewrite] at heval
      rw [Option.bind_eq_some_iff] at heval
      obtain ⟨semanticBound, hsemanticBind, htailEval⟩ := heval
      simp only [CreateProg.checkBindingsDecls, Option.bind_eq_bind] at hwellformed
      rw [Option.bind_eq_some_iff] at hwellformed
      obtain ⟨nextDefined, _, htailWellformed⟩ := hwellformed
      have hboundBounds := MetadataTuple.Shape.bind_valuesInBounds
        (@IsMetadataTuple.shape OpCode inferInstance Outputs outputBundle)
        hcreatedBounds outputs outputValues hbind
      have hboundRefines := MetadataTuple.Shape.bind_refines
        (@IsMetadataTuple.shape OpCode inferInstance Outputs outputBundle)
        hcreated outputs outputValues hbind hsemanticBind
      have hboundMetadata := MetadataTuple.Shape.bind_agrees
        (@IsMetadataTuple.shape OpCode inferInstance Outputs outputBundle)
        hmetadata outputs outputValues hbind hsemanticBind
      exact ih (by intro tail hmem; exact hsupported tail (by simp [hmem]))
        htailRun htailEval htailWellformed hmatchedBounds hboundBounds
        hmatched hboundRefines hboundMetadata
    | operation opCode operands resultTypes property opHandle results =>
      simp only [CreateProg.runDecls, Option.bind_eq_bind] at hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨createdHead, hheadRun, hrun⟩ := hrun
      rcases createdHead with ⟨headCtx, headOps, headCreated⟩
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨createdTail, htailRun, hrun⟩ := hrun
      rcases createdTail with ⟨tailCtx, tailOps, tailCreated⟩
      simp only [pure, Option.some.injEq] at hrun
      rcases hrun with ⟨rfl, rfl, rfl⟩
      simp only [CreateProg.evalDecls, Option.bind_eq_bind] at heval
      rw [Option.bind_eq_some_iff] at heval
      obtain ⟨headSemanticCreated, hheadEval, htailEval⟩ := heval
      simp only [CreateProg.checkBindingsDecls, Option.bind_eq_bind] at hwellformed
      rw [Option.bind_eq_some_iff] at hwellformed
      obtain ⟨nextDefined, hheadWellformed, htailWellformed⟩ := hwellformed
      have htailSupported : ∀ tail ∈ decls, tail.Supported := by
        intro tail hmem
        exact hsupported tail (by simp [hmem])
      have hsuffix : WfIRContext.WithCreatedOps headCtx finalCtx :=
        CreateProg.runDecls_withCreatedOps htailRun
      obtain ⟨afterHead, hinterpretHead, hmemoryHead, hmatchedHead, hcreatedHead,
          hmetadataHead⟩ :=
        CreateDecl.interpret (hsupported _ (by simp)) hheadRun hheadEval hsuffix
          hmatchedBounds hcreatedBounds hmatched hcreated hmetadata
      have hheadCtxChange : WfIRContext.WithCreatedOps ctx headCtx :=
        CreateDecl.run_withCreatedOp hheadRun
      have hmatchedBoundsHead : Assignment.MatchValuesInBounds matched headCtx := by
        intro handle value hget
        exact hheadCtxChange.inBounds_mono (.value value)
          (hmatchedBounds handle value hget)
      have hcreatedBoundsHead : Assignment.ValuesInBounds headCreated headCtx :=
        CreateDecl.run_valuesInBounds hcreatedBounds hheadRun
      obtain ⟨afterTail, hinterpretTail, hmemoryTail, hmatchedTail, hcreatedTail⟩ :=
        ih htailSupported htailRun htailEval htailWellformed hmatchedBoundsHead
          hcreatedBoundsHead hmatchedHead hcreatedHead hmetadataHead
      refine ⟨afterTail, ?_, hmemoryTail.trans hmemoryHead, hmatchedTail, hcreatedTail⟩
      simpa [interpretOpList_append, hinterpretHead] using hinterpretTail

/-- A rule's algebraic validity is the only rule-specific semantic obligation, including for an
ordered creation program whose later declarations consume earlier results. -/
theorem Pattern.Valid.preservesSemantics
    {anyRewrite : Pattern OpCode}
    (h : anyRewrite.Valid)
    (hOps : anyRewrite.compile.ReturnOps)
    (hCtx : anyRewrite.compile.ReturnCtxChanges)
    (hBounds : anyRewrite.compile.ReturnValuesInBounds)
    (hValues : anyRewrite.compile.ReturnValues) :
    anyRewrite.compile.PreservesSemantics hOps hCtx hBounds hValues := by
  simp only [LocalRewritePattern.PreservesSemantics]
  intro ctx ctxRoot ctxDom ctxVerif root rootIn newCtx newOps newValues hpattern state stateWf
    rootState rootCf rootInterp sourceValues hsourceValues targetState targetStateWf
    targetStateDom stateRefinement
  have hcompiled := hpattern
  unfold Pattern.compile at hcompiled
  cases hrun : anyRewrite.matcher.run ctx.raw root with
  | none => simp [hrun] at hcompiled
  | some assignment =>
    cases hcreate : anyRewrite.creation.run assignment ctx with
    | none => simp [hrun, hcreate] at hcompiled
    | some created =>
      rcases created with ⟨createdCtx, createdOps, createdAssignment⟩
      cases hresolve : createdAssignment.getValues anyRewrite.replacement.values with
      | none => simp [hrun, hcreate, hresolve] at hcompiled
      | some resolved =>
        simp [hrun, hcreate, hresolve] at hcompiled
        rcases hcompiled with ⟨rfl, rfl, rfl⟩
        simp [liftM, monadLift, MonadLift.monadLift] at rootInterp
        have hsupported := h.Supported.1
        have hcreateSupported := h.Supported.2
        have hconstrainsRoot := h.ConstrainsRoot
        have hhandles := h.structurallyWellFormed
        have hdenotational := h.refines
        have hcreateSupportedMem :
            ∀ decl ∈ anyRewrite.creation.decls, decl.Supported := by
          intro decl hmem
          exact hcreateSupported decl hmem
        unfold CreateProg.run at hcreate
        let rootHandle := anyRewrite.matcher.rootHandle
        have hmatchedModels := MatchProg.models_of_run hsupported ctxDom ctxVerif rootIn hrun
          stateWf rootInterp hsourceValues
        let semanticMatched :=
          SemanticAssignment.ofConcrete assignment state root sourceValues
        have hrootGet := (MatchProg.run_postconditions hrun).1
        have hrootSupported :=
          MatchProg.supported_root_of_run hsupported hconstrainsRoot hrun
        have hrooted := MatchProg.rooted_of_run ctxDom rootIn hsupported hrun
        have hrootPure :=
          MatchProg.supported_root_pure_of_run hsupported hconstrainsRoot hrun
        have hsemanticRoot := SemanticAssignment.ofConcrete_getOp_root
          (state := state) (rootValues := sourceValues) hrootGet
        change semanticMatched.getOp rootHandle = some sourceValues at hsemanticRoot
        obtain ⟨matchedDefined, createdDefined, finalDefined,
            hmatchedDefined, hcreatedDefined, hreplacementDefined⟩ :=
          hhandles.exists_phase_checks
        have hsemanticEval := hdenotational semanticMatched hmatchedModels
        unfold CreateProg.denote at hsemanticEval
        cases heval : CreateProg.evalDecls anyRewrite.creation.decls semanticMatched with
        | none => simp [heval] at hsemanticEval
        | some semanticCreated =>
          have hsemanticRefinement :
              anyRewrite.replacement.refinesRoot rootHandle semanticMatched semanticCreated := by
            simpa [heval] using hsemanticEval
          rcases stateRefinement with ⟨memoryRefinement, valueRefinement⟩
          have hctxCreated : WfIRContext.WithCreatedOps ctx createdCtx :=
            CreateProg.runDecls_withCreatedOps hcreate
          have hrootInCreated : root.InBounds createdCtx.raw :=
            hctxCreated.inBounds_mono (.operation root) rootIn
          have hmatchedRefines : Assignment.MatchRefines assignment semanticMatched
              targetState := by
            intro handle value sourceRuntime hconcrete hsemantic
            dsimp [semanticMatched] at hsemantic
            obtain ⟨sourceValue, hgetValue, hvalueDom, hnotRootResult, hRuntime⟩ :=
              SemanticAssignment.ofConcrete_getValue_eq_some hsemantic
            rw [hconcrete] at hgetValue
            simp only [Option.some.injEq] at hgetValue
            subst sourceValue
            exact hrooted.exists_target_value ctxDom hconcrete hRuntime hvalueDom
              hnotRootResult rootIn hrootInCreated valueRefinement targetStateDom
          have hcreatedBounds : Assignment.ValuesInBounds assignment ctx := by
            intro handle value hconcrete
            cases hslot : assignment.bindings[handle.id]? with
            | none => simp [Assignment.getValue, Assignment.getBinding, hslot] at hconcrete
            | some binding =>
              cases binding with
              | none => simp [Assignment.getValue, Assignment.getBinding, hslot] at hconcrete
              | some binding =>
                cases binding with
                | op operation =>
                  simp [Assignment.getValue, Assignment.getBinding, hslot] at hconcrete
                | type type =>
                  simp [Assignment.getValue, Assignment.getBinding, hslot] at hconcrete
                | property opCode property =>
                  simp [Assignment.getValue, Assignment.getBinding, hslot] at hconcrete
                | value boundValue =>
                  simp [Assignment.getValue, Assignment.getBinding, hslot] at hconcrete
                  subst boundValue
                  apply hrooted.valuesInBounds handle value
                  simp [Assignment.getValue, Assignment.getBinding, hslot]
          have hcreatedRefines : Assignment.Refines assignment semanticMatched
              targetState := by
            intro handle value sourceRuntime hconcrete hsemantic
            exact hmatchedRefines handle value sourceRuntime hconcrete hsemantic
          have hmetadata : Assignment.MetadataAgrees assignment semanticMatched := by
            exact SemanticAssignment.ofConcrete_metadataAgrees
          obtain ⟨afterCreation, hinterpretCreated, hmemoryCreated,
              hmatchedAfter, hcreatedAfter⟩ :=
            CreateProg.interpret_runDecls hcreateSupportedMem hcreate heval
              (by simpa [CreateProg.checkBindings] using hcreatedDefined)
              hrooted.valuesInBounds hcreatedBounds hmatchedRefines hcreatedRefines hmetadata
          obtain ⟨hRootMemory, hRootCf⟩ :=
            pureOperation_interpret_memory_cf rootIn hrootPure hrootSupported rootInterp
          subst rootCf
          cases hsemanticReplacement :
              semanticCreated.getValues anyRewrite.replacement.values with
          | none =>
            simp [Replacement.refinesRoot, hsemanticRoot,
              hsemanticReplacement] at hsemanticRefinement
          | some sourceReplacements =>
            have hSourceRefinement : sourceValues ⊒ sourceReplacements := by
              simpa [Replacement.refinesRoot, hsemanticRoot,
                hsemanticReplacement] using hsemanticRefinement
            have hreplacementConcrete :
                Assignment.getValues createdAssignment anyRewrite.replacement.values =
                  some resolved := by
              exact hresolve
            obtain ⟨targetReplacements, htargetReplacements,
                hReplacementRefinement⟩ :=
              hcreatedAfter.getValues hreplacementConcrete hsemanticReplacement
            refine ⟨afterCreation, hinterpretCreated,
              (hRootMemory.symm.trans memoryRefinement).trans hmemoryCreated.symm, ?_⟩
            exact ⟨targetReplacements, htargetReplacements,
              RuntimeValue.arrayIsRefinedBy_trans hSourceRefinement hReplacementRefinement⟩

end

end Veir.Puddle
