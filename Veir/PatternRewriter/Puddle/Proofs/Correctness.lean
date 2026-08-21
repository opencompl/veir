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

private def SemanticAssignment.ofConcrete
    {ctx : WfIRContext OpCode}
    (assignment : Assignment OpCode) (state : InterpreterState ctx)
    (root : OperationPtr) (rootValues : Array RuntimeValue) : SemanticAssignment :=
  assignment.bindings.map fun binding =>
    match binding with
    | some (.type type) => some (.type type)
    | some (.property opCode value) => some (.property opCode value)
    | some (.value value) =>
      match state.variables.getVar? value with
      | some runtimeValue => some (.value runtimeValue)
      | none => none
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
      Assignment.matchMetadataStore metadataAtom before handle = some value) :
    metadataAtom.resolve (SemanticAssignment.ofConcrete final state root rootValues) handle =
      some value := by
  cases metadataAtom with
  | type =>
    have hget : Assignment.getType before handle = some value := by
      dsimp [MetadataTuple.Atom.resolve, Assignment.matchMetadataStore] at hresolve
      exact hresolve
    simpa [MetadataTuple.Atom.resolve] using
      SemanticAssignment.ofConcrete_getType (hext.getType hget)
  | property opCode =>
    have hget : Assignment.getProperty before handle = some value := by
      dsimp [MetadataTuple.Atom.resolve, Assignment.matchMetadataStore] at hresolve
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
      Assignment.matchMetadataStore shape before handles = some values) :
    shape.resolve (SemanticAssignment.ofConcrete final state root rootValues) handles =
      some values := by
  induction shape with
  | unit => rfl
  | atom metadataAtom =>
    exact metadataAtom.resolve_ofConcrete_of_extends hext handles values hresolve
  | cons head tail tailIH =>
    rcases handles with ⟨headHandle, tailHandles⟩
    cases hhead : @MetadataTuple.Atom.resolve OpCode _ _ (Assignment OpCode)
        Assignment.matchMetadataStore head before headHandle with
    | none => simp [MetadataTuple.Shape.resolve, hhead] at hresolve
    | some headValue =>
      cases htail : @MetadataTuple.Shape.resolve OpCode _ _ (Assignment OpCode)
          Assignment.matchMetadataStore tail before tailHandles with
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
      Assignment.matchMetadataStore before handles = some values) :
    MetadataTuple.resolve (SemanticAssignment.ofConcrete final state root rootValues) handles =
      some values := by
  exact bundle.shape.resolve_ofConcrete_of_extends hext handles values hresolve

private theorem SemanticAssignment.ofConcrete_getValue
    (hget : Assignment.getValue assignment handle = some value)
    (hvalue : state.variables.getVar? value = some runtimeValue) :
    (SemanticAssignment.ofConcrete assignment state root rootValues).getValue handle =
      some runtimeValue := by
  have hbinding : assignment.bindings[handle.id]? = some (some (.value value)) := by
    apply (Assignment.getBinding_eq_some_iff _ _ _).mp
    unfold Assignment.getValue at hget
    split at hget <;> simp_all
  simp [SemanticAssignment.ofConcrete, SemanticAssignment.getValue, hbinding, hvalue]

private theorem SemanticAssignment.ofConcrete_getValue_eq_some
    (hget : (SemanticAssignment.ofConcrete assignment state root rootValues).getValue handle =
      some runtimeValue) :
    ∃ value, Assignment.getValue assignment handle = some value ∧
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
        cases hRuntime : state.variables.getVar? value with
        | none => simp [hRuntime] at hslot
        | some runtime =>
          simp [hRuntime] at hslot
          subst runtime
          refine ⟨value, ?_, hRuntime⟩
          simp [Assignment.getValue, Assignment.getBinding, hbinding]
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
    {patterns : List (Handle OpCode .value)} {values : List ValuePtr}
    {runtimeValues : List RuntimeValue}
    (hbind : Assignment.matchBindValues before patterns values = some after)
    (hext : Assignment.Extends after final)
    (hvalues : values.mapM state.variables.getVar? = some runtimeValues) :
    patterns.mapM (SemanticAssignment.ofConcrete final state root rootValues).getValue =
      some runtimeValues := by
  induction patterns generalizing before after values runtimeValues with
  | nil =>
    cases values <;> simp [Assignment.matchBindValues] at hbind hvalues
    subst after
    simpa using hvalues
  | cons pattern patterns ih =>
    cases values with
    | nil => simp [Assignment.matchBindValues] at hbind
    | cons value values =>
      change (Assignment.matchBindValue before pattern value).bind
        (fun assignment => Assignment.matchBindValues assignment patterns values) = some after at hbind
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
              (Assignment.matchBindValue_get hvalue))
          have hsemanticValue := SemanticAssignment.ofConcrete_getValue
            (root := root) (rootValues := rootValues) hfinalValue hRuntimeValue
          have hsemanticValues := ih hrest hext hRuntimeValues
          simp [hsemanticValue, hsemanticValues]

private theorem Assignment.matchBindType_get
    {assignment after : Assignment OpCode} {handle : Handle OpCode .type} {type : TypeAttr}
    (hbind : Assignment.matchBindType assignment handle type = some after) :
    Assignment.getType after handle = some type := by
  have h := Assignment.matchBind_get hbind
  simp [Assignment.getType, Assignment.getBinding, h]

private theorem SemanticAssignment.ofConcrete_getTypes_of_bindTypes
    {ctx : WfIRContext OpCode} {state : InterpreterState ctx}
    {root : OperationPtr} {rootValues : Array RuntimeValue}
    {before after final : Assignment OpCode}
    {patterns : List (Handle OpCode .type)} {types : List TypeAttr}
    (hbind : Assignment.matchBindTypes before patterns types = some after)
    (hext : Assignment.Extends after final) :
    patterns.mapM (SemanticAssignment.ofConcrete final state root rootValues).getType =
      some types := by
  induction patterns generalizing before after types with
  | nil =>
    cases types <;> simp [Assignment.matchBindTypes] at hbind
    subst after
    simp
  | cons pattern patterns ih =>
    cases types with
    | nil => simp [Assignment.matchBindTypes] at hbind
    | cons type types =>
      change (Assignment.matchBindType before pattern type).bind
        (fun assignment => Assignment.matchBindTypes assignment patterns types) = some after at hbind
      rw [Option.bind_eq_some_iff] at hbind
      obtain ⟨typeAssignment, htype, hrest⟩ := hbind
      have hfinalType := hext.getType
        ((Assignment.Extends.bindTypes hrest).getType
          (Assignment.matchBindType_get htype))
      have hsemanticType := SemanticAssignment.ofConcrete_getType
        (state := state) (root := root) (rootValues := rootValues) hfinalType
      have hsemanticTypes := ih hrest hext
      simp [hsemanticType, hsemanticTypes]

private theorem MatchDecl.operation_result_models
    {ctx : WfIRContext OpCode} (ctxDom : ctx.Dom)
    {root operation : OperationPtr} {state : InterpreterState ctx}
    {rootValues : Array RuntimeValue} {final base : Assignment OpCode}
    {returnTypes : Array (Handle OpCode .type)} {resultHandles : Array (Handle OpCode .value)}
    {runtimeResult : RuntimeValue}
    (hreturnTypes : returnTypes.size = 1)
    (hresultHandles : resultHandles.size = returnTypes.size ∨ resultHandles = #[])
    (hcheck : Assignment.matchCheckOperationResult base operation resultHandles = some ())
    (hext : Assignment.Extends base final) (hrooted : Assignment.Rooted final ctx root)
    (hlookup : operation ≠ root →
      state.variables.getVar? (.opResult (operation.getResult 0)) = some runtimeResult) :
    MatchDecl.ResultsModel
      (SemanticAssignment.ofConcrete final state root rootValues)
      resultHandles #[runtimeResult] := by
  rcases hresultHandles with hsize | hnone
  · have hsize' : resultHandles.size = 1 := hsize.trans hreturnTypes
    rcases resultHandles with ⟨resultHandles⟩
    simp only [List.size_toArray] at hsize'
    match resultHandles, hsize' with
    | [resultHandle], _ =>
      have hvalue := Assignment.matchCheckOperationResult_getValue
        (resultHandle := resultHandle) (by simp) hcheck
      have hfinalValue := hext.getValue hvalue
      by_cases hop : operation = root
      · subst operation
        obtain ⟨consumer, _, hconsumer, _, hmem⟩ :=
          hrooted.2 resultHandle (.opResult (root.getResult 0)) hfinalValue
        have hrootIn : root.InBounds ctx.raw := by grind
        have hdef : (ValuePtr.opResult (root.getResult 0)).definingOp? = some root := by
          simp
        have hrootDomConsumer : root.ProperlyDominates consumer ctx true :=
          OperationPtr.properlyDominates_of_definingOp?_of_mem_getOperands!
            ctxDom hdef hmem
        rcases hconsumer with rfl | hconsumer
        · exact ((OperationPtr.properlyDominates_def.mp hrootDomConsumer).2 rfl).elim
        · have hcycle := OperationPtr.properlyDominates_trans hrootDomConsumer hconsumer
          exact ((OperationPtr.properlyDominates_def.mp hcycle).2 rfl).elim
      · have hsemanticValue := SemanticAssignment.ofConcrete_getValue
          (root := root) (rootValues := rootValues) hfinalValue (hlookup hop)
        right
        simp [SemanticAssignment.getValues, hsemanticValue]
  · subst resultHandles
    simp [MatchDecl.ResultsModel]


private theorem MatchProg.models_of_run
    {prog : MatchProg OpCode α} (hsupported : prog.Supported)
    {ctx : WfIRContext OpCode} (ctxDom : ctx.Dom) (ctxVerif : ctx.Verified)
    {root : OperationPtr} (rootIn : root.InBounds ctx.raw)
    {assignment : Assignment OpCode}
    (hrun : prog.run ctx.raw root = some assignment)
    {state rootState : InterpreterState ctx} {rootCf}
    (stateWf : state.EquationLemmaAt (InsertPoint.before root) (by grind))
    (rootInterp : interpretOp root state rootIn = .ok (rootState, rootCf))
    {sourceValues : Array RuntimeValue}
    (hsourceValues : (root.getResults ctx.raw).mapM rootState.variables.getVar? =
      some sourceValues) :
    prog.Models (SemanticAssignment.ofConcrete assignment state root sourceValues) := by
  intro decl hmem
  have hoccurs := (MatchProg.matchDecls_postconditions hrun).2 decl hmem
  cases decl with
  | root opCode operands returnTypes property propertyHandle handle =>
    have hrootGet := hoccurs.root_getOp
    have hsemanticRoot := SemanticAssignment.ofConcrete_getOp_root
      (state := state) (rootValues := sourceValues) hrootGet
    simp [MatchDecl.Models, hsemanticRoot]
  | type matcher handle =>
    simp [MatchDecl.Models]
  | guard inputs predicate =>
    obtain ⟨before, after, hmatch, hext⟩ := hoccurs
    simp only [MatchDecl.match, Option.bind_eq_bind] at hmatch
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
    simp [MatchDecl.match] at hmatch
    simp only [Option.bind_eq_some_iff] at hmatch
    obtain ⟨value, hget, htype⟩ := hmatch
    have hfinalGet := hext.getValue
      ((Assignment.Extends.bindType htype).getValue hget)
    have hrooted := MatchProg.rooted_of_run ctxDom rootIn hsupported.1 hrun
    obtain ⟨runtimeValue, hRuntimeValue⟩ :=
      hrooted.exists_getValue rootIn stateWf rootInterp hfinalGet
    have hsemanticValue := SemanticAssignment.ofConcrete_getValue
      (root := root) (rootValues := sourceValues) hfinalGet hRuntimeValue
    exact ⟨runtimeValue, hsemanticValue⟩
  | operation opCode operands returnTypes property propertyHandle handle results =>
    obtain ⟨before, after, hmatchOriginal, hext⟩ := hoccurs
    have hbeforeExtendsFinal :=
      (Assignment.Extends.matchDecl hmatchOriginal).trans hext
    have hmatch := hmatchOriginal
    simp [MatchDecl.match] at hmatch
    simp only [Option.bind_eq_some_iff] at hmatch
    obtain ⟨found, hget, _, hcheck, _, hopcode, _, hproperty,
      propertyAssignment, hbindProperty, _, hresultSize,
      typedAssignment, htypes, _, hoperandSize, hvalues⟩ := hmatch
    rcases found with ⟨operation, baseAssignment⟩
    have hbaseExtendsFinal :=
      ((Assignment.Extends.bindProperty hbindProperty).trans
        ((Assignment.Extends.bindTypes htypes).trans
          (Assignment.Extends.bindValues hvalues))).trans hext
    have hfinalOp := hbaseExtendsFinal.getOp
      (Assignment.matchGetOrBindOp_getOp hget)
    have hopcodeEq : operation.getOpType! ctx.raw = opCode := by
      simpa [_root_.guard] using hopcode
    have hpropertyMatch : property
        (operation.getProperties! ctx.raw opCode) = true := by
      simpa [_root_.guard] using hproperty
    have hpropertyExtendsFinal :=
      ((Assignment.Extends.bindTypes htypes).trans
        (Assignment.Extends.bindValues hvalues)).trans hext
    have hfinalProperty := hpropertyExtendsFinal.getProperty
      (Assignment.matchBindProperty_get hbindProperty)
    have hsemanticProperty := SemanticAssignment.ofConcrete_getProperty
      (state := state) (root := root) (rootValues := sourceValues) hfinalProperty
    have hrooted := MatchProg.rooted_of_run ctxDom rootIn hsupported.1 hrun
    have hopRooted := hrooted.1 handle operation hfinalOp
    have hdeclSupported :=
      hsupported.1
        (.operation opCode operands returnTypes property propertyHandle handle results) hmem
    change property.Supported operands.size returnTypes.size ∧ _
      at hdeclSupported
    have hopPure : operation.Pure ctx.raw :=
      hdeclSupported.1.pure hopcodeEq hpropertyMatch
    rcases hdeclSupported.1 with ⟨hresultPatternSize, _heffects⟩
    subst opCode
    focus
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
      have hsemanticOperandsList :=
        SemanticAssignment.ofConcrete_getValues_of_bindValues
          (root := root) (rootValues := sourceValues) hvalues hext hoperandValueList
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
          (SemanticAssignment.ofConcrete assignment state root sourceValues).getTypes returnTypes =
            some (operation.getResultTypes! ctx.raw) := by
        unfold SemanticAssignment.getTypes
        rw [Array.mapM_eq_mapM_toList, hsemanticResultTypesList]
        simp
      have hopVerified : operation.Verified ctx hopIn := by grind
      have hresultTypesSize :
          (operation.getResultTypes! ctx.raw).size = returnTypes.size := by
        simpa [_root_.guard] using hresultSize
      have hresultValuesSize : resultValues.size = 1 := by
        have hsetSize := VariableState.setResultValues?.getNumRseults!_eq_size hset
        grind
      obtain ⟨runtimeResult, hresultValues⟩ : ∃ runtimeResult, resultValues = #[runtimeResult] := by
        rcases resultValues with ⟨resultValues⟩
        simp only [List.size_toArray] at hresultValuesSize
        match resultValues, hresultValuesSize with
        | [runtimeResult], _ => exact ⟨runtimeResult, rfl⟩
      subst resultValues
      have hresults : operation.getResults! ctx.raw =
          #[ValuePtr.opResult (operation.getResult 0)] := by grind
      have hoperationEq_of_ne : operation ≠ root → operationState = state := by
        intro hopEq
        have hdominates := hopRooted.2.resolve_left hopEq
        have hdomIp : operation.dominatesIp (InsertPoint.before root) ctx := by grind
        obtain ⟨equationCf, hequation⟩ := stateWf operation hopIn hopPure hdomIp
        rw [hoperationInterp] at hequation
        grind
      have hsemanticResult :
          (SemanticAssignment.ofConcrete assignment state root sourceValues).getOp handle =
            some #[runtimeResult] := by
        by_cases hopEq : operation = root
        · subst operation
          have hresultLookup := VariableState.getVar?_getResult_of_setResultValues?
            (varState := state.variables) (varState' := variables)
            (op := root) (resultValues := #[runtimeResult]) (i := 0) (by grind) hset
          have hsource : sourceValues = #[runtimeResult] := by
            have hstateEq : operationState = rootState := by
              rw [rootInterp] at hoperationInterp
              grind
            rw [← hstateEq, hoperationState] at hsourceValues
            have hrootResults : root.getResults ctx.raw (by grind) =
                #[ValuePtr.opResult (root.getResult 0)] := by grind
            rw [hrootResults] at hsourceValues
            symm
            simpa [Array.mapM_eq_mapM_toList, hresultLookup] using hsourceValues
          subst sourceValues
          exact SemanticAssignment.ofConcrete_getOp_root
            (state := state) (rootValues := #[runtimeResult]) hfinalOp
        · apply SemanticAssignment.ofConcrete_getOp_other
            (rootValues := sourceValues) (runtimeValues := #[runtimeResult]) hfinalOp hopEq
          have hresultLookup := VariableState.getVar?_getResult_of_setResultValues?
            (varState := state.variables) (varState' := variables)
            (op := operation) (resultValues := #[runtimeResult]) (i := 0) (by grind) hset
          have hoperationEq := hoperationEq_of_ne hopEq
          have hvariables : state.variables = variables := by
            exact congrArg InterpreterState.variables (hoperationEq.symm.trans hoperationState)
          rw [hresults]
          simp [Array.mapM_eq_mapM_toList, hvariables, hresultLookup]
      have hresultModels := MatchDecl.operation_result_models
        (rootValues := sourceValues) ctxDom hresultPatternSize hdeclSupported.2
        (by simpa using hcheck) hbaseExtendsFinal hrooted (by
          intro hopEq
          have hresultLookup := VariableState.getVar?_getResult_of_setResultValues?
            (varState := state.variables) (varState' := variables)
            (op := operation) (resultValues := #[runtimeResult]) (i := 0) (by grind) hset
          have hoperationEq := hoperationEq_of_ne hopEq
          have hvariables : state.variables = variables := by
            exact congrArg InterpreterState.variables (hoperationEq.symm.trans hoperationState)
          rw [hvariables]
          simpa using hresultLookup)
      have hmemory : state.memory = memory :=
        OperationPtr.Pure.interpretOp'_eq_ok_implies_memory_eq hopPure (by
          simpa [OperationPtr.interpret] using hinterpret)
      simp only [MatchDecl.Models]
      refine ⟨operandValues, operation.getResultTypes! ctx.raw, #[runtimeResult],
        operation.getProperties! ctx.raw (operation.getOpType! ctx.raw),
        hsemanticOperands, hsemanticResultTypes, hsemanticResult, hsemanticProperty,
        hresultModels, ?_⟩
      simp [PropertyMatcher.Models, hpropertyMatch, PropertyMatcher.Interprets]
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
    (hrooted : Assignment.Rooted assignment ctx root) (ctxDom : ctx.Dom)
    {handle : Handle OpCode .value} {value : ValuePtr}
    (hget : Assignment.getValue assignment handle = some value)
    {state : InterpreterState ctx} {runtimeValue : RuntimeValue}
    (hRuntime : state.variables.getVar? value = some runtimeValue)
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
  obtain ⟨consumer, consumerIn, hconsumer, _, hoperand⟩ := hrooted.2 handle value hget
  have hvalueIn : value.InBounds ctx.raw := by grind
  have hvalueDom : value.dominatesIp (InsertPoint.before root) ctx := by
    rcases hconsumer with rfl | hconsumer
    · grind [WfIRContext.Dom.operand_dominates_op]
    · have hdomConsumer : value.dominatesIp (InsertPoint.before consumer) ctx := by
        grind [WfIRContext.Dom.operand_dominates_op]
      exact ValuePtr.dominatesIp_before_of_properlyDominates hdomConsumer hconsumer
  have hnotResult : value ∉ root.getResults! ctx.raw := by
    have hconsumerDom : consumer.Dominates root ctx := by
      rcases hconsumer with rfl | hstrict
      · exact OperationPtr.dominates_refl
      · exact OperationPtr.dominates_of_properlyDominates hstrict
    exact IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates
      ctxDom hconsumerDom value hoperand
  have hcreated := hreturn₃ ctx root newCtx newOps newValues hpattern
  have hvalueDomNew : value.dominatesIp (InsertPoint.before root) newCtx :=
    hcreated.value_dominatesIp_mono hvalueDom
  exact LocalRewritePattern.exists_refined_getVar?
    (ipIn := by grind) (ipIn' := by grind) valueRefinement targetStateDom
    hvalueIn hRuntime hvalueDom hvalueDomNew hnotResult

/-- Every semantically-created value has a refining concrete value in the target state. -/
private def Assignment.Refines
    {ctx : WfIRContext OpCode}
    (concrete : Assignment OpCode) (semantic : SemanticCreateAssignment)
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

private theorem Assignment.getType_bindType_eq
    (assignment : Assignment OpCode) (bound query : Handle OpCode .type) (value : TypeAttr)
    (heq : query.id = bound.id) :
    Assignment.getType (Assignment.bindType assignment bound value) query = some value := by
  rcases bound with ⟨bound⟩; rcases query with ⟨query⟩
  simp only at heq; subst query
  simp only [Assignment.bindType]
  unfold Assignment.bind
  split
  · rename_i h; unfold Assignment.getType Assignment.getBinding; rw [Array.getElem?_set]; simp
  · rename_i h; unfold Assignment.getType Assignment.getBinding
    rw [Array.getElem?_append_replicate_singleton_self _ _ _ _ h]; simp

private theorem Assignment.getType_bindType_ne
    (assignment : Assignment OpCode) (bound query : Handle OpCode .type) (value : TypeAttr)
    (hne : query.id ≠ bound.id) :
    Assignment.getType (Assignment.bindType assignment bound value) query = Assignment.getType assignment query := by
  rcases bound with ⟨bound⟩; rcases query with ⟨query⟩
  simp only at hne
  simp only [Assignment.bindType]
  unfold Assignment.bind
  split
  · rename_i h; unfold Assignment.getType Assignment.getBinding
    rw [Array.getElem?_set_ne h (Ne.symm hne)]
  · rename_i h; unfold Assignment.getType Assignment.getBinding
    rw [Array.getElem?_append_replicate_singleton_ne _ _ _ _ h hne]

private theorem Assignment.getProperty_bindType_eq
    (assignment : Assignment OpCode) (bound : Handle OpCode .type)
    (query : Handle OpCode (.prop opCode)) (value : TypeAttr) (heq : query.id = bound.id) :
    Assignment.getProperty (Assignment.bindType assignment bound value) query = none := by
  rcases bound with ⟨bound⟩; rcases query with ⟨query⟩
  simp only at heq; subst query
  simp only [Assignment.bindType]
  unfold Assignment.bind
  split
  · rename_i h; unfold Assignment.getProperty Assignment.getBinding; rw [Array.getElem?_set]; simp
  · rename_i h; unfold Assignment.getProperty Assignment.getBinding
    rw [Array.getElem?_append_replicate_singleton_self _ _ _ _ h]; simp

private theorem Assignment.getProperty_bindType_ne
    (assignment : Assignment OpCode) (bound : Handle OpCode .type)
    (query : Handle OpCode (.prop opCode)) (value : TypeAttr) (hne : query.id ≠ bound.id) :
    Assignment.getProperty (Assignment.bindType assignment bound value) query = Assignment.getProperty assignment query := by
  rcases bound with ⟨bound⟩; rcases query with ⟨query⟩
  simp only at hne
  simp only [Assignment.bindType]
  unfold Assignment.bind
  split
  · rename_i h; unfold Assignment.getProperty Assignment.getBinding
    rw [Array.getElem?_set_ne h (Ne.symm hne)]
  · rename_i h; unfold Assignment.getProperty Assignment.getBinding
    rw [Array.getElem?_append_replicate_singleton_ne _ _ _ _ h hne]

private theorem Assignment.getType_bindProperty_eq
    (assignment : Assignment OpCode) (bound : Handle OpCode (.prop opCode))
    (query : Handle OpCode .type) (value : propertiesOf opCode) (heq : query.id = bound.id) :
    Assignment.getType (Assignment.bindProperty assignment bound value) query = none := by
  rcases bound with ⟨bound⟩; rcases query with ⟨query⟩
  simp only at heq; subst query
  simp only [Assignment.bindProperty]
  unfold Assignment.bind
  split
  · rename_i h; unfold Assignment.getType Assignment.getBinding; rw [Array.getElem?_set]; simp
  · rename_i h; unfold Assignment.getType Assignment.getBinding
    rw [Array.getElem?_append_replicate_singleton_self _ _ _ _ h]; simp

private theorem Assignment.getType_bindProperty_ne
    (assignment : Assignment OpCode) (bound : Handle OpCode (.prop opCode))
    (query : Handle OpCode .type) (value : propertiesOf opCode) (hne : query.id ≠ bound.id) :
    Assignment.getType (Assignment.bindProperty assignment bound value) query = Assignment.getType assignment query := by
  rcases bound with ⟨bound⟩; rcases query with ⟨query⟩
  simp only at hne
  simp only [Assignment.bindProperty]
  unfold Assignment.bind
  split
  · rename_i h; unfold Assignment.getType Assignment.getBinding
    rw [Array.getElem?_set_ne h (Ne.symm hne)]
  · rename_i h; unfold Assignment.getType Assignment.getBinding
    rw [Array.getElem?_append_replicate_singleton_ne _ _ _ _ h hne]

private theorem Assignment.getProperty_bindProperty_ne
    (assignment : Assignment OpCode) (bound : Handle OpCode (.prop opCode))
    (query : Handle OpCode (.prop queryOpCode)) (value : propertiesOf opCode)
    (hne : query.id ≠ bound.id) :
    Assignment.getProperty (Assignment.bindProperty assignment bound value) query = Assignment.getProperty assignment query := by
  rcases bound with ⟨bound⟩; rcases query with ⟨query⟩
  simp only at hne
  simp only [Assignment.bindProperty]
  unfold Assignment.bind
  split
  · rename_i h; unfold Assignment.getProperty Assignment.getBinding
    rw [Array.getElem?_set_ne h (Ne.symm hne)]
  · rename_i h; unfold Assignment.getProperty Assignment.getBinding
    rw [Array.getElem?_append_replicate_singleton_ne _ _ _ _ h hne]

private theorem Assignment.getProperty_bindProperty_eq
    (assignment : Assignment OpCode) (bound : Handle OpCode (.prop opCode))
    (query : Handle OpCode (.prop queryOpCode)) (value : propertiesOf opCode)
    (heq : query.id = bound.id) :
    Assignment.getProperty (Assignment.bindProperty assignment bound value) query =
      if h : opCode = queryOpCode then some (h ▸ value) else none := by
  rcases bound with ⟨bound⟩; rcases query with ⟨query⟩
  simp only at heq; subst query
  simp only [Assignment.bindProperty]
  unfold Assignment.bind
  split
  · rename_i h
    unfold Assignment.getProperty Assignment.getBinding
    rw [Array.getElem?_set]
    by_cases hop : opCode = queryOpCode <;> simp [hop]
  · rename_i h
    unfold Assignment.getProperty Assignment.getBinding
    rw [Array.getElem?_append_replicate_singleton_self _ _ _ _ h]
    by_cases hop : opCode = queryOpCode <;> simp [hop]

private theorem SemanticCreateAssignment.getType_bindType_eq
    (assignment : SemanticCreateAssignment) (bound query : Handle OpCode .type) (value : TypeAttr)
    (heq : query.id = bound.id) :
    (assignment.bindType bound value).getType query = some value := by
  rcases bound with ⟨bound⟩; rcases query with ⟨query⟩
  simp only at heq; subst query
  simp only [SemanticCreateAssignment.bindType]
  unfold SemanticCreateAssignment.bind
  split
  · rename_i h; unfold SemanticCreateAssignment.getType SemanticAssignment.getType
    rw [Array.getElem?_set]; simp
  · rename_i h
    have hs : assignment.size ≤ bound := Nat.le_of_not_gt h
    unfold SemanticCreateAssignment.getType SemanticAssignment.getType
    simp only [Array.getElem?_append]; simp [hs]

private theorem SemanticCreateAssignment.getType_bindType_ne
    (assignment : SemanticCreateAssignment) (bound query : Handle OpCode .type) (value : TypeAttr)
    (hne : query.id ≠ bound.id) :
    (assignment.bindType bound value).getType query = assignment.getType query := by
  rcases bound with ⟨bound⟩; rcases query with ⟨query⟩
  simp only at hne
  simp only [SemanticCreateAssignment.bindType]
  unfold SemanticCreateAssignment.bind
  split
  · rename_i h; unfold SemanticCreateAssignment.getType SemanticAssignment.getType
    rw [Array.getElem?_set_ne h (Ne.symm hne)]
  · rename_i h
    have hs : assignment.size ≤ bound := Nat.le_of_not_gt h
    have hsize : assignment.size + (bound - assignment.size) = bound := Nat.add_sub_of_le hs
    unfold SemanticCreateAssignment.getType SemanticAssignment.getType
    simp only [Array.size_append, Array.size_replicate, Array.getElem?_append,
      Array.getElem?_replicate]; rw [hsize]
    by_cases hquery : query < assignment.size
    · have hqb : query < bound := Nat.lt_of_lt_of_le hquery hs; simp [hquery, hqb]
    · have hqs : assignment.size ≤ query := Nat.le_of_not_gt hquery
      by_cases hqb : query < bound
      · have hgap : query - assignment.size < bound - assignment.size :=
          Nat.sub_lt_sub_right hqs hqb
        simp [hquery, hqb, hgap]
      · have hbq : bound < query := by omega
        have hdiff : query - bound ≠ 0 := by omega
        simp [hquery, hqb, hdiff]

private theorem SemanticCreateAssignment.getProperty_bindType_eq
    (assignment : SemanticCreateAssignment) (bound : Handle OpCode .type)
    (query : Handle OpCode (.prop opCode)) (value : TypeAttr) (heq : query.id = bound.id) :
    (assignment.bindType bound value).getProperty query = none := by
  rcases bound with ⟨bound⟩; rcases query with ⟨query⟩
  simp only at heq; subst query
  simp only [SemanticCreateAssignment.bindType]
  unfold SemanticCreateAssignment.bind
  split
  · rename_i h; unfold SemanticCreateAssignment.getProperty SemanticAssignment.getProperty
    rw [Array.getElem?_set]; simp
  · rename_i h
    have hs : assignment.size ≤ bound := Nat.le_of_not_gt h
    unfold SemanticCreateAssignment.getProperty SemanticAssignment.getProperty
    simp only [Array.getElem?_append]; simp [hs]

private theorem SemanticCreateAssignment.getProperty_bindType_ne
    (assignment : SemanticCreateAssignment) (bound : Handle OpCode .type)
    (query : Handle OpCode (.prop opCode)) (value : TypeAttr) (hne : query.id ≠ bound.id) :
    (assignment.bindType bound value).getProperty query = assignment.getProperty query := by
  rcases bound with ⟨bound⟩; rcases query with ⟨query⟩
  simp only at hne
  simp only [SemanticCreateAssignment.bindType]
  unfold SemanticCreateAssignment.bind
  split
  · rename_i h; unfold SemanticCreateAssignment.getProperty SemanticAssignment.getProperty
    rw [Array.getElem?_set_ne h (Ne.symm hne)]
  · rename_i h
    have hs : assignment.size ≤ bound := Nat.le_of_not_gt h
    have hsize : assignment.size + (bound - assignment.size) = bound := Nat.add_sub_of_le hs
    unfold SemanticCreateAssignment.getProperty SemanticAssignment.getProperty
    simp only [Array.size_append, Array.size_replicate, Array.getElem?_append,
      Array.getElem?_replicate]; rw [hsize]
    by_cases hquery : query < assignment.size
    · have hqb : query < bound := Nat.lt_of_lt_of_le hquery hs; simp [hquery, hqb]
    · have hqs : assignment.size ≤ query := Nat.le_of_not_gt hquery
      by_cases hqb : query < bound
      · have hgap : query - assignment.size < bound - assignment.size :=
          Nat.sub_lt_sub_right hqs hqb
        simp [hquery, hqb, hgap]
      · have hbq : bound < query := by omega
        have hdiff : query - bound ≠ 0 := by omega
        simp [hquery, hqb, hdiff]

private theorem SemanticCreateAssignment.getType_bindProperty_eq
    (assignment : SemanticCreateAssignment) (bound : Handle OpCode (.prop opCode))
    (query : Handle OpCode .type) (value : propertiesOf opCode) (heq : query.id = bound.id) :
    (assignment.bindProperty bound value).getType query = none := by
  rcases bound with ⟨bound⟩; rcases query with ⟨query⟩
  simp only at heq; subst query
  simp only [SemanticCreateAssignment.bindProperty]
  unfold SemanticCreateAssignment.bind
  split
  · rename_i h; unfold SemanticCreateAssignment.getType SemanticAssignment.getType
    rw [Array.getElem?_set]; simp
  · rename_i h
    have hs : assignment.size ≤ bound := Nat.le_of_not_gt h
    unfold SemanticCreateAssignment.getType SemanticAssignment.getType
    simp only [Array.getElem?_append]; simp [hs]

private theorem SemanticCreateAssignment.getType_bindProperty_ne
    (assignment : SemanticCreateAssignment) (bound : Handle OpCode (.prop opCode))
    (query : Handle OpCode .type) (value : propertiesOf opCode) (hne : query.id ≠ bound.id) :
    (assignment.bindProperty bound value).getType query = assignment.getType query := by
  rcases bound with ⟨bound⟩; rcases query with ⟨query⟩
  simp only at hne
  simp only [SemanticCreateAssignment.bindProperty]
  unfold SemanticCreateAssignment.bind
  split
  · rename_i h; unfold SemanticCreateAssignment.getType SemanticAssignment.getType
    rw [Array.getElem?_set_ne h (Ne.symm hne)]
  · rename_i h
    have hs : assignment.size ≤ bound := Nat.le_of_not_gt h
    have hsize : assignment.size + (bound - assignment.size) = bound := Nat.add_sub_of_le hs
    unfold SemanticCreateAssignment.getType SemanticAssignment.getType
    simp only [Array.size_append, Array.size_replicate, Array.getElem?_append,
      Array.getElem?_replicate]; rw [hsize]
    by_cases hquery : query < assignment.size
    · have hqb : query < bound := Nat.lt_of_lt_of_le hquery hs; simp [hquery, hqb]
    · have hqs : assignment.size ≤ query := Nat.le_of_not_gt hquery
      by_cases hqb : query < bound
      · have hgap : query - assignment.size < bound - assignment.size :=
          Nat.sub_lt_sub_right hqs hqb
        simp [hquery, hqb, hgap]
      · have hbq : bound < query := by omega
        have hdiff : query - bound ≠ 0 := by omega
        simp [hquery, hqb, hdiff]

private theorem SemanticCreateAssignment.getProperty_bindProperty_ne
    (assignment : SemanticCreateAssignment) (bound : Handle OpCode (.prop opCode))
    (query : Handle OpCode (.prop queryOpCode)) (value : propertiesOf opCode)
    (hne : query.id ≠ bound.id) :
    (assignment.bindProperty bound value).getProperty query = assignment.getProperty query := by
  rcases bound with ⟨bound⟩; rcases query with ⟨query⟩
  simp only at hne
  simp only [SemanticCreateAssignment.bindProperty]
  unfold SemanticCreateAssignment.bind
  split
  · rename_i h; unfold SemanticCreateAssignment.getProperty SemanticAssignment.getProperty
    rw [Array.getElem?_set_ne h (Ne.symm hne)]
  · rename_i h
    have hs : assignment.size ≤ bound := Nat.le_of_not_gt h
    have hsize : assignment.size + (bound - assignment.size) = bound := Nat.add_sub_of_le hs
    unfold SemanticCreateAssignment.getProperty SemanticAssignment.getProperty
    simp only [Array.size_append, Array.size_replicate, Array.getElem?_append,
      Array.getElem?_replicate]; rw [hsize]
    by_cases hquery : query < assignment.size
    · have hqb : query < bound := Nat.lt_of_lt_of_le hquery hs; simp [hquery, hqb]
    · have hqs : assignment.size ≤ query := Nat.le_of_not_gt hquery
      by_cases hqb : query < bound
      · have hgap : query - assignment.size < bound - assignment.size :=
          Nat.sub_lt_sub_right hqs hqb
        simp [hquery, hqb, hgap]
      · have hbq : bound < query := by omega
        have hdiff : query - bound ≠ 0 := by omega
        simp [hquery, hqb, hdiff]

private theorem SemanticCreateAssignment.getProperty_bindProperty_eq
    (assignment : SemanticCreateAssignment) (bound : Handle OpCode (.prop opCode))
    (query : Handle OpCode (.prop queryOpCode)) (value : propertiesOf opCode)
    (heq : query.id = bound.id) :
    (assignment.bindProperty bound value).getProperty query =
      if h : opCode = queryOpCode then some (h ▸ value) else none := by
  rcases bound with ⟨bound⟩; rcases query with ⟨query⟩
  simp only at heq; subst query
  simp only [SemanticCreateAssignment.bindProperty]
  unfold SemanticCreateAssignment.bind
  split
  · rename_i h; unfold SemanticCreateAssignment.getProperty SemanticAssignment.getProperty
    rw [Array.getElem?_set]; simp
  · rename_i h
    have hs : assignment.size ≤ bound := Nat.le_of_not_gt h
    unfold SemanticCreateAssignment.getProperty SemanticAssignment.getProperty
    simp only [Array.getElem?_append]; simp [hs]

private theorem Assignment.getValue_bindType_eq
    (assignment : Assignment OpCode) (bound : Handle OpCode .type) (query : Handle OpCode .value)
    (value : TypeAttr) (heq : query.id = bound.id) :
    Assignment.getValue (Assignment.bindType assignment bound value) query = none := by
  simp only [Assignment.bindType]
  unfold Assignment.bind
  split
  · rename_i h; unfold Assignment.getValue Assignment.getBinding; rw [Array.getElem?_set]; simp [heq]
  · rename_i h; unfold Assignment.getValue Assignment.getBinding
    rw [heq, Array.getElem?_append_replicate_singleton_self _ _ _ _ h]; simp

private theorem Assignment.getValue_bindType_ne
    (assignment : Assignment OpCode) (bound : Handle OpCode .type) (query : Handle OpCode .value)
    (value : TypeAttr) (hne : query.id ≠ bound.id) :
    Assignment.getValue (Assignment.bindType assignment bound value) query = Assignment.getValue assignment query := by
  simp only [Assignment.bindType]
  unfold Assignment.bind
  split
  · rename_i h; unfold Assignment.getValue Assignment.getBinding
    rw [Array.getElem?_set_ne h (Ne.symm hne)]
  · rename_i h; unfold Assignment.getValue Assignment.getBinding
    rw [Array.getElem?_append_replicate_singleton_ne _ _ _ _ h hne]

private theorem Assignment.getValue_bindProperty_eq
    (assignment : Assignment OpCode) (bound : Handle OpCode (.prop opCode)) (query : Handle OpCode .value)
    (value : propertiesOf opCode) (heq : query.id = bound.id) :
    Assignment.getValue (Assignment.bindProperty assignment bound value) query = none := by
  simp only [Assignment.bindProperty]
  unfold Assignment.bind
  split
  · rename_i h; unfold Assignment.getValue Assignment.getBinding; rw [Array.getElem?_set]; simp [heq]
  · rename_i h; unfold Assignment.getValue Assignment.getBinding
    rw [heq, Array.getElem?_append_replicate_singleton_self _ _ _ _ h]; simp

private theorem Assignment.getValue_bindProperty_ne
    (assignment : Assignment OpCode) (bound : Handle OpCode (.prop opCode)) (query : Handle OpCode .value)
    (value : propertiesOf opCode) (hne : query.id ≠ bound.id) :
    Assignment.getValue (Assignment.bindProperty assignment bound value) query = Assignment.getValue assignment query := by
  simp only [Assignment.bindProperty]
  unfold Assignment.bind
  split
  · rename_i h; unfold Assignment.getValue Assignment.getBinding
    rw [Array.getElem?_set_ne h (Ne.symm hne)]
  · rename_i h; unfold Assignment.getValue Assignment.getBinding
    rw [Array.getElem?_append_replicate_singleton_ne _ _ _ _ h hne]

private theorem SemanticCreateAssignment.getValue_bindType_eq
    (assignment : SemanticCreateAssignment) (bound : Handle OpCode .type) (query : Handle OpCode .value)
    (value : TypeAttr) (heq : query.id = bound.id) :
    (assignment.bindType bound value).getValue query = none := by
  simp only [SemanticCreateAssignment.bindType]
  unfold SemanticCreateAssignment.bind
  split
  · rename_i h; unfold SemanticCreateAssignment.getValue; rw [Array.getElem?_set]; simp [heq]
  · rename_i h
    have hs : assignment.size ≤ bound.id := Nat.le_of_not_gt h
    unfold SemanticCreateAssignment.getValue
    simp only [Array.getElem?_append]; simp [hs, heq]

private theorem SemanticCreateAssignment.getValue_bindType_ne
    (assignment : SemanticCreateAssignment) (bound : Handle OpCode .type) (query : Handle OpCode .value)
    (value : TypeAttr) (hne : query.id ≠ bound.id) :
    (assignment.bindType bound value).getValue query = assignment.getValue query := by
  simp only [SemanticCreateAssignment.bindType]
  unfold SemanticCreateAssignment.bind
  split
  · rename_i h; unfold SemanticCreateAssignment.getValue
    rw [Array.getElem?_set_ne h (Ne.symm hne)]
  · rename_i h
    have hs : assignment.size ≤ bound.id := Nat.le_of_not_gt h
    have hsize : assignment.size + (bound.id - assignment.size) = bound.id :=
      Nat.add_sub_of_le hs
    unfold SemanticCreateAssignment.getValue
    simp only [Array.size_append, Array.size_replicate, Array.getElem?_append,
      Array.getElem?_replicate]; rw [hsize]
    by_cases hquery : query.id < assignment.size
    · have hqb : query.id < bound.id := Nat.lt_of_lt_of_le hquery hs; simp [hquery, hqb]
    · have hqs : assignment.size ≤ query.id := Nat.le_of_not_gt hquery
      by_cases hqb : query.id < bound.id
      · have hgap : query.id - assignment.size < bound.id - assignment.size :=
          Nat.sub_lt_sub_right hqs hqb
        simp [hquery, hqb, hgap]
      · have hdiff : query.id - bound.id ≠ 0 := by omega
        simp [hquery, hqb, hdiff]

private theorem SemanticCreateAssignment.getValue_bindProperty_eq
    (assignment : SemanticCreateAssignment) (bound : Handle OpCode (.prop opCode))
    (query : Handle OpCode .value) (value : propertiesOf opCode) (heq : query.id = bound.id) :
    (assignment.bindProperty bound value).getValue query = none := by
  simp only [SemanticCreateAssignment.bindProperty]
  unfold SemanticCreateAssignment.bind
  split
  · rename_i h; unfold SemanticCreateAssignment.getValue; rw [Array.getElem?_set]; simp [heq]
  · rename_i h
    have hs : assignment.size ≤ bound.id := Nat.le_of_not_gt h
    unfold SemanticCreateAssignment.getValue
    simp only [Array.getElem?_append]; simp [hs, heq]

private theorem SemanticCreateAssignment.getValue_bindProperty_ne
    (assignment : SemanticCreateAssignment) (bound : Handle OpCode (.prop opCode))
    (query : Handle OpCode .value) (value : propertiesOf opCode) (hne : query.id ≠ bound.id) :
    (assignment.bindProperty bound value).getValue query = assignment.getValue query := by
  simp only [SemanticCreateAssignment.bindProperty]
  unfold SemanticCreateAssignment.bind
  split
  · rename_i h; unfold SemanticCreateAssignment.getValue
    rw [Array.getElem?_set_ne h (Ne.symm hne)]
  · rename_i h
    have hs : assignment.size ≤ bound.id := Nat.le_of_not_gt h
    have hsize : assignment.size + (bound.id - assignment.size) = bound.id :=
      Nat.add_sub_of_le hs
    unfold SemanticCreateAssignment.getValue
    simp only [Array.size_append, Array.size_replicate, Array.getElem?_append,
      Array.getElem?_replicate]; rw [hsize]
    by_cases hquery : query.id < assignment.size
    · have hqb : query.id < bound.id := Nat.lt_of_lt_of_le hquery hs; simp [hquery, hqb]
    · have hqs : assignment.size ≤ query.id := Nat.le_of_not_gt hquery
      by_cases hqb : query.id < bound.id
      · have hgap : query.id - assignment.size < bound.id - assignment.size :=
          Nat.sub_lt_sub_right hqs hqb
        simp [hquery, hqb, hgap]
      · have hdiff : query.id - bound.id ≠ 0 := by omega
        simp [hquery, hqb, hdiff]

/-- Concrete and semantic creation assignments carry identical metadata. -/
private def Assignment.MetadataAgrees
    (concrete : Assignment OpCode) (semantic : SemanticCreateAssignment) : Prop :=
  (∀ handle, (Assignment.getType concrete) handle = semantic.getType handle) ∧
  (∀ opCode (handle : Handle OpCode (.prop opCode)),
    (Assignment.getProperty concrete) handle = semantic.getProperty handle)

private theorem SemanticAssignment.ofConcrete_metadataAgrees
    {ctx : WfIRContext OpCode} {assignment : Assignment OpCode}
    {state : InterpreterState ctx} {root : OperationPtr} {rootValues : Array RuntimeValue} :
    Assignment.MetadataAgrees assignment
      (SemanticAssignment.ofConcrete assignment state root rootValues) := by
  constructor
  · intro handle
    unfold Assignment.getType Assignment.getBinding SemanticCreateAssignment.getType
      SemanticAssignment.getType SemanticAssignment.ofConcrete
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
    unfold Assignment.getProperty Assignment.getBinding SemanticCreateAssignment.getProperty
      SemanticAssignment.getProperty SemanticAssignment.ofConcrete
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

private theorem MetadataTuple.Atom.resolve_agrees
    {Handle : Type} (metadataAtom : MetadataTuple.Atom OpCode Handle)
    {concrete : Assignment OpCode} {semantic : SemanticCreateAssignment}
    (hagrees : (Assignment.MetadataAgrees concrete) semantic) (handle : Handle) :
    metadataAtom.resolve concrete handle = metadataAtom.resolve semantic handle := by
  cases metadataAtom with
  | type => exact hagrees.1 handle
  | property opCode => exact hagrees.2 opCode handle

private theorem MetadataTuple.Shape.resolve_agrees
    {Handles : Type} (shape : MetadataTuple.Shape OpCode Handles)
    {concrete : Assignment OpCode} {semantic : SemanticCreateAssignment}
    (hagrees : (Assignment.MetadataAgrees concrete) semantic) (handles : Handles) :
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
    {concrete : Assignment OpCode} {semantic : SemanticCreateAssignment}
    (hagrees : (Assignment.MetadataAgrees concrete) semantic) (handles : Handles) :
    MetadataTuple.resolve (self := bundle) concrete handles =
      MetadataTuple.resolve (self := bundle) semantic handles :=
  MetadataTuple.Shape.resolve_agrees bundle.shape hagrees handles

private theorem Assignment.MetadataAgrees.bindType
    {concrete : Assignment OpCode} {semantic : SemanticCreateAssignment}
    (hagrees : (Assignment.MetadataAgrees concrete) semantic)
    (handle : Handle OpCode .type) (value : TypeAttr) :
    (Assignment.MetadataAgrees ((Assignment.bindType concrete) handle value))
      (semantic.bindType handle value) := by
  constructor
  · intro query
    by_cases heq : query.id = handle.id
    · rw [Assignment.getType_bindType_eq _ _ _ _ heq,
        SemanticCreateAssignment.getType_bindType_eq _ _ _ _ heq]
    · rw [Assignment.getType_bindType_ne _ _ _ _ heq,
        SemanticCreateAssignment.getType_bindType_ne _ _ _ _ heq]
      exact hagrees.1 query
  · intro opCode query
    by_cases heq : query.id = handle.id
    · rw [Assignment.getProperty_bindType_eq _ _ _ _ heq,
        SemanticCreateAssignment.getProperty_bindType_eq _ _ _ _ heq]
    · rw [Assignment.getProperty_bindType_ne _ _ _ _ heq,
        SemanticCreateAssignment.getProperty_bindType_ne _ _ _ _ heq]
      exact hagrees.2 opCode query

private theorem Assignment.MetadataAgrees.bindProperty
    {concrete : Assignment OpCode} {semantic : SemanticCreateAssignment}
    (hagrees : (Assignment.MetadataAgrees concrete) semantic)
    {opCode : OpCode} (handle : Handle OpCode (.prop opCode)) (value : propertiesOf opCode) :
    (Assignment.MetadataAgrees ((Assignment.bindProperty concrete) handle value))
      (semantic.bindProperty handle value) := by
  constructor
  · intro query
    by_cases heq : query.id = handle.id
    · rw [Assignment.getType_bindProperty_eq _ _ _ _ heq,
        SemanticCreateAssignment.getType_bindProperty_eq _ _ _ _ heq]
    · rw [Assignment.getType_bindProperty_ne _ _ _ _ heq,
        SemanticCreateAssignment.getType_bindProperty_ne _ _ _ _ heq]
      exact hagrees.1 query
  · intro queryOpCode query
    by_cases heq : query.id = handle.id
    · rw [Assignment.getProperty_bindProperty_eq _ _ _ _ heq,
        SemanticCreateAssignment.getProperty_bindProperty_eq _ _ _ _ heq]
    · rw [Assignment.getProperty_bindProperty_ne _ _ _ _ heq,
        SemanticCreateAssignment.getProperty_bindProperty_ne _ _ _ _ heq]
      exact hagrees.2 queryOpCode query

/-! Non-metadata bindings overwrite metadata slots consistently on both sides. -/
private theorem Assignment.MetadataAgrees.bindOp
    {concrete : Assignment OpCode} {semantic : SemanticCreateAssignment}
    (hagrees : (Assignment.MetadataAgrees concrete) semantic) (bound : Handle OpCode .op)
    (operation : OperationPtr) (results : Array RuntimeValue) :
    (Assignment.MetadataAgrees ((Assignment.bindOp concrete) bound operation))
      (semantic.bindOp bound results) := by
  constructor
  · intro query
    by_cases heq : query.id = bound.id
    · have hc : (Assignment.getType ((Assignment.bindOp concrete) bound operation)) query = none := by
        simp only [Assignment.bindOp]; unfold Assignment.bind
        split
        · rename_i h; unfold Assignment.getType Assignment.getBinding; rw [Array.getElem?_set]; simp [heq]
        · rename_i h; unfold Assignment.getType Assignment.getBinding
          rw [heq, Array.getElem?_append_replicate_singleton_self _ _ _ _ h]; simp
      have hs : (semantic.bindOp bound results).getType query = none := by
        simp only [SemanticCreateAssignment.bindOp]; unfold SemanticCreateAssignment.bind
        split
        · rename_i h; unfold SemanticCreateAssignment.getType SemanticAssignment.getType
          rw [Array.getElem?_set]; simp [heq]
        · rename_i h
          have hle : semantic.size ≤ bound.id := Nat.le_of_not_gt h
          unfold SemanticCreateAssignment.getType SemanticAssignment.getType
          simp only [Array.getElem?_append]; simp [hle, heq]
      rw [hc, hs]
    · have hc : (Assignment.getType ((Assignment.bindOp concrete) bound operation)) query = (Assignment.getType concrete) query := by
        simp only [Assignment.bindOp]; unfold Assignment.bind
        split
        · rename_i h; unfold Assignment.getType Assignment.getBinding
          rw [Array.getElem?_set_ne h (Ne.symm heq)]
        · rename_i h; unfold Assignment.getType Assignment.getBinding
          rw [Array.getElem?_append_replicate_singleton_ne _ _ _ _ h heq]
      have hs : (semantic.bindOp bound results).getType query = semantic.getType query := by
        simp only [SemanticCreateAssignment.bindOp]; unfold SemanticCreateAssignment.bind
        split
        · rename_i h; unfold SemanticCreateAssignment.getType SemanticAssignment.getType
          rw [Array.getElem?_set_ne h (Ne.symm heq)]
        · rename_i h
          have hle : semantic.size ≤ bound.id := Nat.le_of_not_gt h
          have hsize : semantic.size + (bound.id - semantic.size) = bound.id := Nat.add_sub_of_le hle
          unfold SemanticCreateAssignment.getType SemanticAssignment.getType
          simp only [Array.size_append, Array.size_replicate, Array.getElem?_append,
            Array.getElem?_replicate]; rw [hsize]
          by_cases hquery : query.id < semantic.size
          · have hqb : query.id < bound.id := Nat.lt_of_lt_of_le hquery hle
            simp [hquery, hqb]
          · have hqs : semantic.size ≤ query.id := Nat.le_of_not_gt hquery
            by_cases hqb : query.id < bound.id
            · have hgap := Nat.sub_lt_sub_right hqs hqb
              simp [hquery, hqb, hgap]
            · have hdiff : query.id - bound.id ≠ 0 := by omega
              simp [hquery, hqb, hdiff]
      rw [hc, hs]; exact hagrees.1 query
  · intro queryOpCode query
    by_cases heq : query.id = bound.id
    · have hc : (Assignment.getProperty ((Assignment.bindOp concrete) bound operation)) query = none := by
        simp only [Assignment.bindOp]; unfold Assignment.bind
        split
        · rename_i h; unfold Assignment.getProperty Assignment.getBinding; rw [Array.getElem?_set]; simp [heq]
        · rename_i h; unfold Assignment.getProperty Assignment.getBinding
          rw [heq, Array.getElem?_append_replicate_singleton_self _ _ _ _ h]; simp
      have hs : (semantic.bindOp bound results).getProperty query = none := by
        simp only [SemanticCreateAssignment.bindOp]; unfold SemanticCreateAssignment.bind
        split
        · rename_i h
          unfold SemanticCreateAssignment.getProperty SemanticAssignment.getProperty
          rw [Array.getElem?_set]; simp [heq]
        · rename_i h
          have hle : semantic.size ≤ bound.id := Nat.le_of_not_gt h
          unfold SemanticCreateAssignment.getProperty SemanticAssignment.getProperty
          simp only [Array.getElem?_append]; simp [hle, heq]
      rw [hc, hs]
    · have hc : (Assignment.getProperty ((Assignment.bindOp concrete) bound operation)) query =
          (Assignment.getProperty concrete) query := by
        simp only [Assignment.bindOp]; unfold Assignment.bind
        split
        · rename_i h; unfold Assignment.getProperty Assignment.getBinding
          rw [Array.getElem?_set_ne h (Ne.symm heq)]
        · rename_i h; unfold Assignment.getProperty Assignment.getBinding
          rw [Array.getElem?_append_replicate_singleton_ne _ _ _ _ h heq]
      have hs : (semantic.bindOp bound results).getProperty query =
          semantic.getProperty query := by
        simp only [SemanticCreateAssignment.bindOp]; unfold SemanticCreateAssignment.bind
        split
        · rename_i h; unfold SemanticCreateAssignment.getProperty SemanticAssignment.getProperty
          rw [Array.getElem?_set_ne h (Ne.symm heq)]
        · rename_i h
          have hle : semantic.size ≤ bound.id := Nat.le_of_not_gt h
          have hsize : semantic.size + (bound.id - semantic.size) = bound.id := Nat.add_sub_of_le hle
          unfold SemanticCreateAssignment.getProperty SemanticAssignment.getProperty
          simp only [Array.size_append, Array.size_replicate, Array.getElem?_append,
            Array.getElem?_replicate]; rw [hsize]
          by_cases hquery : query.id < semantic.size
          · have hqb : query.id < bound.id := Nat.lt_of_lt_of_le hquery hle
            simp [hquery, hqb]
          · have hqs : semantic.size ≤ query.id := Nat.le_of_not_gt hquery
            by_cases hqb : query.id < bound.id
            · have hgap := Nat.sub_lt_sub_right hqs hqb
              simp [hquery, hqb, hgap]
            · have hdiff : query.id - bound.id ≠ 0 := by omega
              simp [hquery, hqb, hdiff]
      rw [hc, hs]; exact hagrees.2 queryOpCode query

private theorem Assignment.MetadataAgrees.bindValue
    {concrete : Assignment OpCode} {semantic : SemanticCreateAssignment}
    (hagrees : (Assignment.MetadataAgrees concrete) semantic) (bound : Handle OpCode .value)
    (value : ValuePtr) (runtime : RuntimeValue) :
    (Assignment.MetadataAgrees ((Assignment.bindValue concrete) bound value))
      (semantic.bindValue bound runtime) := by
  constructor
  · intro query
    by_cases heq : query.id = bound.id
    · have hc : (Assignment.getType ((Assignment.bindValue concrete) bound value)) query = none := by
        simp only [Assignment.bindValue]; unfold Assignment.bind
        split
        · rename_i h; unfold Assignment.getType Assignment.getBinding; rw [Array.getElem?_set]; simp [heq]
        · rename_i h; unfold Assignment.getType Assignment.getBinding
          rw [heq, Array.getElem?_append_replicate_singleton_self _ _ _ _ h]; simp
      have hs : (semantic.bindValue bound runtime).getType query = none := by
        simp only [SemanticCreateAssignment.bindValue]; unfold SemanticCreateAssignment.bind
        split
        · rename_i h; unfold SemanticCreateAssignment.getType SemanticAssignment.getType
          rw [Array.getElem?_set]; simp [heq]
        · rename_i h
          have hle : semantic.size ≤ bound.id := Nat.le_of_not_gt h
          unfold SemanticCreateAssignment.getType SemanticAssignment.getType
          simp only [Array.getElem?_append]; simp [hle, heq]
      rw [hc, hs]
    · have hc : (Assignment.getType ((Assignment.bindValue concrete) bound value)) query = (Assignment.getType concrete) query := by
        simp only [Assignment.bindValue]; unfold Assignment.bind
        split
        · rename_i h; unfold Assignment.getType Assignment.getBinding
          rw [Array.getElem?_set_ne h (Ne.symm heq)]
        · rename_i h; unfold Assignment.getType Assignment.getBinding
          rw [Array.getElem?_append_replicate_singleton_ne _ _ _ _ h heq]
      have hs : (semantic.bindValue bound runtime).getType query = semantic.getType query := by
        simp only [SemanticCreateAssignment.bindValue]; unfold SemanticCreateAssignment.bind
        split
        · rename_i h; unfold SemanticCreateAssignment.getType SemanticAssignment.getType
          rw [Array.getElem?_set_ne h (Ne.symm heq)]
        · rename_i h
          have hle : semantic.size ≤ bound.id := Nat.le_of_not_gt h
          have hsize : semantic.size + (bound.id - semantic.size) = bound.id := Nat.add_sub_of_le hle
          unfold SemanticCreateAssignment.getType SemanticAssignment.getType
          simp only [Array.size_append, Array.size_replicate, Array.getElem?_append,
            Array.getElem?_replicate]; rw [hsize]
          by_cases hquery : query.id < semantic.size
          · have hqb : query.id < bound.id := Nat.lt_of_lt_of_le hquery hle
            simp [hquery, hqb]
          · have hqs : semantic.size ≤ query.id := Nat.le_of_not_gt hquery
            by_cases hqb : query.id < bound.id
            · have hgap := Nat.sub_lt_sub_right hqs hqb
              simp [hquery, hqb, hgap]
            · have hdiff : query.id - bound.id ≠ 0 := by omega
              simp [hquery, hqb, hdiff]
      rw [hc, hs]; exact hagrees.1 query
  · intro queryOpCode query
    by_cases heq : query.id = bound.id
    · have hc : (Assignment.getProperty ((Assignment.bindValue concrete) bound value)) query = none := by
        simp only [Assignment.bindValue]; unfold Assignment.bind
        split
        · rename_i h; unfold Assignment.getProperty Assignment.getBinding; rw [Array.getElem?_set]; simp [heq]
        · rename_i h; unfold Assignment.getProperty Assignment.getBinding
          rw [heq, Array.getElem?_append_replicate_singleton_self _ _ _ _ h]; simp
      have hs : (semantic.bindValue bound runtime).getProperty query = none := by
        simp only [SemanticCreateAssignment.bindValue]; unfold SemanticCreateAssignment.bind
        split
        · rename_i h
          unfold SemanticCreateAssignment.getProperty SemanticAssignment.getProperty
          rw [Array.getElem?_set]; simp [heq]
        · rename_i h
          have hle : semantic.size ≤ bound.id := Nat.le_of_not_gt h
          unfold SemanticCreateAssignment.getProperty SemanticAssignment.getProperty
          simp only [Array.getElem?_append]; simp [hle, heq]
      rw [hc, hs]
    · have hc : (Assignment.getProperty ((Assignment.bindValue concrete) bound value)) query =
          (Assignment.getProperty concrete) query := by
        simp only [Assignment.bindValue]; unfold Assignment.bind
        split
        · rename_i h; unfold Assignment.getProperty Assignment.getBinding
          rw [Array.getElem?_set_ne h (Ne.symm heq)]
        · rename_i h; unfold Assignment.getProperty Assignment.getBinding
          rw [Array.getElem?_append_replicate_singleton_ne _ _ _ _ h heq]
      have hs : (semantic.bindValue bound runtime).getProperty query =
          semantic.getProperty query := by
        simp only [SemanticCreateAssignment.bindValue]; unfold SemanticCreateAssignment.bind
        split
        · rename_i h; unfold SemanticCreateAssignment.getProperty SemanticAssignment.getProperty
          rw [Array.getElem?_set_ne h (Ne.symm heq)]
        · rename_i h
          have hle : semantic.size ≤ bound.id := Nat.le_of_not_gt h
          have hsize : semantic.size + (bound.id - semantic.size) = bound.id := Nat.add_sub_of_le hle
          unfold SemanticCreateAssignment.getProperty SemanticAssignment.getProperty
          simp only [Array.size_append, Array.size_replicate, Array.getElem?_append,
            Array.getElem?_replicate]; rw [hsize]
          by_cases hquery : query.id < semantic.size
          · have hqb : query.id < bound.id := Nat.lt_of_lt_of_le hquery hle
            simp [hquery, hqb]
          · have hqs : semantic.size ≤ query.id := Nat.le_of_not_gt hquery
            by_cases hqb : query.id < bound.id
            · have hgap := Nat.sub_lt_sub_right hqs hqb
              simp [hquery, hqb, hgap]
            · have hdiff : query.id - bound.id ≠ 0 := by omega
              simp [hquery, hqb, hdiff]
      rw [hc, hs]; exact hagrees.2 queryOpCode query


private theorem Assignment.MetadataAgrees.bindValues
    {concrete : Assignment OpCode} {semantic : SemanticCreateAssignment}
    (hagrees : (Assignment.MetadataAgrees concrete) semantic) :
    ∀ handles values runtimes,
      values.length = handles.length → runtimes.length = handles.length →
      (Assignment.MetadataAgrees ((Assignment.bindValues concrete) handles values))
        (semantic.bindValues handles runtimes)
  | [], [], [], _, _ => hagrees
  | handle :: handles, value :: values, runtime :: runtimes, hvalues, hruntimes => by
      simp only [Assignment.bindValues, SemanticCreateAssignment.bindValues]
      exact (hagrees.bindValue handle value runtime).bindValues handles values runtimes
        (by simpa using hvalues) (by simpa using hruntimes)
  | [], _ :: _, _, hvalues, _ => by simp at hvalues
  | _ :: _, [], _, hvalues, _ => by simp at hvalues
  | [], [], _ :: _, _, hruntimes => by simp at hruntimes
  | _ :: _, _ :: _, [], _, hruntimes => by simp at hruntimes
private theorem MetadataTuple.Atom.bind_agrees
    {Handle : Type} (metadataAtom : MetadataTuple.Atom OpCode Handle)
    {concrete concrete' : Assignment OpCode}
    {semantic semantic' : SemanticCreateAssignment}
    (hagrees : (Assignment.MetadataAgrees concrete) semantic) (handle : Handle)
    (value : metadataAtom.Value)
    (hconcrete : metadataAtom.bind concrete handle value = some concrete')
    (hsemantic : metadataAtom.bind semantic handle value = some semantic') :
    (Assignment.MetadataAgrees concrete') semantic' := by
  cases metadataAtom with
  | type =>
    change some ((Assignment.bindType concrete) handle value) = some concrete' at hconcrete
    change some (semantic.bindType handle value) = some semantic' at hsemantic
    have hconcreteEq : (Assignment.bindType concrete) handle value = concrete' :=
      Option.some.inj hconcrete
    have hsemanticEq : semantic.bindType handle value = semantic' :=
      Option.some.inj hsemantic
    rw [← hconcreteEq, ← hsemanticEq]
    exact hagrees.bindType handle value
  | property opCode =>
    change some ((Assignment.bindProperty concrete) handle value) = some concrete' at hconcrete
    change some (semantic.bindProperty handle value) = some semantic' at hsemantic
    have hconcreteEq : (Assignment.bindProperty concrete) handle value = concrete' :=
      Option.some.inj hconcrete
    have hsemanticEq : semantic.bindProperty handle value = semantic' :=
      Option.some.inj hsemantic
    rw [← hconcreteEq, ← hsemanticEq]
    exact hagrees.bindProperty handle value

private theorem MetadataTuple.Shape.bind_agrees
    {Handles : Type} (shape : MetadataTuple.Shape OpCode Handles)
    {concrete concrete' : Assignment OpCode}
    {semantic semantic' : SemanticCreateAssignment}
    (hagrees : (Assignment.MetadataAgrees concrete) semantic) (handles : Handles)
    (values : shape.Values)
    (hconcrete : shape.bind concrete handles values = some concrete')
    (hsemantic : shape.bind semantic handles values = some semantic') :
    (Assignment.MetadataAgrees concrete') semantic' := by
  induction shape generalizing concrete semantic concrete' semantic' with
  | unit =>
    change some concrete = some concrete' at hconcrete
    change some semantic = some semantic' at hsemantic
    simp at hconcrete hsemantic
    subst concrete'; subst semantic'; exact hagrees
  | atom metadataAtom =>
    exact metadataAtom.bind_agrees hagrees handles values hconcrete hsemantic
  | cons head tail tailIH =>
    simp only [MetadataTuple.Shape.bind, Option.bind_eq_bind] at hconcrete hsemantic
    rw [Option.bind_eq_some_iff] at hconcrete hsemantic
    obtain ⟨concreteMiddle, hconcreteHead, hconcreteTail⟩ := hconcrete
    obtain ⟨semanticMiddle, hsemanticHead, hsemanticTail⟩ := hsemantic
    have hmiddle := head.bind_agrees hagrees handles.1 values.1 hconcreteHead hsemanticHead
    exact tailIH (concrete := concreteMiddle) (semantic := semanticMiddle)
      hmiddle handles.2 values.2 hconcreteTail hsemanticTail

private theorem Assignment.MetadataAgrees.bind
    {Handles : Type} [bundle : IsMetadataTuple OpCode Handles]
    {concrete concrete' : Assignment OpCode}
    {semantic semantic' : SemanticCreateAssignment}
    (hagrees : (Assignment.MetadataAgrees concrete) semantic) (handles : Handles)
    (values : MetadataValues OpCode Handles)
    (hconcrete : MetadataTuple.bind (self := bundle) concrete handles values = some concrete')
    (hsemantic : MetadataTuple.bind (self := bundle) semantic handles values = some semantic') :
    (Assignment.MetadataAgrees concrete') semantic' :=
  MetadataTuple.Shape.bind_agrees bundle.shape
    hagrees handles values hconcrete hsemantic

private theorem Assignment.Refines.bindType
    {ctx : WfIRContext OpCode} {targetState : InterpreterState ctx}
    {concrete : Assignment OpCode} {semantic : SemanticCreateAssignment}
    (hrefines : (Assignment.Refines concrete) semantic targetState)
    (bound : Handle OpCode .type) (type : TypeAttr) :
    (Assignment.Refines ((Assignment.bindType concrete) bound type)) (semantic.bindType bound type) targetState := by
  intro query value sourceRuntime hconcrete hsemantic
  by_cases heq : query.id = bound.id
  · rw [Assignment.getValue_bindType_eq _ _ _ _ heq] at hconcrete
    simp at hconcrete
  · rw [Assignment.getValue_bindType_ne _ _ _ _ heq] at hconcrete
    rw [SemanticCreateAssignment.getValue_bindType_ne _ _ _ _ heq] at hsemantic
    exact hrefines query value sourceRuntime hconcrete hsemantic

private theorem Assignment.Refines.bindOp
    {ctx : WfIRContext OpCode} {targetState : InterpreterState ctx}
    {concrete : Assignment OpCode} {semantic : SemanticCreateAssignment}
    (hrefines : (Assignment.Refines concrete) semantic targetState)
    (bound : Handle OpCode .op) (operation : OperationPtr) (results : Array RuntimeValue) :
    (Assignment.Refines ((Assignment.bindOp concrete) bound operation))
      (semantic.bindOp bound results) targetState := by
  intro query value sourceRuntime hconcrete hsemantic
  by_cases heq : query.id = bound.id
  · rw [Assignment.getValue_bindOp_of_eq _ _ _ _ heq] at hconcrete
    simp at hconcrete
  · rw [Assignment.getValue_bindOp_of_ne _ _ _ _ heq] at hconcrete
    rw [SemanticCreateAssignment.getValue_bindOp_of_ne _ _ _ _ heq] at hsemantic
    exact hrefines query value sourceRuntime hconcrete hsemantic

private theorem Assignment.Refines.bindValue
    {ctx : WfIRContext OpCode} {targetState : InterpreterState ctx}
    {concrete : Assignment OpCode} {semantic : SemanticCreateAssignment}
    (hrefines : (Assignment.Refines concrete) semantic targetState)
    (bound : Handle OpCode .value) (value : ValuePtr)
    (sourceRuntime targetRuntime : RuntimeValue)
    (htarget : targetState.variables.getVar? value = some targetRuntime)
    (hrefinement : sourceRuntime ⊒ targetRuntime) :
    (Assignment.Refines ((Assignment.bindValue concrete) bound value))
      (semantic.bindValue bound sourceRuntime) targetState := by
  intro query queryValue queryRuntime hconcrete hsemantic
  by_cases heq : query.id = bound.id
  · rw [Assignment.getValue_bindValue_of_eq _ _ _ _ heq] at hconcrete
    rw [SemanticCreateAssignment.getValue_bindValue_of_eq _ _ _ _ heq] at hsemantic
    simp only [Option.some.injEq] at hconcrete hsemantic
    subst queryValue
    subst queryRuntime
    exact ⟨targetRuntime, htarget, hrefinement⟩
  · rw [Assignment.getValue_bindValue_of_ne _ _ _ _ heq] at hconcrete
    rw [SemanticCreateAssignment.getValue_bindValue_of_ne _ _ _ _ heq] at hsemantic
    exact hrefines query queryValue queryRuntime hconcrete hsemantic

private theorem Assignment.Refines.bindValues
    {ctx : WfIRContext OpCode} {targetState : InterpreterState ctx}
    {concrete : Assignment OpCode} {semantic : SemanticCreateAssignment}
    (hrefines : (Assignment.Refines concrete) semantic targetState) :
    ∀ (handles : List (Handle OpCode .value)) (values : List ValuePtr)
      (sourceRuntimes targetRuntimes : List RuntimeValue),
      values.length = handles.length →
      sourceRuntimes.length = handles.length →
      targetRuntimes.length = handles.length →
      values.mapM targetState.variables.getVar? = some targetRuntimes →
      sourceRuntimes.toArray ⊒ targetRuntimes.toArray →
      (Assignment.Refines ((Assignment.bindValues concrete) handles values))
        (semantic.bindValues handles sourceRuntimes) targetState := by
  intro handles
  induction handles generalizing concrete semantic with
  | nil =>
      intro values sourceRuntimes targetRuntimes hvalues hsources htargets _ _
      have hvalues' : values = [] := List.eq_nil_of_length_eq_zero (by simpa using hvalues)
      have hsources' : sourceRuntimes = [] :=
        List.eq_nil_of_length_eq_zero (by simpa using hsources)
      have htargets' : targetRuntimes = [] :=
        List.eq_nil_of_length_eq_zero (by simpa using htargets)
      subst values
      subst sourceRuntimes
      subst targetRuntimes
      exact hrefines
  | cons handle handles ih =>
      intro values sourceRuntimes targetRuntimes hvalues hsources htargets hlookup hrefinement
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
              simp only [Assignment.bindValues, SemanticCreateAssignment.bindValues]
              exact ih (hrefines.bindValue handle value source target hhead hrefinement'.1)
                values sources targets (by simpa using hvalues) (by simpa using hsources)
                (by simpa using htargets) htail hrefinement'.2

private theorem VariableState.mapM_getResults_of_setResultValues
    {ctx : WfIRContext OpCode} {state state' : VariableState ctx}
    {op : OperationPtr} {resultValues : Array RuntimeValue}
    {inBounds : op.InBounds ctx.raw}
    (hset : state.setResultValues? op resultValues inBounds = some state') :
    (op.getResults! ctx.raw).toList.mapM state'.getVar? =
      some resultValues.toList := by
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
  simpa [Array.mapM_eq_mapM_toList] using
    congrArg (Option.map Array.toList) harray

private theorem Assignment.Refines.bindProperty
    {ctx : WfIRContext OpCode} {targetState : InterpreterState ctx}
    {concrete : Assignment OpCode} {semantic : SemanticCreateAssignment}
    (hrefines : (Assignment.Refines concrete) semantic targetState)
    (bound : Handle OpCode (.prop opCode)) (property : propertiesOf opCode) :
    (Assignment.Refines ((Assignment.bindProperty concrete) bound property))
      (semantic.bindProperty bound property) targetState := by
  intro query value sourceRuntime hconcrete hsemantic
  by_cases heq : query.id = bound.id
  · rw [Assignment.getValue_bindProperty_eq _ _ _ _ heq] at hconcrete
    simp at hconcrete
  · rw [Assignment.getValue_bindProperty_ne _ _ _ _ heq] at hconcrete
    rw [SemanticCreateAssignment.getValue_bindProperty_ne _ _ _ _ heq] at hsemantic
    exact hrefines query value sourceRuntime hconcrete hsemantic

private theorem MetadataTuple.Atom.bind_refines
    {Handle : Type} (metadataAtom : MetadataTuple.Atom OpCode Handle)
    {ctx : WfIRContext OpCode} {targetState : InterpreterState ctx}
    {concrete concrete' : Assignment OpCode}
    {semantic semantic' : SemanticCreateAssignment}
    (hrefines : (Assignment.Refines concrete) semantic targetState) (handle : Handle)
    (value : metadataAtom.Value)
    (hconcrete : metadataAtom.bind concrete handle value = some concrete')
    (hsemantic : metadataAtom.bind semantic handle value = some semantic') :
    (Assignment.Refines concrete') semantic' targetState := by
  cases metadataAtom with
  | type =>
    change some ((Assignment.bindType concrete) handle value) = some concrete' at hconcrete
    change some (semantic.bindType handle value) = some semantic' at hsemantic
    have hc := Option.some.inj hconcrete
    have hs := Option.some.inj hsemantic
    rw [← hc, ← hs]
    exact hrefines.bindType handle value
  | property opCode =>
    change some ((Assignment.bindProperty concrete) handle value) = some concrete' at hconcrete
    change some (semantic.bindProperty handle value) = some semantic' at hsemantic
    have hc := Option.some.inj hconcrete
    have hs := Option.some.inj hsemantic
    rw [← hc, ← hs]
    exact hrefines.bindProperty handle value

private theorem MetadataTuple.Shape.bind_refines
    {Handles : Type} (shape : MetadataTuple.Shape OpCode Handles)
    {ctx : WfIRContext OpCode} {targetState : InterpreterState ctx}
    {concrete concrete' : Assignment OpCode}
    {semantic semantic' : SemanticCreateAssignment}
    (hrefines : (Assignment.Refines concrete) semantic targetState) (handles : Handles)
    (values : shape.Values)
    (hconcrete : shape.bind concrete handles values = some concrete')
    (hsemantic : shape.bind semantic handles values = some semantic') :
    (Assignment.Refines concrete') semantic' targetState := by
  induction shape generalizing concrete semantic concrete' semantic' with
  | unit =>
    change some concrete = some concrete' at hconcrete
    change some semantic = some semantic' at hsemantic
    simp at hconcrete hsemantic; subst concrete'; subst semantic'; exact hrefines
  | atom metadataAtom =>
    exact metadataAtom.bind_refines hrefines handles values hconcrete hsemantic
  | cons head tail tailIH =>
    simp only [MetadataTuple.Shape.bind, Option.bind_eq_bind] at hconcrete hsemantic
    rw [Option.bind_eq_some_iff] at hconcrete hsemantic
    obtain ⟨concreteMiddle, hcHead, hcTail⟩ := hconcrete
    obtain ⟨semanticMiddle, hsHead, hsTail⟩ := hsemantic
    have hmiddle := head.bind_refines hrefines handles.1 values.1 hcHead hsHead
    exact tailIH (concrete := concreteMiddle) (semantic := semanticMiddle)
      hmiddle handles.2 values.2 hcTail hsTail

private theorem Assignment.Refines.getValuesList
    {ctx : WfIRContext OpCode}
    {concrete : Assignment OpCode} {semantic : SemanticCreateAssignment}
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
    {concrete : Assignment OpCode} {semantic : SemanticCreateAssignment}
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

private theorem Assignment.Refines.getCreateOperands
    {ctx : WfIRContext OpCode}
    {concrete : Assignment OpCode} {semantic : SemanticCreateAssignment}
    {targetState : InterpreterState ctx}
    (hrefines : (Assignment.Refines concrete) semantic targetState)
    {operands : Array (CreateOperand OpCode)} {values : Array ValuePtr}
    {sourceRuntimes : Array RuntimeValue}
    (hconcrete : CreateOperand.resolveValues operands concrete = some values)
    (hsemantic : CreateOperand.getValues operands semantic = some sourceRuntimes) :
    ∃ targetRuntimes,
      values.mapM targetState.variables.getVar? = some targetRuntimes ∧
      sourceRuntimes ⊒ targetRuntimes := by
  apply hrefines.getValues (handles := operands.map (fun operand => operand.value))
  · simpa [Assignment.getValues, CreateOperand.resolveValues,
      CreateOperand.resolveValue, Array.mapM_map, Function.comp_def] using hconcrete
  · simpa [SemanticAssignment.getValues, CreateOperand.getValues,
      CreateOperand.getValue, Array.mapM_map, Function.comp_def] using hsemantic

private def Assignment.MatchValuesInBounds
    (assignment : Assignment OpCode) (ctx : WfIRContext OpCode) : Prop :=
  ∀ handle value, Assignment.getValue assignment handle = some value → value.InBounds ctx.raw

private theorem CreateOperand.exists_target_value_of_refines
    {concreteCreated : Assignment OpCode} {semanticCreated : SemanticCreateAssignment}
    {ctx : WfIRContext OpCode} {targetState : InterpreterState ctx}
    {operand : CreateOperand OpCode} {value : ValuePtr} {sourceRuntime : RuntimeValue}
    (hcreated : Assignment.Refines concreteCreated semanticCreated targetState)
    (hconcrete : operand.resolveValue concreteCreated = some value)
    (hsemantic : operand.getValue semanticCreated = some sourceRuntime) :
    ∃ targetRuntime, targetState.variables.getVar? value = some targetRuntime ∧
      sourceRuntime ⊒ targetRuntime := by
  rcases operand with ⟨handle⟩
  exact hcreated handle value sourceRuntime hconcrete hsemantic

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

private theorem Assignment.ValuesInBounds.bindType
    {created : Assignment OpCode} {ctx : WfIRContext OpCode}
    (hinBounds : (Assignment.ValuesInBounds created) ctx) (bound : Handle OpCode .type) (type : TypeAttr) :
    (Assignment.ValuesInBounds ((Assignment.bindType created) bound type)) ctx := by
  intro query value hget
  by_cases heq : query.id = bound.id
  · simp only [Assignment.bindType] at hget
    unfold Assignment.bind at hget
    split at hget
    · rename_i h; unfold Assignment.getValue Assignment.getBinding at hget
      rw [Array.getElem?_set] at hget; simp [heq] at hget
    · rename_i h; unfold Assignment.getValue Assignment.getBinding at hget
      rw [heq, Array.getElem?_append_replicate_singleton_self _ _ _ _ h] at hget
      simp at hget
  · apply hinBounds query value
    simp only [Assignment.bindType] at hget
    unfold Assignment.bind at hget
    split at hget
    · rename_i h; unfold Assignment.getValue Assignment.getBinding at hget ⊢
      rw [Array.getElem?_set_ne h (Ne.symm heq)] at hget
      exact hget
    · rename_i h; unfold Assignment.getValue Assignment.getBinding at hget ⊢
      rw [Array.getElem?_append_replicate_singleton_ne _ _ _ _ h heq] at hget
      exact hget

private theorem Assignment.ValuesInBounds.bindProperty
    {created : Assignment OpCode} {ctx : WfIRContext OpCode}
    (hinBounds : (Assignment.ValuesInBounds created) ctx) (bound : Handle OpCode (.prop opCode))
    (property : propertiesOf opCode) :
    (Assignment.ValuesInBounds ((Assignment.bindProperty created) bound property)) ctx := by
  intro query value hget
  by_cases heq : query.id = bound.id
  · simp only [Assignment.bindProperty] at hget
    unfold Assignment.bind at hget
    split at hget
    · rename_i h; unfold Assignment.getValue Assignment.getBinding at hget
      rw [Array.getElem?_set] at hget; simp [heq] at hget
    · rename_i h; unfold Assignment.getValue Assignment.getBinding at hget
      rw [heq, Array.getElem?_append_replicate_singleton_self _ _ _ _ h] at hget
      simp at hget
  · apply hinBounds query value
    simp only [Assignment.bindProperty] at hget
    unfold Assignment.bind at hget
    split at hget
    · rename_i h; unfold Assignment.getValue Assignment.getBinding at hget ⊢
      rw [Array.getElem?_set_ne h (Ne.symm heq)] at hget
      exact hget
    · rename_i h; unfold Assignment.getValue Assignment.getBinding at hget ⊢
      rw [Array.getElem?_append_replicate_singleton_ne _ _ _ _ h heq] at hget
      exact hget

private theorem MetadataTuple.Atom.bind_valuesInBounds
    {Handle : Type} (metadataAtom : MetadataTuple.Atom OpCode Handle)
    {created created' : Assignment OpCode} {ctx : WfIRContext OpCode}
    (hinBounds : (Assignment.ValuesInBounds created) ctx) (handle : Handle) (value : metadataAtom.Value)
    (hbind : metadataAtom.bind created handle value = some created') :
    (Assignment.ValuesInBounds created') ctx := by
  cases metadataAtom with
  | type =>
    change some ((Assignment.bindType created) handle value) = some created' at hbind
    simp at hbind; subst created'; exact hinBounds.bindType handle value
  | property opCode =>
    change some ((Assignment.bindProperty created) handle value) = some created' at hbind
    simp at hbind; subst created'; exact hinBounds.bindProperty handle value

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

private theorem CreateDecl.run_withCreatedOp
    {decl : CreateDecl OpCode} {created created' : Assignment OpCode}
    {ctx ctx' : WfIRContext OpCode} {op : OperationPtr}
    (hrun : decl.run created ctx = some (ctx', created', op)) :
    WfIRContext.WithCreatedOps ctx ctx' := by
  cases decl with
  | operation opCode operands resultTypes propertySource opHandle results =>
    simp only [CreateDecl.run, Option.bind_eq_bind] at hrun
    simp only [Option.bind_eq_some_iff] at hrun
    rcases hrun with
      ⟨concreteOperands, hoperands, concreteResultTypes, htypes,
        concreteProperties, hproperties, returnValue, hreturnValue, returnType, hreturnType,
        _, hresultCount, _, hresultHandles, _, htypeEq, hrun⟩
    split at hrun
    · rename_i hoper
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨createdPair, hcreate, hrun⟩ := hrun
      rcases createdPair with ⟨newCtx, newOp⟩
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at hrun
      rcases hrun with ⟨rfl, rfl, rfl⟩
      exact .CreatedOp ctx ctx newCtx (.Nil ctx)
        ⟨opCode, concreteResultTypes, concreteOperands, #[], #[], concreteProperties,
          hoper, by simp, by simp, by simp, hcreate⟩
    · simp at hrun
  | applyNative => simp [CreateDecl.run] at hrun

private theorem CreateDecl.run_operationInBounds
    {decl : CreateDecl OpCode} {created created' : Assignment OpCode}
    {ctx ctx' : WfIRContext OpCode} {op : OperationPtr}
    (hrun : decl.run created ctx = some (ctx', created', op)) :
    op.InBounds ctx'.raw := by
  cases decl with
  | operation opCode operands resultTypes propertySource opHandle results =>
    simp only [CreateDecl.run, Option.bind_eq_bind] at hrun
    simp only [Option.bind_eq_some_iff] at hrun
    rcases hrun with
      ⟨concreteOperands, hoperands, concreteResultTypes, htypes,
        concreteProperties, hproperties, returnValue, hreturnValue, returnType, hreturnType,
        _, hresultCount, _, hresultHandles, _, htypeEq, hrun⟩
    split at hrun
    · rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨createdPair, hcreate, hrun⟩ := hrun
      rcases createdPair with ⟨newCtx, newOp⟩
      simp at hrun
      rcases hrun with ⟨rfl, rfl, rfl⟩
      exact WfRewriter.createOp_new_inBounds newOp hcreate
    · simp at hrun
  | applyNative => simp [CreateDecl.run] at hrun

private theorem CreateDecl.run_valuesInBounds
    {decl : CreateDecl OpCode} {created created' : Assignment OpCode}
    {ctx ctx' : WfIRContext OpCode} {op : OperationPtr}
    (hcreated : Assignment.ValuesInBounds created ctx)
    (hrun : decl.run created ctx = some (ctx', created', op)) :
    Assignment.ValuesInBounds created' ctx' := by
  cases decl with
  | operation opCode operands resultTypes properties opHandle results =>
    simp only [CreateDecl.run, Option.bind_eq_bind] at hrun
    simp only [Option.bind_eq_some_iff] at hrun
    rcases hrun with
      ⟨concreteOperands, hoperands, concreteResultTypes, htypes,
        concreteProperties, hproperties, returnValue, hreturnValue, returnType, hreturnType,
        _, hresultCount, _, hresultHandles, _, htypeEq, hrun⟩
    split at hrun
    · rename_i hoper
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨createdPair, hcreate, hrun⟩ := hrun
      rcases createdPair with ⟨newCtx, newOp⟩
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at hrun
      rcases hrun with ⟨rfl, rfl, rfl⟩
      intro handle value hget
      have hconcreteResultTypesSize : concreteResultTypes.size = 1 := by
        simpa [_root_.guard] using hresultCount
      have hresultHandlesSize : results.size = 1 := by
        have : results.size = concreteResultTypes.size := by
          simpa [_root_.guard] using hresultHandles
        omega
      obtain ⟨resultHandle, rfl⟩ := Array.eq_singleton_of_size_eq_one hresultHandlesSize
      have hnumResults : newOp.getNumResults! newCtx.raw = 1 := by
        simpa [hconcreteResultTypesSize] using
          (OperationPtr.getNumResults!_WfRewriter_createOp (operation := newOp) hcreate)
      have hresultsSize : (newOp.getResults! newCtx.raw).size = 1 := by
        rw [OperationPtr.getResults!.size_eq_getNumResults!, hnumResults]
      have hresultsEq : newOp.getResults! newCtx.raw =
          #[.opResult (newOp.getResult 0)] := by
        apply Array.ext
        · simp [hresultsSize]
        · intro i hi₁ hi₂
          match i, hi₁ with
          | 0, hi =>
            apply OperationPtr.getResults!.getElem_eq_getResult
            rw [← OperationPtr.getResults!.size_eq_getNumResults!]
            exact hi
      rw [hresultsEq] at hget
      simp only [Assignment.bindValues] at hget
      by_cases hresult : handle.id = resultHandle.id
      · rw [Assignment.getValue_bindValue_of_eq _ _ _ _ hresult] at hget
        simp only [Option.some.injEq] at hget
        subst value
        apply ValuePtr.InBounds.op_result
        apply OperationPtr.getResult_inBounds newOp
          (WfRewriter.createOp_new_inBounds newOp hcreate) 0
        grind
      · by_cases hop : handle.id = opHandle.id
        · by_cases hopResult : opHandle.id = resultHandle.id
          · exact (hresult (hop.trans hopResult)).elim
          · rw [Assignment.getValue_bindValue_of_ne _ _ _ _ hresult,
              Assignment.getValue_bindOp_of_eq _ _ _ _ hop] at hget
            simp at hget
        · have hold : Assignment.getValue created handle = some value := by
            simpa [Assignment.bindValues,
              Assignment.getValue_bindValue_of_ne _ _ _ _ hresult,
              Assignment.getValue_bindOp_of_ne _ _ _ _ hop] using hget
          exact (WfRewriter.createOp_inBounds_mono (ptr := .value value) hcreate)
            (hcreated handle value hold)
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
    | operation opCode operands resultTypes properties opHandle results =>
      simp only [CreateProg.runDecls, Option.bind_eq_bind] at hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨createdHead, hhead, hrun⟩ := hrun
      rcases createdHead with ⟨headCtx, headCreated, headOp⟩
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨createdTail, htail, hrun⟩ := hrun
      rcases createdTail with ⟨tailCtx, tailOps, tailCreated⟩
      simp at hrun
      obtain ⟨rfl, rfl, rfl⟩ := hrun
      exact WfIRContext.WithCreatedOps.trans (CreateDecl.run_withCreatedOp hhead) (ih htail)
    | @applyNative Inputs Outputs inputBundle outputBundle inputs rewrite outputs =>
      simp only [CreateProg.runDecls, Option.bind_eq_bind] at hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨inputValues, _, hrun⟩ := hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨outputValues, _, hrun⟩ := hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨bound, _, htail⟩ := hrun
      exact ih htail

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
    | operation opCode operands resultTypes properties opHandle results =>
      simp only [CreateProg.runDecls, Option.bind_eq_bind] at hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨createdHead, hhead, hrun⟩ := hrun
      rcases createdHead with ⟨headCtx, headCreated, headOp⟩
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨createdTail, htail, hrun⟩ := hrun
      rcases createdTail with ⟨tailCtx, tailOps, tailCreated⟩
      simp at hrun
      obtain ⟨rfl, rfl, rfl⟩ := hrun
      exact ih (CreateDecl.run_valuesInBounds hcreated hhead) htail
    | @applyNative Inputs Outputs inputBundle outputBundle inputs rewrite outputs =>
      simp only [CreateProg.runDecls, Option.bind_eq_bind] at hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨inputValues, _, hrun⟩ := hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨outputValues, _, hrun⟩ := hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨bound, hbind, htail⟩ := hrun
      have hbound := MetadataTuple.Shape.bind_valuesInBounds outputBundle.shape
        hcreated outputs outputValues hbind
      exact ih hbound htail

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
    | operation opCode operands resultTypes properties opHandle results =>
      simp only [CreateProg.runDecls, Option.bind_eq_bind] at hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨createdHead, hhead, hrun⟩ := hrun
      rcases createdHead with ⟨headCtx, headCreated, headOp⟩
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨createdTail, htail, hrun⟩ := hrun
      rcases createdTail with ⟨tailCtx, tailOps, tailCreated⟩
      simp at hrun
      obtain ⟨rfl, rfl, rfl⟩ := hrun
      intro operation hopen
      simp only [Array.mem_append] at hopen
      rcases hopen with hopen | hopen
      · simp at hopen
        subst operation
        have hheadIn : headOp.InBounds headCtx.raw :=
          CreateDecl.run_operationInBounds hhead
        exact (CreateProg.runDecls_withCreatedOps htail).inBounds_mono
          (.operation headOp) hheadIn
      · exact ih htail operation hopen
    | @applyNative Inputs Outputs inputBundle outputBundle inputs rewrite outputs =>
      simp only [CreateProg.runDecls, Option.bind_eq_bind] at hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨inputValues, _, hrun⟩ := hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨outputValues, _, hrun⟩ := hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨bound, _, htail⟩ := hrun
      exact ih htail

private theorem CreateDecl.interpret
    {decl : CreateDecl OpCode} {matched : Assignment OpCode} {semanticMatched : SemanticAssignment}
    {created created' : Assignment OpCode}
    {semanticCreated semanticCreated' : SemanticCreateAssignment}
    {ctx ctx' finalCtx : WfIRContext OpCode} {op : OperationPtr}
    {targetState : InterpreterState finalCtx}
    (hsupported : decl.Supported)
    (hrun : decl.run created ctx = some (ctx', created', op))
    (heval : decl.eval semanticCreated = some semanticCreated')
    (hsuffix : WfIRContext.WithCreatedOps ctx' finalCtx)
    (hmatchedBounds : (Assignment.MatchValuesInBounds matched) ctx)
    (hcreatedBounds : (Assignment.ValuesInBounds created) ctx)
    (hmatched : Assignment.MatchRefines matched semanticMatched targetState)
    (hcreated : Assignment.Refines created semanticCreated targetState)
    (hmetadata : (Assignment.MetadataAgrees created) semanticCreated) :
    ∃ afterCreation,
      interpretOp op targetState
          (hsuffix.inBounds_mono (.operation op)
            (CreateDecl.run_operationInBounds hrun)) =
        .ok (afterCreation, none) ∧
      afterCreation.memory = targetState.memory ∧
      Assignment.MatchRefines matched semanticMatched afterCreation ∧
      Assignment.Refines created' semanticCreated' afterCreation := by
  cases decl with
  | operation opCode operands resultTypes propertySource opHandle results =>
    rcases hsupported with ⟨hterminator, heffects⟩
    simp only [CreateDecl.run, Option.bind_eq_bind] at hrun
    simp only [Option.bind_eq_some_iff] at hrun
    rcases hrun with
      ⟨concreteOperands, hconcreteOperands, concreteResultTypes, hconcreteResultTypes,
        properties, hconcreteProperties, returnValue, hreturnValue, returnType, hreturnType,
        _, hresultGuard, _, hhandleGuard, _, htypeGuard, hrun⟩
    have hsemanticProperties :
        propertySource.resolveSemantic semanticCreated = some properties := by
      cases propertySource with
      | literal value => simpa [CreateProperty.resolve, CreateProperty.resolveSemantic]
          using hconcreteProperties
      | handle propertyHandle =>
        simp only [CreateProperty.resolve] at hconcreteProperties
        simp only [CreateProperty.resolveSemantic]
        calc
          SemanticAssignment.getProperty semanticCreated propertyHandle =
              (Assignment.getProperty created) propertyHandle := by
            simpa [SemanticCreateAssignment.getProperty] using
              (hmetadata.2 opCode propertyHandle).symm
          _ = some properties := hconcreteProperties
    have hsemanticResultTypes :
        semanticCreated.getTypes resultTypes = some concreteResultTypes := by
      have hgetType : (Assignment.getType created) = SemanticAssignment.getType semanticCreated :=
        funext hmetadata.1
      unfold Assignment.getTypes at hconcreteResultTypes
      unfold SemanticAssignment.getTypes
      rw [← hgetType]
      exact hconcreteResultTypes
    split at hrun
    · rename_i hoper
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨createdPair, hcreate, hrun⟩ := hrun
      rcases createdPair with ⟨newCtx, newOp⟩
      simp at hrun
      rcases hrun with ⟨rfl, rfl, rfl⟩
      simp only [CreateDecl.eval] at heval
      cases hdenote : CreateDecl.denoteResults
          (.operation opCode operands resultTypes propertySource opHandle results)
          semanticCreated with
      | none => simp [hdenote] at heval
      | some sourceResults =>
        simp [hdenote] at heval
        subst semanticCreated'
        obtain ⟨sourceOperands, sourceResultTypes, sourceProperties, sourceMemory,
            hsemanticOperands, hsourceResultTypes, hsourceProperties, hsourceInterpret⟩ :=
          CreateDecl.denoteResults_operation_eq_some_iff.mp hdenote
        rw [hsemanticResultTypes] at hsourceResultTypes
        simp only [Option.some.injEq] at hsourceResultTypes
        subst sourceResultTypes
        rw [hsemanticProperties] at hsourceProperties
        simp only [Option.some.injEq] at hsourceProperties
        subst sourceProperties
        obtain ⟨targetOperands, htargetOperands, hrefineOperands⟩ :=
          hcreated.getCreateOperands hconcreteOperands hsemanticOperands
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
          exact heffects properties
        have hsourceRaw : newOp.interpret finalCtx.raw sourceOperands .empty =
            .ok (sourceResults, sourceMemory, none) := by
          simp only [OperationPtr.interpret]
          rw [hnewOpType]
          change interpretOp' opCode (newOp.getProperties! finalCtx.raw opCode)
            (newOp.getResultTypes! finalCtx.raw) sourceOperands
            (newOp.getSuccessors! finalCtx.raw) .empty = _
          rw [hnewProperties, hnewResultTypes, hnewSuccessors]
          exact hsourceInterpret
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
        have htargetMemoryEmpty : targetMemory = .empty := by
          exact (hnewPure.interpretOp'_eq_ok_implies_memory_eq htargetEmptyRaw).symm
        subst targetMemory
        have htargetRaw : newOp.interpret finalCtx.raw targetOperands targetState.memory =
            .ok (targetResults, targetState.memory, none) := by
          simp only [OperationPtr.interpret] at htargetEmptyRaw ⊢
          rw [hnewPure targetOperands targetState.memory MemoryState.empty]
          simp [htargetEmptyRaw, htargetMemoryEmpty, Interp.map]
        have htargetConforms : RuntimeValue.ArrayConforms targetResults
            (newOp.getResultTypes! finalCtx.raw) := by
          rw [hnewResultTypes]
          exact interpretOp'_results_conform_of_eq_some htargetInterpret
        obtain ⟨afterCreation, hinterpretCreated, hmemoryCreated, hsetCreated⟩ :=
          interpretOp_forward (inBounds := hnewOpIn)
            htargetOperandValues htargetRaw htargetConforms
        have hmatchedAfter : (Assignment.MatchRefines matched) semanticMatched afterCreation := by
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
        have hresultTypeSize : concreteResultTypes.size = 1 := by
          simpa [_root_.guard] using hresultGuard
        have hhandleSize : results.size = concreteResultTypes.size := by
          simpa [_root_.guard] using hhandleGuard
        have hnewNumResults :
            newOp.getNumResults! newCtx.raw = concreteResultTypes.size := by
          simpa using OperationPtr.getNumResults!_WfRewriter_createOp
            (operation := newOp) hcreate
        have hnewResultsEq : newOp.getResults! finalCtx.raw =
            newOp.getResults! newCtx.raw := by
          apply Array.ext
          · simp only [OperationPtr.getResults!.size_eq_getNumResults!]
            exact WfIRContext.WithCreatedOps.getNumResults!_eq hsuffix
              (WfRewriter.createOp_new_inBounds newOp hcreate)
          · intro i hiFinal hiNew
            rw [OperationPtr.getResults!.getElem_eq_getResult
                (by simpa using hiFinal),
              OperationPtr.getResults!.getElem_eq_getResult (by simpa using hiNew)]
        have htargetResultValues :
            (newOp.getResults! newCtx.raw).toList.mapM afterCreation.variables.getVar? =
              some targetResults.toList := by
          rw [← hnewResultsEq]
          exact VariableState.mapM_getResults_of_setResultValues
            (inBounds := hnewOpIn) hsetCreated
        have hcreatedBaseAfter : (Assignment.Refines created) semanticCreated afterCreation := by
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
            Assignment.Refines
              (Assignment.bindValues
                (Assignment.bindOp created opHandle newOp) results.toList
                (newOp.getResults! newCtx.raw).toList)
              ((semanticCreated.bindOp opHandle sourceResults).bindValues
                results.toList sourceResults.toList) afterCreation := by
          rw [hnewResultTypes] at htargetConforms
          apply (hcreatedBaseAfter.bindOp opHandle newOp sourceResults).bindValues
            results.toList (newOp.getResults! newCtx.raw).toList
            sourceResults.toList targetResults.toList
          · simp only [Array.length_toList, OperationPtr.getResults!.size_eq_getNumResults!]
            omega
          · simp only [Array.length_toList]
            unfold RuntimeValue.ArrayConforms at htargetConforms
            unfold RuntimeValue.arrayIsRefinedBy at hrefineResults
            omega
          · simp only [Array.length_toList]
            unfold RuntimeValue.ArrayConforms at htargetConforms
            omega
          · exact htargetResultValues
          · simpa using hrefineResults
        exact ⟨afterCreation, hinterpretCreated, hmemoryCreated,
          hmatchedAfter, hcreatedAfter⟩
    · simp at hrun
  | applyNative => simp [CreateDecl.run] at hrun

private theorem CreateProg.interpret_runDecls
    {decls : List (CreateDecl OpCode)} {matched : Assignment OpCode}
    {semanticMatched : SemanticAssignment}
    {ctx finalCtx : WfIRContext OpCode} {created finalCreated : Assignment OpCode}
    {semanticCreated finalSemanticCreated : SemanticCreateAssignment}
    {operations : Array OperationPtr} {targetState : InterpreterState finalCtx}
    (hsupported : ∀ decl ∈ decls, decl.Supported)
    (hrun : CreateProg.runDecls decls ctx created =
      some (finalCtx, operations, finalCreated))
    (heval : CreateProg.evalDecls decls semanticCreated =
      some finalSemanticCreated)
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
  sorry
/-
  induction decls generalizing ctx created semanticCreated finalCtx operations finalCreated
      finalSemanticCreated targetState with
  | nil =>
    simp [CreateProg.runDecls, CreateProg.evalDecls] at hrun heval
    rcases hrun with ⟨rfl, rfl, rfl⟩
    subst finalSemanticCreated
    exact ⟨targetState, by simp, rfl, hmatched, hcreated⟩
  | cons decl decls ih =>
    cases decl with
    | operation opCode operands resultTypes properties opHandle results =>
      simp only [CreateProg.runDecls, Option.bind_eq_bind] at hrun
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨createdHead, hheadRun, hrun⟩ := hrun
      rcases createdHead with ⟨headCtx, headCreated, headOp⟩
      rw [Option.bind_eq_some_iff] at hrun
      obtain ⟨createdTail, htailRun, hrun⟩ := hrun
      rcases createdTail with ⟨tailCtx, tailOps, tailCreated⟩
      simp at hrun
      rcases hrun with ⟨rfl, rfl, rfl⟩
      simp only [CreateProg.evalDecls, Option.bind_eq_bind] at heval
      rw [Option.bind_eq_some_iff] at heval
      obtain ⟨headSemanticCreated, hheadEval, htailEval⟩ := heval
      have hheadSupported :
          (CreateDecl.operation opCode operands resultTypes properties opHandle results).Supported :=
        hsupported _ (by simp)
      have htailSupported : ∀ tailDecl ∈ decls, tailDecl.Supported := by
        intro tailDecl hmem
        exact hsupported tailDecl (by simp [hmem])
      have hsuffix : WfIRContext.WithCreatedOps headCtx tailCtx :=
        CreateProg.runDecls_withCreatedOps htailRun
      obtain ⟨afterHead, hinterpretHead, hmemoryHead, hmatchedHead, hcreatedHead⟩ :=
        CreateDecl.interpret hheadSupported hheadRun hheadEval hsuffix
          hmatchedBounds hcreatedBounds hmatched hcreated hmetadata
      have hheadCtxChange : WfIRContext.WithCreatedOps ctx headCtx :=
        CreateDecl.run_withCreatedOp hheadRun
      have hmatchedBoundsHead : (Assignment.MatchValuesInBounds matched) headCtx := by
        intro handle value hget
        exact hheadCtxChange.inBounds_mono (.value value)
          (hmatchedBounds handle value hget)
      have hcreatedBoundsHead : Assignment.ValuesInBounds headCreated headCtx :=
        CreateDecl.run_valuesInBounds hcreatedBounds hheadRun
      have hmetadataHead : Assignment.MetadataAgrees headCreated headSemanticCreated := by
        sorry
      obtain ⟨afterTail, hinterpretTail, hmemoryTail, hmatchedTail, hcreatedTail⟩ :=
        ih htailSupported htailRun htailEval hmatchedBoundsHead hcreatedBoundsHead
          hmatchedHead hcreatedHead hmetadataHead
      refine ⟨afterTail, ?_, hmemoryTail.trans hmemoryHead, hmatchedTail, hcreatedTail⟩
      simpa [interpretOpList_cons, hinterpretHead] using hinterpretTail
    | @applyNative Inputs Outputs inputBundle outputBundle inputs rewrite outputs =>
      have hrunNative := hrun
      simp only [CreateProg.runDecls, Option.bind_eq_bind] at hrunNative
      rw [Option.bind_eq_some_iff] at hrunNative
      obtain ⟨inputValues, hinput, hrunNative⟩ := hrunNative
      rw [Option.bind_eq_some_iff] at hrunNative
      obtain ⟨outputValues, hrewrite, hrunNative⟩ := hrunNative
      rw [Option.bind_eq_some_iff] at hrunNative
      obtain ⟨bound, hbind, htailRun⟩ := hrunNative
      simp only [CreateProg.evalDecls, CreateDecl.eval, Option.bind_eq_bind] at heval
      have hinputSemantic :
          MetadataTuple.resolve (self := inputBundle) semanticCreated inputs = some inputValues := by
        rw [← hmetadata.resolve inputs]
        exact hinput
      simp only [Option.bind_some, hrewrite] at heval
      rw [Option.bind_eq_some_iff] at heval
      obtain ⟨semanticBound, hsemanticBind, htailEval⟩ := heval
      have htailSupported : ∀ tailDecl ∈ decls, tailDecl.Supported := by
        intro tailDecl hmem
        exact hsupported tailDecl (by simp [hmem])
      have hboundBounds := MetadataTuple.Shape.bind_valuesInBounds
        (@IsMetadataTuple.shape Outputs outputBundle) hcreatedBounds outputs outputValues hbind
      have hboundRefines := MetadataTuple.Shape.bind_refines
        (@IsMetadataTuple.shape Outputs outputBundle) hcreated outputs outputValues hbind hsemanticBind
      have hboundMetadata := hmetadata.bind outputs outputValues hbind hsemanticBind
      exact ih htailSupported htailRun htailEval hmatchedBounds hboundBounds
        hmatched hboundRefines hboundMetadata
-/

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
  intro ctx ctxDom ctxVerif root rootIn newCtx newOps newValues hpattern state stateWf
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
      cases hresolve : anyRewrite.replacement.resolve createdAssignment createdCtx.raw root with
      | none => simp [hrun, hcreate, hresolve] at hcompiled
      | some resolved =>
        simp [hrun, hcreate, hresolve] at hcompiled
        rcases hcompiled with ⟨rfl, rfl, rfl⟩
        simp [liftM, monadLift, MonadLift.monadLift] at rootInterp
        obtain ⟨hsupported, hcreateSupported, hdenotational⟩ := h
        have hcreateSupportedMem :
            ∀ decl ∈ anyRewrite.creation.decls, decl.Supported := by
          intro decl hmem
          exact hcreateSupported.of_mem hmem
        unfold CreateProg.run at hcreate
        cases hroot : anyRewrite.matcher.root? with
        | none => simp [hroot] at hdenotational
        | some rootHandle =>
          rw [hroot] at hdenotational
          have hmodels := MatchProg.models_of_run hsupported ctxDom ctxVerif rootIn hrun
            stateWf rootInterp hsourceValues
          let semanticMatched :=
            SemanticAssignment.ofConcrete assignment state root sourceValues
          have hsemanticRefinement := hdenotational semanticMatched hmodels
          obtain ⟨hnumResults', hreplacement, hnotResult'⟩ :=
            Replacement.resolve_eq_some hresolve
          obtain ⟨rootOpCode, rootOperands, rootReturnTypes, rootProperty,
              rootPropertyHandle, hrootMem⟩ :=
            MatchProg.root_mem_of_root?_eq_some hroot
          have hrootSupported := MatchProg.supported_root_of_run hsupported hrootMem hrun
          have hrooted := MatchProg.rooted_of_run ctxDom rootIn hsupported.1 hrun
          have hrootOccurs := (MatchProg.matchDecls_postconditions hrun).2
            (.root rootOpCode rootOperands rootReturnTypes rootProperty rootPropertyHandle
              rootHandle) hrootMem
          have hrootOperationMem := hsupported.2.1 rootOpCode rootOperands rootReturnTypes
            rootProperty rootPropertyHandle rootHandle hrootMem
          have hrootPure := MatchProg.supported_operation_of_run hsupported hrootOperationMem
            hrun hrootOccurs.root_getOp
          have hsemanticRoot := SemanticAssignment.ofConcrete_getOp_root
            (state := state) (rootValues := sourceValues) hrootOccurs.root_getOp
          change semanticMatched.getOp rootHandle = some sourceValues at hsemanticRoot
          unfold CreateProg.denote at hsemanticRefinement
          cases heval : CreateProg.evalDecls anyRewrite.creation.decls semanticMatched with
          | none => sorry
          | some semanticCreated =>
            rcases stateRefinement with ⟨memoryRefinement, valueRefinement⟩
            have hctxCreated : WfIRContext.WithCreatedOps ctx createdCtx :=
              CreateProg.runDecls_withCreatedOps hcreate
            have hrootInCreated : root.InBounds createdCtx.raw :=
              hctxCreated.inBounds_mono (.operation root) rootIn
            have hmatchedRefines : Assignment.MatchRefines assignment semanticMatched
                targetState := by
              intro handle value sourceRuntime hconcrete hsemantic
              dsimp [semanticMatched] at hsemantic
              obtain ⟨sourceValue, hgetValue, hRuntime⟩ :=
                SemanticAssignment.ofConcrete_getValue_eq_some hsemantic
              rw [hconcrete] at hgetValue
              simp only [Option.some.injEq] at hgetValue
              subst sourceValue
              exact hrooted.exists_target_value ctxDom hconcrete hRuntime rootIn
                hrootInCreated valueRefinement targetStateDom
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
                hrooted.valuesInBounds hcreatedBounds hmatchedRefines hcreatedRefines hmetadata
            obtain ⟨hRootMemory, hRootCf⟩ :=
              pureOperation_interpret_memory_cf rootIn hrootPure hrootSupported rootInterp
            subst rootCf
            cases hsemanticReplacement :
                semanticCreated.getValues anyRewrite.replacement with
            | none =>
              simp [heval, Replacement.refinesRoot, hsemanticRoot,
                hsemanticReplacement] at hsemanticRefinement
            | some sourceReplacements =>
              have hSourceRefinement : sourceValues ⊒ sourceReplacements := by
                simpa [heval, Replacement.refinesRoot, hsemanticRoot,
                  hsemanticReplacement] using hsemanticRefinement
              have hreplacementConcrete :
                  Assignment.getValues createdAssignment anyRewrite.replacement =
                    some resolved := by
                simpa [Replacement.resolveValues] using hreplacement
              obtain ⟨targetReplacements, htargetReplacements,
                  hReplacementRefinement⟩ :=
                hcreatedAfter.getValues hreplacementConcrete hsemanticReplacement
              refine ⟨afterCreation, hinterpretCreated,
                (hRootMemory.symm.trans memoryRefinement).trans hmemoryCreated.symm, ?_⟩
              exact ⟨targetReplacements, htargetReplacements,
                RuntimeValue.arrayIsRefinedBy_trans hSourceRefinement hReplacementRefinement⟩

end

end Veir.Puddle
