module

public import Veir.PatternRewriter.Puddle.ValidityWithAssignment
public import Veir.Interpreter.EquationLemma

import Veir.Data.Refinement
import all Veir.Dialects.Cf.OpInfo
import all Veir.Dialects.LLVM.OpInfo
import all Veir.Dialects.RISCV_Cf.OpInfo
import all Veir.GlobalOpInfo
import Veir.Interpreter.Lemmas
import Veir.Interpreter.Refinement.Lemmas
import all Veir.Interpreter.Basic
import all Veir.Interpreter.EquationLemma
import all Veir.Interpreter.Refinement.Basic
import all Veir.IR.Attribute
import all Veir.IR.Basic
import all Veir.PatternRewriter.Semantics
import all Veir.Verifier.Lemmas
import Lean.Elab.Tactic.Unfold

/-! Proof support and tactics for author-facing Puddle validity obligations. -/

namespace Veir.Puddle

public section

variable {OpInfo : Type} [HasOpInfo OpInfo]

@[simp] theorem SemanticAssignment.getValue_bind_of_ne
    (assignment : SemanticAssignment) (bound : Nat) (binding : SemanticBinding)
    (query : Handle OpCode .value) (hne : query.id ≠ bound) :
    (assignment.bind bound binding).getValue query = assignment.getValue query := by
  simp_all [SemanticAssignment.getValue, SemanticAssignment.bind]

@[simp] theorem SemanticAssignment.getType_bind_of_ne
    (assignment : SemanticAssignment) (bound : Nat) (binding : SemanticBinding)
    (query : Handle OpCode .type) (hne : query.id ≠ bound) :
    (assignment.bind bound binding).getType query = assignment.getType query := by
  simp_all [SemanticAssignment.getType, SemanticAssignment.bind]

@[simp] theorem SemanticAssignment.getProperty_bind_of_ne
    (assignment : SemanticAssignment) (bound : Nat) (binding : SemanticBinding)
    (query : Handle OpCode (.prop opCode)) (hne : query.id ≠ bound) :
    (assignment.bind bound binding).getProperty query = assignment.getProperty query := by
  simp_all [SemanticAssignment.getProperty, SemanticAssignment.bind]

@[simp] theorem SemanticAssignment.getValue_bindValue_self
    (assignment : SemanticAssignment) (handle : Handle OpCode .value) (value : RuntimeValue) :
    (assignment.bindValue handle value).getValue handle = some value := by
  simp_all [SemanticAssignment.getValue, SemanticAssignment.bindValue, SemanticAssignment.bind]

@[simp] theorem SemanticAssignment.getValue_bind_value_self
    (assignment : SemanticAssignment) (handle : Handle OpCode .value) (value : RuntimeValue) :
    (assignment.bind handle.id (.value value)).getValue handle = some value := by
  simp_all [SemanticAssignment.getValue, SemanticAssignment.bind]

theorem SemanticAssignment.getValue_bind_value_of_eq
    (assignment : SemanticAssignment) (bound query : Handle OpCode .value)
    (value : RuntimeValue) (heq : query.id = bound.id) :
    (assignment.bind bound.id (.value value)).getValue query = some value := by
  simp_all [SemanticAssignment.getValue, SemanticAssignment.bind]

theorem SemanticAssignment.getValue_bind_value_id
    (assignment : SemanticAssignment) (id : Nat) (value : RuntimeValue) :
    (assignment.bind id (.value value)).getValue ⟨id⟩ = some value :=
  getValue_bind_value_self assignment ⟨id⟩ value

@[simp] theorem SemanticAssignment.getType_bindType_self
    (assignment : SemanticAssignment) (handle : Handle OpCode .type) (type : TypeAttr) :
    (assignment.bindType handle type).getType handle = some type := by
  simp_all [SemanticAssignment.getType, SemanticAssignment.bindType, SemanticAssignment.bind]

@[simp] theorem SemanticAssignment.getType_bind_type_self
    (assignment : SemanticAssignment) (handle : Handle OpCode .type) (type : TypeAttr) :
    (assignment.bind handle.id (.type type)).getType handle = some type := by
  simp_all [SemanticAssignment.getType, SemanticAssignment.bind]

theorem SemanticAssignment.getType_bind_type_of_eq
    (assignment : SemanticAssignment) (bound query : Handle OpCode .type)
    (type : TypeAttr) (heq : query.id = bound.id) :
    (assignment.bind bound.id (.type type)).getType query = some type := by
  simp_all [SemanticAssignment.getType, SemanticAssignment.bind]

theorem SemanticAssignment.getType_bind_type_id
    (assignment : SemanticAssignment) (id : Nat) (type : TypeAttr) :
    (assignment.bind id (.type type)).getType ⟨id⟩ = some type :=
  getType_bind_type_self assignment ⟨id⟩ type

@[simp] theorem SemanticAssignment.getProperty_bindProperty_self
    (assignment : SemanticAssignment) (handle : Handle OpCode (.prop opCode))
    (value : propertiesOf opCode) :
    (assignment.bindProperty handle value).getProperty handle = some value := by
  simp_all [SemanticAssignment.getProperty, SemanticAssignment.bindProperty, SemanticAssignment.bind]

@[simp] theorem SemanticAssignment.getProperty_bind_property_self
    (assignment : SemanticAssignment) (handle : Handle OpCode (.prop opCode))
    (value : propertiesOf opCode) :
    (assignment.bind handle.id (.property opCode value)).getProperty handle = some value := by
  simp_all [SemanticAssignment.getProperty, SemanticAssignment.bind]

theorem SemanticAssignment.getProperty_bind_property_of_eq
    (assignment : SemanticAssignment)
    (bound query : Handle OpCode (.prop opCode)) (value : propertiesOf opCode)
    (heq : query.id = bound.id) :
    (assignment.bind bound.id (.property opCode value)).getProperty query = some value := by
  simp_all [SemanticAssignment.getProperty, SemanticAssignment.bind]

theorem SemanticAssignment.getProperty_bind_property_id
    (assignment : SemanticAssignment) (id : Nat) (value : propertiesOf opCode) :
    (assignment.bind id (.property opCode value)).getProperty ⟨id⟩ = some value :=
  getProperty_bind_property_self assignment ⟨id⟩ value

/--
The interpreter's side-effect table is the trusted bridge between an operation being marked as
effect-free and the memory-independence property used by the equation lemma.
-/
axiom OperationPtr.Pure.of_getEffects_eq_none
    {op : OperationPtr} {ctx : IRContext OpCode}
    (h : HasOpInfo.getEffects (op.getOpType! ctx)
      (op.getProperties! ctx (op.getOpType! ctx)) == .none) :
    op.Pure ctx

/-- Non-terminating opcodes never produce a control-flow action. -/
axiom controlFlow_eq_none_of_isTerminator_eq_false
    {opCode : OpCode} {actual : propertiesOf opCode}
    {resultTypes : Array TypeAttr} {operands : Array RuntimeValue}
    {successors : Array BlockPtr} {memory memory' : MemoryState}
    {results : Array RuntimeValue} {controlFlow : Option ControlFlowAction}
    (hterminator : HasOpInfo.isTerminator opCode = false)
    (hinterpret : interpretOp' opCode actual resultTypes operands successors memory =
      .ok (results, memory', controlFlow)) :
    controlFlow = none

/-- The successor array is observationally irrelevant for non-terminating opcodes. -/
theorem interpretOp'_empty_successors_of_isTerminator_eq_false
    {opCode : OpCode} {actual : propertiesOf opCode}
    {resultTypes : Array TypeAttr} {operands : Array RuntimeValue}
    {successors : Array BlockPtr} {memory memory' : MemoryState}
    {results : Array RuntimeValue} {controlFlow : Option ControlFlowAction}
    (hterminator : HasOpInfo.isTerminator opCode = false)
    (hinterpret : interpretOp' opCode actual resultTypes operands successors memory =
      .ok (results, memory', controlFlow)) :
    interpretOp' opCode actual resultTypes operands #[] memory =
      .ok (results, memory', controlFlow) := by
  cases opCode <;> rename_i op <;> cases op <;>
    simp_all [interpretOp', HasOpInfo.isTerminator, OpCode.isTerminator,
      Llvm.isTerminator, Cf.isTerminator, Riscv_Cf.isTerminator,
      Arith.interpretOp', Felt.interpretOp', ModArith.interpretOp', Llvm.interpretOp',
      Riscv.interpretOp', Riscv_Stack.interpretOp', Rv64.interpretOp',
      Comb.interpretOp', HW.interpretOp']

/-- Successful dialect interpretation returns values conforming to the declared result types. -/
axiom interpretOp'_results_conform_of_eq_some
    {opCode : OpCode} {actual : propertiesOf opCode}
    {resultTypes : Array TypeAttr} {operands : Array RuntimeValue}
    {successors : Array BlockPtr} {memory memory' : MemoryState}
    {results : Array RuntimeValue} {controlFlow : Option ControlFlowAction}
    (hinterpret : interpretOp' opCode actual resultTypes operands successors memory =
      .ok (results, memory', controlFlow)) :
    RuntimeValue.ArrayConforms results resultTypes

theorem SupportedOpCode.pure
    {opCode : OpCode} {property : PropertyMatcher opCode}
    {op : OperationPtr} {ctx : IRContext OpCode}
    (hsupported : SupportedOpCode opCode)
    (hOpCode : op.getOpType! ctx = opCode)
    (_hproperty : property (op.getProperties! ctx opCode) = true) :
    op.Pure ctx := by
  apply OperationPtr.Pure.of_getEffects_eq_none
  subst opCode
  unfold SupportedOpCode at hsupported
  simp [hsupported.2]

/-- Pointwise counterpart of `TypeMatcher.denote_type`, used to unpack a matcher model into the
specific type accepted by a typed Puddle matcher. -/
theorem TypeMatcher.accepts_type {Attr : Type} [IsTypeAttr Attr]
    (matcher : Attr → Bool) (type : TypeAttr) :
    ((type.cast? Attr).map matcher).getD false = true ↔
      ∃ specificAttr : Attr, type = (specificAttr : TypeAttr) ∧ matcher specificAttr = true := by
  constructor
  · intro h
    cases hcast : type.cast? Attr with
    | none => simp [hcast] at h
    | some specificAttr =>
      have heq : (specificAttr : TypeAttr) = type :=
        (IsTypeAttr.cast?_eq_some_iff type specificAttr).mp hcast
      exact ⟨specificAttr, heq.symm, by simpa [hcast] using h⟩
  · rintro ⟨specificAttr, rfl, hmatcher⟩
    have hcast : ((specificAttr : TypeAttr).cast? Attr) = some specificAttr := by
      exact IsTypeAttr.cast?_of specificAttr
    simp [hcast, hmatcher]

/-! These specialized forms expose the canonical `TypeAttr` constructor. That matters to
`RuntimeValue.Conforms`: a generic `IsTypeAttr` coercion is intentionally abstract, while a closed
Puddle rule uses one of these canonical instances. -/

theorem TypeMatcher.accepts_integerType (matcher : IntegerType → Bool) (type : TypeAttr) :
    ((type.cast? IntegerType).map matcher).getD false = true ↔
      ∃ intType, type = Attribute.asType (.integerType intType) ∧ matcher intType = true := by
  simpa only [Coe.coe, IsTypeAttr.toCoe, instIsTypeAttrIntegerType] using
    (@TypeMatcher.accepts_type IntegerType instIsTypeAttrIntegerType matcher type)

theorem TypeMatcher.accepts_floatType (matcher : FloatType → Bool) (type : TypeAttr) :
    ((type.cast? FloatType).map matcher).getD false = true ↔
      ∃ floatType, type = Attribute.asType (.floatType floatType) ∧ matcher floatType = true := by
  simpa only [Coe.coe, IsTypeAttr.toCoe, instIsTypeAttrFloatType] using
    (@TypeMatcher.accepts_type FloatType instIsTypeAttrFloatType matcher type)

theorem TypeMatcher.accepts_byteType (matcher : LLVM.ByteType → Bool) (type : TypeAttr) :
    ((type.cast? LLVM.ByteType).map matcher).getD false = true ↔
      ∃ byteType, type = Attribute.asType (.byteType byteType) ∧ matcher byteType = true := by
  simpa only [Coe.coe, IsTypeAttr.toCoe, instIsTypeAttrByteType] using
    (@TypeMatcher.accepts_type LLVM.ByteType instIsTypeAttrByteType matcher type)

theorem TypeMatcher.accepts_modArithType (matcher : ModArithType → Bool) (type : TypeAttr) :
    ((type.cast? ModArithType).map matcher).getD false = true ↔
      ∃ modType, type = Attribute.asType (.modArithType modType) ∧ matcher modType = true := by
  simpa only [Coe.coe, IsTypeAttr.toCoe, instIsTypeAttrModArithType] using
    (@TypeMatcher.accepts_type ModArithType instIsTypeAttrModArithType matcher type)

theorem TypeMatcher.accepts_registerType (matcher : RegisterType → Bool) (type : TypeAttr) :
    ((type.cast? RegisterType).map matcher).getD false = true ↔
      ∃ registerType, type = Attribute.asType (.registerType registerType) ∧
        matcher registerType = true := by
  simpa only [Coe.coe, IsTypeAttr.toCoe, instIsTypeAttrRegisterType] using
    (@TypeMatcher.accepts_type RegisterType instIsTypeAttrRegisterType matcher type)

theorem TypeMatcher.accepts_pointerType (matcher : LLVM.PointerType → Bool) (type : TypeAttr) :
    ((type.cast? LLVM.PointerType).map matcher).getD false = true ↔
      ∃ pointerType, type = Attribute.asType (.llvmPointerType pointerType) ∧
        matcher pointerType = true := by
  simpa only [Coe.coe, IsTypeAttr.toCoe, instIsTypeAttrPointerType] using
    (@TypeMatcher.accepts_type LLVM.PointerType instIsTypeAttrPointerType matcher type)

/-! Pointwise conformance equations turn model witnesses back into the typed runtime values exposed
by the author-facing validity obligation. -/

theorem RuntimeValue.conforms_integerType_iff (runtimeValue : RuntimeValue)
    (intType : IntegerType) :
    runtimeValue.Conforms (intType : TypeAttr) ↔
      ∃ value, runtimeValue = .int intType.bitwidth value := by
  constructor
  · exact RuntimeValue.Conforms.integerType
  · rintro ⟨value, rfl⟩
    change intType.bitwidth = intType.bitwidth
    rfl

theorem RuntimeValue.conforms_floatType_iff (runtimeValue : RuntimeValue)
    (floatType : FloatType) :
    runtimeValue.Conforms (floatType : TypeAttr) ↔
      ∃ value, runtimeValue = .float floatType value := by
  constructor
  · exact RuntimeValue.Conforms.floatType
  · rintro ⟨value, rfl⟩
    change floatType = floatType
    rfl

theorem RuntimeValue.conforms_byteType_iff (runtimeValue : RuntimeValue)
    (byteType : LLVM.ByteType) :
    runtimeValue.Conforms (byteType : TypeAttr) ↔
      ∃ value, runtimeValue = .byte byteType.bitwidth value := by
  constructor
  · exact RuntimeValue.Conforms.byteType
  · rintro ⟨value, rfl⟩
    change byteType.bitwidth = byteType.bitwidth
    rfl

theorem RuntimeValue.conforms_modArithType_iff (runtimeValue : RuntimeValue)
    (modType : ModArithType) :
    runtimeValue.Conforms (modType : TypeAttr) ↔
      ∃ value, runtimeValue = .int modType.modulus.type.bitwidth value := by
  constructor
  · exact RuntimeValue.Conforms.modArithType
  · rintro ⟨value, rfl⟩
    change modType.modulus.type.bitwidth = modType.modulus.type.bitwidth
    rfl

theorem RuntimeValue.conforms_registerType_iff (runtimeValue : RuntimeValue)
    (registerType : RegisterType) :
    runtimeValue.Conforms (registerType : TypeAttr) ↔
      ∃ value, runtimeValue = .reg value := by
  constructor
  · exact RuntimeValue.Conforms.registerType
  · rintro ⟨value, rfl⟩
    change True
    trivial

theorem RuntimeValue.conforms_pointerType_iff (runtimeValue : RuntimeValue)
    (pointerType : LLVM.PointerType) :
    runtimeValue.Conforms (pointerType : TypeAttr) ↔
      ∃ value, runtimeValue = .addr value := by
  constructor
  · exact RuntimeValue.Conforms.llvmPointerType
  · rintro ⟨value, rfl⟩
    change True
    trivial

theorem CreateProg.Supported.of_mem
    {prog : CreateProg OpCode α} (hsupported : prog.Supported)
    {decl : CreateDecl OpCode} (hmem : decl ∈ prog.decls) : decl.Supported := by
  exact hsupported decl hmem

@[simp]
theorem HandleContext.require_eq_true_iff
    {defined : HandleContext} {kind : HandleType OpCode}
    {handle : Handle OpCode kind} :
    defined.require handle = true ↔
      defined.lookup handle.id = some kind ∧ handle.id ∉ defined.unavailable := by
  simp [HandleContext.require]

@[simp]
theorem HandleContext.requireMany_eq_true_iff
    {defined : HandleContext} {used : List (Handle OpCode kind)} :
    defined.requireMany used = true ↔
      ∀ handle ∈ used,
        defined.lookup handle.id = some kind ∧ handle.id ∉ defined.unavailable := by
  simp [HandleContext.requireMany, HandleContext.require]

/-! Canonical tuple equations used when reducing inline native declarations. -/

@[simp]
theorem MetadataTuple.resolveSemantic_unit
    (assignment : SemanticAssignment) (handles : Unit) :
    MetadataTuple.resolveSemantic assignment handles = some () := by
  rfl

@[simp]
theorem MetadataTuple.resolveSemantic_type
    (assignment : SemanticAssignment) (handle : Handle OpCode .type) :
    MetadataTuple.resolveSemantic assignment handle = assignment.getType handle := by
  rfl

@[simp]
theorem MetadataTuple.resolveSemantic_property
    (assignment : SemanticAssignment) {opCode : OpCode}
    (handle : Handle OpCode (.prop opCode)) :
    MetadataTuple.resolveSemantic assignment handle = assignment.getProperty handle := by
  rfl

@[simp]
theorem MetadataTuple.resolveSemantic_type_cons
    {Tail : Type} [IsMetadataTuple OpCode Tail]
    (assignment : SemanticAssignment) (handles : Handle OpCode .type × Tail) :
    MetadataTuple.resolveSemantic assignment handles = do
      let headValue ← assignment.getType handles.1
      let tailValues ← MetadataTuple.resolveSemantic assignment handles.2
      return (headValue, tailValues) := by
  rfl

@[simp]
theorem MetadataTuple.resolveSemantic_property_cons
    {Tail : Type} [IsMetadataTuple OpCode Tail]
    (assignment : SemanticAssignment) {opCode : OpCode}
    (handles : Handle OpCode (.prop opCode) × Tail) :
    MetadataTuple.resolveSemantic assignment handles = do
      let headValue ← assignment.getProperty handles.1
      let tailValues ← MetadataTuple.resolveSemantic assignment handles.2
      return (headValue, tailValues) := by
  rfl

@[simp]
theorem MetadataTuple.bindSemantic_unit
    (assignment : SemanticAssignment) (handles values : Unit) :
    MetadataTuple.bindSemantic assignment handles values = assignment := by
  rfl

@[simp]
theorem MetadataTuple.bindSemantic_type
    (assignment : SemanticAssignment) (handle : Handle OpCode .type) (value : TypeAttr) :
    MetadataTuple.bindSemantic assignment handle value = assignment.bindType handle value := by
  rfl

@[simp]
theorem MetadataTuple.bindSemantic_property
    (assignment : SemanticAssignment) {opCode : OpCode}
    (handle : Handle OpCode (.prop opCode)) (value : propertiesOf opCode) :
    MetadataTuple.bindSemantic assignment handle value =
      assignment.bindProperty handle value := by
  rfl

theorem Pattern.StructurallyWellFormed.exists_checkStructure
    {rule : Pattern OpCode} (h : rule.StructurallyWellFormed) :
    ∃ defined, rule.checkStructure = some defined := by
  exact Option.isSome_iff_exists.mp h

theorem Pattern.StructurallyWellFormed.exists_phase_checks
    {rule : Pattern OpCode} (h : rule.StructurallyWellFormed) :
    ∃ matched created,
      rule.matcher.collectBindings = some matched ∧
      rule.creation.checkBindings matched = some created ∧
      rule.replacement.checkBindings created = true := by
  cases hmatched : rule.matcher.collectBindings with
  | none =>
      simp [Pattern.StructurallyWellFormed, Pattern.checkStructure, hmatched] at h
  | some matched =>
      cases hcreated : rule.creation.checkBindings matched with
      | none =>
          simp [Pattern.StructurallyWellFormed, Pattern.checkStructure,
            hmatched, hcreated] at h
      | some created =>
          refine ⟨matched, created, rfl, hcreated, ?_⟩
          cases hreplacement : rule.replacement.checkBindings created with
          | false =>
              simp [Pattern.StructurallyWellFormed, Pattern.checkStructure,
                hmatched, hcreated, hreplacement, guard] at h
              change false = true at h
              contradiction
          | true => rfl

/-! `puddle_simp` unfolds pointwise matcher models into the algebraic obligation written by the
rule author. -/
private meta def tryUnfoldMatcherTarget (goal : Lean.MVarId) (matcherName : Lean.Name) :
    Lean.Meta.MetaM Lean.MVarId := do
  try
    Lean.Meta.unfoldTarget goal matcherName
  catch _ =>
    return goal

private meta def tryUnfoldMatcherLocal (goal : Lean.MVarId) (fvarId : Lean.FVarId)
    (matcherName : Lean.Name) : Lean.Meta.MetaM Lean.MVarId := do
  try
    Lean.Meta.unfoldLocalDecl goal fvarId matcherName
  catch _ =>
    return goal

open Lean Elab Tactic Meta in
/-- Unfold the matcher stored by a closed Puddle rule, if it is a named definition. -/
elab "puddle_unfold_rule_matcher" rule:term : tactic => withMainContext do
  let ruleExpr ← elabTerm rule none
  let some matcherExpr ← reduceProj? (mkProj ``Pattern 1 ruleExpr) | return
  let some matcherName := matcherExpr.getAppFn.constName? | return
  if matcherName == ``MatchProg.build then return
  let localDecls := (← getLCtx).decls.toArray
  let mut goal ← getMainGoal
  for localDecl? in localDecls do
    let some localDecl := localDecl? | continue
    goal ← tryUnfoldMatcherLocal goal localDecl.fvarId matcherName
  goal ← tryUnfoldMatcherTarget goal matcherName
  replaceMainGoal [goal]

private meta partial def casesModelFacts (goal : Lean.MVarId) : Lean.Meta.MetaM (List Lean.MVarId) :=
  goal.withContext do
    let localCtx ← Lean.getLCtx
    for localDecl? in localCtx.decls do
      let some localDecl := localDecl? | continue
      let type ← Lean.Meta.whnf localDecl.type
      if localDecl.isAuxDecl && !type.isAppOfArity ``Exists 2 then continue
      let variableEquality :=
        type.isAppOfArity ``Eq 3 &&
          (type.getAppArgs[1]!.isFVar || type.getAppArgs[2]!.isFVar)
      if type.isAppOfArity ``And 2 || type.isAppOfArity ``Or 2 ||
          type.isAppOfArity ``Exists 2 || variableEquality then
        let subgoals ← goal.cases localDecl.fvarId
        let mut result := []
        for subgoal in subgoals do
          result := result ++ (← casesModelFacts subgoal.mvarId)
        return result
    return [goal]

open Lean Elab Tactic Meta in
/-- Recursively expose conjunctions, alternatives, and witnesses supplied by pointwise matcher
models. -/
elab "puddle_cases_models" : tactic => withMainContext do
  let goal ← getMainGoal
  let goals ← casesModelFacts goal
  replaceMainGoal goals

private meta def specializeMemoryFacts (goal : Lean.MVarId) : Lean.Meta.MetaM Lean.MVarId := do
  let candidates ← goal.withContext do
    let mut candidates := #[]
    for localDecl? in (← Lean.getLCtx).decls do
      let some localDecl := localDecl? | continue
      let type ← Lean.Meta.whnf localDecl.type
      if type.isForall then
        let domain ← Lean.Meta.whnf type.bindingDomain!
        if domain.isConstOf ``MemoryState then
          candidates := candidates.push localDecl.fvarId
    return candidates
  let mut goal := goal
  for fvarId in candidates do
    goal ← goal.withContext do
      let localDecl ← fvarId.getDecl
      let type ← Lean.Meta.whnf localDecl.type
      let memory := Lean.mkConst ``MemoryState.empty
      let specializedType := type.bindingBody!.instantiate1 memory
      let specializedValue := Lean.mkApp (Lean.mkFVar fvarId) memory
      let goal ← goal.assert localDecl.userName specializedType specializedValue
      let goal ← goal.tryClear fvarId
      let (_, goal) ← goal.intro1P
      return goal
  return goal

open Lean Elab Tactic Meta in
/-- Instantiate interpreter facts at empty memory so simplification can expose their result value. -/
elab "puddle_specialize_memory" : tactic => withMainContext do
  replaceMainGoal [← specializeMemoryFacts (← getMainGoal)]

macro "puddle_simp" "[" rule:ident "]" : tactic =>
  `(tactic| (
    unfold $rule
    puddle_unfold_rule_matcher $rule
    try simp only [CreateProg.empty]
    try unfoldPuddleBuilder
    try simp
    try unfoldPuddleBuilder
    constructor
    · provePuddleSupported
    · cbv
    · native_decide
    simpPuddleSemantics
    all_goals letI : Nonempty MemoryState := ⟨.empty⟩
    all_goals intros
    all_goals try simp_all [InterpretsTo,
      TypeMatcher.accepts_integerType, RuntimeValue.conforms_integerType_iff, RuntimeValue.ArrayConforms]
    all_goals puddle_cases_models
    all_goals subst_vars
    all_goals puddle_specialize_memory
    all_goals try simp_all [interpretOp', Arith.interpretOp', bind, pure,
      RuntimeValue.conforms_integerType_iff, RuntimeValue.ArrayConforms]
    all_goals puddle_cases_models
    all_goals subst_vars
    all_goals try simp_all [interpretOp', Arith.interpretOp', bind, pure,
      RuntimeValue.conforms_integerType_iff, RuntimeValue.ArrayConforms]
    all_goals puddle_cases_models
    all_goals subst_vars
    all_goals try exact RuntimeValue.isRefinedBy_refl _
    all_goals try simp_all [RuntimeValue.isRefinedBy]
    all_goals try simp_all [and_assoc, and_left_comm, and_comm]))

end

end Veir.Puddle
