module

public import Veir.PatternRewriter.Puddle.Validity

import Veir.Data.Refinement
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

private def SemanticAssignment.normalizeSlot
    (slot : Option (Option SemanticBinding)) : Option (Option SemanticBinding) :=
  match slot with
  | some none => none
  | slot => slot

private theorem SemanticAssignment.normalizeSlot_getElem?_bind_of_ne
    (assignment : SemanticAssignment) (bound query : Nat)
    (binding : SemanticBinding) (hne : query ≠ bound) :
    normalizeSlot (assignment.bind bound binding)[query]? =
      normalizeSlot assignment[query]? := by
  unfold SemanticAssignment.bind
  split
  · rename_i hin
    rw [Array.getElem?_set]
    split <;> simp_all
  · rename_i hout
    simp only [Array.getElem?_append, Array.size_replicate, Array.size_append]
    split
    · split
      · rfl
      · rename_i hmiddle hquery
        have ha : assignment[query]? = none := Array.getElem?_eq_none (by omega)
        rw [ha, Array.getElem?_replicate]
        have : query - assignment.size < bound - assignment.size := by omega
        simp [this, normalizeSlot]
    · rename_i hquery
      simp only [Array.getElem?_singleton]
      split
      · omega
      · have ha : assignment[query]? = none := Array.getElem?_eq_none (by omega)
        rw [ha]

private theorem SemanticAssignment.normalizeSlot_getElem?_bind_self
    (assignment : SemanticAssignment) (id : Nat) (binding : SemanticBinding) :
    normalizeSlot (assignment.bind id binding)[id]? = some (some binding) := by
  unfold SemanticAssignment.bind
  split
  · simp [normalizeSlot]
  · rename_i hout
    simp only [Array.getElem?_append, Array.size_append, Array.size_replicate]
    split
    · omega
    · have heq : id - (assignment.size + (id - assignment.size)) = 0 := by omega
      rw [heq]
      rfl

private def SemanticAssignment.readValueSlot :
    Option (Option SemanticBinding) → Option RuntimeValue
  | some (some (.value value)) => some value
  | _ => none

private def SemanticAssignment.readOpSlot :
    Option (Option SemanticBinding) → Option (Array RuntimeValue)
  | some (some (.op values)) => some values
  | _ => none

private def SemanticAssignment.readTypeSlot :
    Option (Option SemanticBinding) → Option TypeAttr
  | some (some (.type type)) => some type
  | _ => none

private def SemanticAssignment.readPropertySlot (opCode : OpCode) :
    Option (Option SemanticBinding) → Option (propertiesOf opCode)
  | some (some (.property actualOpCode value)) =>
      if h : actualOpCode = opCode then some (h ▸ value) else none
  | _ => none

private theorem SemanticAssignment.readValueSlot_normalize (slot) :
    readValueSlot (normalizeSlot slot) = readValueSlot slot := by
  cases slot with
  | none => rfl
  | some slot => cases slot with
    | none => rfl
    | some binding => cases binding <;> rfl

private theorem SemanticAssignment.readOpSlot_normalize (slot) :
    readOpSlot (normalizeSlot slot) = readOpSlot slot := by
  cases slot with
  | none => rfl
  | some slot => cases slot with
    | none => rfl
    | some binding => cases binding <;> rfl

private theorem SemanticAssignment.readTypeSlot_normalize (slot) :
    readTypeSlot (normalizeSlot slot) = readTypeSlot slot := by
  cases slot with
  | none => rfl
  | some slot => cases slot with
    | none => rfl
    | some binding => cases binding <;> rfl

private theorem SemanticAssignment.readPropertySlot_normalize (opCode) (slot) :
    readPropertySlot opCode (normalizeSlot slot) = readPropertySlot opCode slot := by
  cases slot with
  | none => rfl
  | some slot => cases slot with
    | none => rfl
    | some binding => cases binding <;> rfl

@[simp] theorem SemanticAssignment.getValue_bind_of_ne
    (assignment : SemanticAssignment) (bound : Nat) (binding : SemanticBinding)
    (query : Handle OpCode .value) (hne : query.id ≠ bound) :
    (assignment.bind bound binding).getValue query = assignment.getValue query := by
  change readValueSlot (assignment.bind bound binding)[query.id]? =
    readValueSlot assignment[query.id]?
  rw [← readValueSlot_normalize,
    normalizeSlot_getElem?_bind_of_ne assignment bound query.id binding hne,
    readValueSlot_normalize]

@[simp] theorem SemanticAssignment.getOp_bind_of_ne
    (assignment : SemanticAssignment) (bound : Nat) (binding : SemanticBinding)
    (query : Handle OpCode .op) (hne : query.id ≠ bound) :
    (assignment.bind bound binding).getOp query = assignment.getOp query := by
  change readOpSlot (assignment.bind bound binding)[query.id]? = readOpSlot assignment[query.id]?
  rw [← readOpSlot_normalize,
    normalizeSlot_getElem?_bind_of_ne assignment bound query.id binding hne,
    readOpSlot_normalize]

@[simp] theorem SemanticAssignment.getType_bind_of_ne
    (assignment : SemanticAssignment) (bound : Nat) (binding : SemanticBinding)
    (query : Handle OpCode .type) (hne : query.id ≠ bound) :
    (assignment.bind bound binding).getType query = assignment.getType query := by
  change readTypeSlot (assignment.bind bound binding)[query.id]? =
    readTypeSlot assignment[query.id]?
  rw [← readTypeSlot_normalize,
    normalizeSlot_getElem?_bind_of_ne assignment bound query.id binding hne,
    readTypeSlot_normalize]

@[simp] theorem SemanticAssignment.getProperty_bind_of_ne
    (assignment : SemanticAssignment) (bound : Nat) (binding : SemanticBinding)
    (query : Handle OpCode (.prop opCode)) (hne : query.id ≠ bound) :
    (assignment.bind bound binding).getProperty query = assignment.getProperty query := by
  change readPropertySlot opCode (assignment.bind bound binding)[query.id]? =
    readPropertySlot opCode assignment[query.id]?
  rw [← readPropertySlot_normalize,
    normalizeSlot_getElem?_bind_of_ne assignment bound query.id binding hne,
    readPropertySlot_normalize]

@[simp] theorem SemanticAssignment.getValue_bindValue_self
    (assignment : SemanticAssignment) (handle : Handle OpCode .value) (value : RuntimeValue) :
    (assignment.bindValue handle value).getValue handle = some value := by
  change readValueSlot (assignment.bind handle.id (.value value))[handle.id]? = some value
  rw [← readValueSlot_normalize, normalizeSlot_getElem?_bind_self]
  rfl

@[simp] theorem SemanticAssignment.getValue_bind_value_self
    (assignment : SemanticAssignment) (handle : Handle OpCode .value) (value : RuntimeValue) :
    (assignment.bind handle.id (.value value)).getValue handle = some value := by
  change readValueSlot (assignment.bind handle.id (.value value))[handle.id]? = some value
  rw [← readValueSlot_normalize, normalizeSlot_getElem?_bind_self]
  rfl

theorem SemanticAssignment.getValue_bind_value_of_eq
    (assignment : SemanticAssignment) (bound query : Handle OpCode .value)
    (value : RuntimeValue) (heq : query.id = bound.id) :
    (assignment.bind bound.id (.value value)).getValue query = some value := by
  rcases bound with ⟨bound⟩
  rcases query with ⟨query⟩
  simp only at heq ⊢
  subst query
  exact getValue_bind_value_self assignment ⟨bound⟩ value

theorem SemanticAssignment.getValue_bind_value_id
    (assignment : SemanticAssignment) (id : Nat) (value : RuntimeValue) :
    (assignment.bind id (.value value)).getValue ⟨id⟩ = some value :=
  getValue_bind_value_self assignment ⟨id⟩ value

theorem SemanticAssignment.getValue_bindValues_singleton
    (assignment : SemanticAssignment) (handle : Handle OpCode .value) (value : RuntimeValue) :
    (assignment.bindValues [handle] [value]).getValue handle = some value := by
  change (assignment.bind handle.id (.value value)).getValue handle = some value
  exact getValue_bind_value_self assignment handle value

@[simp] theorem SemanticAssignment.getOp_bindOp_self
    (assignment : SemanticAssignment) (handle : Handle OpCode .op)
    (values : Array RuntimeValue) :
    (assignment.bindOp handle values).getOp handle = some values := by
  change readOpSlot (assignment.bind handle.id (.op values))[handle.id]? = some values
  rw [← readOpSlot_normalize, normalizeSlot_getElem?_bind_self]
  rfl

@[simp] theorem SemanticAssignment.getOp_bind_op_self
    (assignment : SemanticAssignment) (handle : Handle OpCode .op)
    (values : Array RuntimeValue) :
    (assignment.bind handle.id (.op values)).getOp handle = some values := by
  change readOpSlot (assignment.bind handle.id (.op values))[handle.id]? = some values
  rw [← readOpSlot_normalize, normalizeSlot_getElem?_bind_self]
  rfl

theorem SemanticAssignment.getOp_bind_op_of_eq
    (assignment : SemanticAssignment) (bound query : Handle OpCode .op)
    (values : Array RuntimeValue) (heq : query.id = bound.id) :
    (assignment.bind bound.id (.op values)).getOp query = some values := by
  rcases bound with ⟨bound⟩
  rcases query with ⟨query⟩
  simp only at heq ⊢
  subst query
  exact getOp_bind_op_self assignment ⟨bound⟩ values

theorem SemanticAssignment.getOp_bind_op_id
    (assignment : SemanticAssignment) (id : Nat) (values : Array RuntimeValue) :
    (assignment.bind id (.op values)).getOp ⟨id⟩ = some values :=
  getOp_bind_op_self assignment ⟨id⟩ values

@[simp] theorem SemanticAssignment.getType_bindType_self
    (assignment : SemanticAssignment) (handle : Handle OpCode .type) (type : TypeAttr) :
    (assignment.bindType handle type).getType handle = some type := by
  change readTypeSlot (assignment.bind handle.id (.type type))[handle.id]? = some type
  rw [← readTypeSlot_normalize, normalizeSlot_getElem?_bind_self]
  rfl

@[simp] theorem SemanticAssignment.getType_bind_type_self
    (assignment : SemanticAssignment) (handle : Handle OpCode .type) (type : TypeAttr) :
    (assignment.bind handle.id (.type type)).getType handle = some type := by
  change readTypeSlot (assignment.bind handle.id (.type type))[handle.id]? = some type
  rw [← readTypeSlot_normalize, normalizeSlot_getElem?_bind_self]
  rfl

theorem SemanticAssignment.getType_bind_type_of_eq
    (assignment : SemanticAssignment) (bound query : Handle OpCode .type)
    (type : TypeAttr) (heq : query.id = bound.id) :
    (assignment.bind bound.id (.type type)).getType query = some type := by
  rcases bound with ⟨bound⟩
  rcases query with ⟨query⟩
  simp only at heq ⊢
  subst query
  exact getType_bind_type_self assignment ⟨bound⟩ type

theorem SemanticAssignment.getType_bind_type_id
    (assignment : SemanticAssignment) (id : Nat) (type : TypeAttr) :
    (assignment.bind id (.type type)).getType ⟨id⟩ = some type :=
  getType_bind_type_self assignment ⟨id⟩ type

@[simp] theorem SemanticAssignment.getProperty_bindProperty_self
    (assignment : SemanticAssignment) (handle : Handle OpCode (.prop opCode))
    (value : propertiesOf opCode) :
    (assignment.bindProperty handle value).getProperty handle = some value := by
  change readPropertySlot opCode
    (assignment.bind handle.id (.property opCode value))[handle.id]? = some value
  rw [← readPropertySlot_normalize, normalizeSlot_getElem?_bind_self]
  simp [readPropertySlot]

@[simp] theorem SemanticAssignment.getProperty_bind_property_self
    (assignment : SemanticAssignment) (handle : Handle OpCode (.prop opCode))
    (value : propertiesOf opCode) :
    (assignment.bind handle.id (.property opCode value)).getProperty handle = some value := by
  change readPropertySlot opCode
    (assignment.bind handle.id (.property opCode value))[handle.id]? = some value
  rw [← readPropertySlot_normalize, normalizeSlot_getElem?_bind_self]
  simp [readPropertySlot]

theorem SemanticAssignment.getProperty_bind_property_of_eq
    (assignment : SemanticAssignment)
    (bound query : Handle OpCode (.prop opCode)) (value : propertiesOf opCode)
    (heq : query.id = bound.id) :
    (assignment.bind bound.id (.property opCode value)).getProperty query = some value := by
  rcases bound with ⟨bound⟩
  rcases query with ⟨query⟩
  simp only at heq ⊢
  subst query
  exact getProperty_bind_property_self assignment ⟨bound⟩ value

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
@[simp 2000]
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

@[simp 3000]
theorem TypeMatcher.accepts_integerType (matcher : IntegerType → Bool) (type : TypeAttr) :
    ((type.cast? IntegerType).map matcher).getD false = true ↔
      ∃ intType, type = Attribute.asType (.integerType intType) ∧ matcher intType = true := by
  simpa only [Coe.coe, IsTypeAttr.toCoe, instIsTypeAttrIntegerType] using
    (@TypeMatcher.accepts_type IntegerType instIsTypeAttrIntegerType matcher type)

@[simp 3000]
theorem TypeMatcher.accepts_floatType (matcher : FloatType → Bool) (type : TypeAttr) :
    ((type.cast? FloatType).map matcher).getD false = true ↔
      ∃ floatType, type = Attribute.asType (.floatType floatType) ∧ matcher floatType = true := by
  simpa only [Coe.coe, IsTypeAttr.toCoe, instIsTypeAttrFloatType] using
    (@TypeMatcher.accepts_type FloatType instIsTypeAttrFloatType matcher type)

@[simp 3000]
theorem TypeMatcher.accepts_byteType (matcher : LLVM.ByteType → Bool) (type : TypeAttr) :
    ((type.cast? LLVM.ByteType).map matcher).getD false = true ↔
      ∃ byteType, type = Attribute.asType (.byteType byteType) ∧ matcher byteType = true := by
  simpa only [Coe.coe, IsTypeAttr.toCoe, instIsTypeAttrByteType] using
    (@TypeMatcher.accepts_type LLVM.ByteType instIsTypeAttrByteType matcher type)

@[simp 3000]
theorem TypeMatcher.accepts_modArithType (matcher : ModArithType → Bool) (type : TypeAttr) :
    ((type.cast? ModArithType).map matcher).getD false = true ↔
      ∃ modType, type = Attribute.asType (.modArithType modType) ∧ matcher modType = true := by
  simpa only [Coe.coe, IsTypeAttr.toCoe, instIsTypeAttrModArithType] using
    (@TypeMatcher.accepts_type ModArithType instIsTypeAttrModArithType matcher type)

@[simp 3000]
theorem TypeMatcher.accepts_registerType (matcher : RegisterType → Bool) (type : TypeAttr) :
    ((type.cast? RegisterType).map matcher).getD false = true ↔
      ∃ registerType, type = Attribute.asType (.registerType registerType) ∧
        matcher registerType = true := by
  simpa only [Coe.coe, IsTypeAttr.toCoe, instIsTypeAttrRegisterType] using
    (@TypeMatcher.accepts_type RegisterType instIsTypeAttrRegisterType matcher type)

@[simp 3000]
theorem TypeMatcher.accepts_pointerType (matcher : LLVM.PointerType → Bool) (type : TypeAttr) :
    ((type.cast? LLVM.PointerType).map matcher).getD false = true ↔
      ∃ pointerType, type = Attribute.asType (.llvmPointerType pointerType) ∧
        matcher pointerType = true := by
  simpa only [Coe.coe, IsTypeAttr.toCoe, instIsTypeAttrPointerType] using
    (@TypeMatcher.accepts_type LLVM.PointerType instIsTypeAttrPointerType matcher type)

/-! Pointwise conformance equations turn model witnesses back into the typed runtime values exposed
by the author-facing validity obligation. -/

@[simp 2000]
theorem RuntimeValue.conforms_integerType_iff (runtimeValue : RuntimeValue)
    (intType : IntegerType) :
    runtimeValue.Conforms (intType : TypeAttr) ↔
      ∃ value, runtimeValue = .int intType.bitwidth value := by
  constructor
  · exact RuntimeValue.Conforms.integerType
  · rintro ⟨value, rfl⟩
    change intType.bitwidth = intType.bitwidth
    rfl

@[simp 2000]
theorem RuntimeValue.conforms_floatType_iff (runtimeValue : RuntimeValue)
    (floatType : FloatType) :
    runtimeValue.Conforms (floatType : TypeAttr) ↔
      ∃ value, runtimeValue = .float floatType.bitwidth value := by
  constructor
  · exact RuntimeValue.Conforms.floatType
  · rintro ⟨value, rfl⟩
    change floatType.bitwidth = floatType.bitwidth
    rfl

@[simp 2000]
theorem RuntimeValue.conforms_byteType_iff (runtimeValue : RuntimeValue)
    (byteType : LLVM.ByteType) :
    runtimeValue.Conforms (byteType : TypeAttr) ↔
      ∃ value, runtimeValue = .byte byteType.bitwidth value := by
  constructor
  · exact RuntimeValue.Conforms.byteType
  · rintro ⟨value, rfl⟩
    change byteType.bitwidth = byteType.bitwidth
    rfl

@[simp 2000]
theorem RuntimeValue.conforms_modArithType_iff (runtimeValue : RuntimeValue)
    (modType : ModArithType) :
    runtimeValue.Conforms (modType : TypeAttr) ↔
      ∃ value, runtimeValue = .int modType.modulus.type.bitwidth value := by
  constructor
  · exact RuntimeValue.Conforms.modArithType
  · rintro ⟨value, rfl⟩
    change modType.modulus.type.bitwidth = modType.modulus.type.bitwidth
    rfl

@[simp 2000]
theorem RuntimeValue.conforms_registerType_iff (runtimeValue : RuntimeValue)
    (registerType : RegisterType) :
    runtimeValue.Conforms (registerType : TypeAttr) ↔
      ∃ value, runtimeValue = .reg value := by
  constructor
  · exact RuntimeValue.Conforms.registerType
  · rintro ⟨value, rfl⟩
    change True
    trivial

@[simp 2000]
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
theorem HandleContext.require_eq_some_iff
    {defined final : HandleContext} {kind : HandleType OpCode}
    {handle : Handle OpCode kind} :
    defined.require handle = some final ↔
      (defined.lookup handle.id = some kind ∧ handle.id ∉ defined.unavailable) ∧
        defined = final := by
  unfold HandleContext.require
  split <;> simp_all

@[simp]
theorem HandleContext.requireMany_eq_some_iff
    {defined final : HandleContext} {used : List (Handle OpCode kind)} :
    defined.requireMany used = some final ↔
      (∀ handle ∈ used,
        defined.lookup handle.id = some kind ∧ handle.id ∉ defined.unavailable) ∧
        defined = final := by
  induction used generalizing final with
  | nil => simp [HandleContext.requireMany]
  | cons handle used ih =>
    constructor
    · intro h
      change (defined.require handle).bind (fun handles => handles.requireMany used) =
        some final at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨afterHead, hhead, htail⟩ := h
      obtain ⟨hheadAvailable, hsame⟩ := HandleContext.require_eq_some_iff.mp hhead
      subst afterHead
      obtain ⟨hrest, hsame⟩ := ih.mp htail
      exact ⟨by
        intro item hmem
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact hheadAvailable
        · exact hrest item hmem,
        hsame⟩
    · rintro ⟨hall, hsame⟩
      subst final
      have hhead := hall handle (by simp)
      have hrest : ∀ item ∈ used,
          defined.lookup item.id = some kind ∧ item.id ∉ defined.unavailable := by
        intro item hmem
        exact hall item (by simp [hmem])
      change (defined.require handle).bind (fun handles => handles.requireMany used) =
        some defined
      rw [Option.bind_eq_some_iff]
      exact ⟨defined, HandleContext.require_eq_some_iff.mpr ⟨hhead, rfl⟩,
        ih.mpr ⟨hrest, rfl⟩⟩

theorem MetadataTuple.Shape.require_eq_some_imp_eq
    {Handles : Type} (shape : MetadataTuple.Shape OpCode Handles)
    {defined final : HandleContext} {handles : Handles}
    (hrequire : shape.require defined handles = some final) :
    final = defined := by
  induction shape generalizing defined final with
  | unit => simpa [MetadataTuple.Shape.require] using hrequire.symm
  | atom metadataAtom =>
    cases metadataAtom <;>
      exact (HandleContext.require_eq_some_iff.mp hrequire).2.symm
  | cons head tail ih =>
    cases head <;>
      simp only [MetadataTuple.Shape.require, Option.bind_eq_bind] at hrequire <;>
      rw [Option.bind_eq_some_iff] at hrequire <;>
      obtain ⟨afterHead, hhead, htail⟩ := hrequire <;>
      have hsame : afterHead = defined :=
        (HandleContext.require_eq_some_iff.mp hhead).2.symm <;>
      subst afterHead <;>
      exact ih htail

theorem Pattern.StructurallyWellFormed.exists_checkStructure
    {rule : Pattern OpCode} (h : rule.StructurallyWellFormed) :
    ∃ defined, rule.checkStructure = some defined := by
  exact Option.isSome_iff_exists.mp h

theorem Pattern.StructurallyWellFormed.exists_phase_checks
    {rule : Pattern OpCode} (h : rule.StructurallyWellFormed) :
    ∃ matched created final,
      rule.matcher.collectBindings = some matched ∧
      rule.creation.checkBindings matched = some created ∧
      rule.replacement.checkBindings created = some final := by
  obtain ⟨final, hfinal⟩ := h.exists_checkStructure
  unfold Pattern.checkStructure at hfinal
  change rule.matcher.collectBindings.bind (fun matched =>
    (rule.creation.checkBindings matched).bind fun created =>
      rule.replacement.checkBindings created) = some final at hfinal
  rw [Option.bind_eq_some_iff] at hfinal
  obtain ⟨matched, hmatched, hfinal⟩ := hfinal
  rw [Option.bind_eq_some_iff] at hfinal
  obtain ⟨created, hcreated, hreplacement⟩ := hfinal
  exact ⟨matched, created, final, hmatched, hcreated, hreplacement⟩

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

macro "puddle_simp" "[" rule:ident "]" : tactic =>
  `(tactic| (
    constructor
    · constructor
      · unfold $rule
        puddle_unfold_rule_matcher $rule
        simp [MatchProg.Supported, MatchDecl.Supported, SupportedOpCode,
          Pattern.Builder, MatchProg.build, MatchProg.type, MatchProg.value,
          MatchProg.operation, MatchProg.root, MatchProg.guard, bind, pure]
        all_goals subst_vars <;> try simp_all
        all_goals try grind
        all_goals try (constructor <;> intros <;> rfl)
      · unfold $rule
        simp [CreateProg.Supported, CreateDecl.Supported,
          Pattern.Builder, CreateProg.empty, CreateProg.build, CreateProg.property,
          CreateProg.operation,
          CreateProg.applyNative,
          bind, pure]
        all_goals try (constructor <;> intros <;> rfl)
        all_goals native_decide
    · unfold $rule
      puddle_unfold_rule_matcher $rule
      simp [MatchProg.ConstrainsRoot,
        Pattern.Builder, MatchProg.build, MatchProg.type, MatchProg.value,
        MatchProg.operation, MatchProg.root, MatchProg.guard,
        bind, pure]
      all_goals subst_vars <;> try simp_all
      all_goals try grind
    · unfold $rule
      native_decide
    intro assignment hmodels
    unfold $rule at hmodels ⊢
    puddle_unfold_rule_matcher $rule
    simp (config := { maxSteps := 300000 })
      [MatchProg.Models, MatchProg.rootHandle,
      MatchDecl.Models, InterpretsTo,
      Pattern.Builder, MatchProg.build, MatchProg.type, MatchProg.value,
      MatchProg.operation, MatchProg.root, MatchProg.guard,
      CreateProg.empty, CreateProg.build, CreateProg.property, CreateProg.operation,
      CreateProg.applyNative,
      CreateProg.denote, CreateProg.evalDecls, CreateDecl.eval, CreateDecl.evalResults,
      SemanticAssignment.bindOp,
      SemanticAssignment.bindValue, SemanticAssignment.bindType,
      SemanticAssignment.bindProperty, SemanticAssignment.bindValues,
      SemanticAssignment.getValue_bind_of_ne,
      SemanticAssignment.getOp_bind_of_ne,
      SemanticAssignment.getType_bind_of_ne,
      SemanticAssignment.getProperty_bind_of_ne,
      SemanticAssignment.getValue_bind_value_self,
      SemanticAssignment.getOp_bind_op_self,
      SemanticAssignment.getType_bind_type_self,
      SemanticAssignment.getProperty_bind_property_self,
      SemanticAssignment.getValue_bind_value_of_eq,
      SemanticAssignment.getOp_bind_op_of_eq,
      SemanticAssignment.getType_bind_type_of_eq,
      SemanticAssignment.getProperty_bind_property_of_eq,
      SemanticAssignment.getValue_bind_value_id,
      SemanticAssignment.getOp_bind_op_id,
      SemanticAssignment.getType_bind_type_id,
      SemanticAssignment.getProperty_bind_property_id,
      SemanticAssignment.getValue_bindValues_singleton,
      Replacement.refinesRoot,
      RuntimeValue.isRefinedBy_refl, RuntimeValue.arrayIsRefinedBy_refl,
      Option.bind_eq_some_iff,
      SemanticAssignment.getValues, SemanticAssignment.getTypes,
      Array.mapM_eq_mapM_toList,
      default, instInhabitedBool.default,
      bind, pure] at hmodels ⊢
    all_goals puddle_cases_models
    all_goals subst_vars
    all_goals simp_all (config := { maxSteps := 300000 })
      [InterpretsTo, MatchProg.root, MatchProg.rootHandle,
      CreateProg.denote, CreateProg.evalDecls, CreateDecl.eval, CreateDecl.evalResults,
      SemanticAssignment.bindOp,
      SemanticAssignment.bindValue, SemanticAssignment.bindType,
      SemanticAssignment.bindProperty, SemanticAssignment.bindValues,
      SemanticAssignment.getValue_bind_of_ne,
      SemanticAssignment.getOp_bind_of_ne,
      SemanticAssignment.getType_bind_of_ne,
      SemanticAssignment.getProperty_bind_of_ne,
      SemanticAssignment.getValue_bind_value_self,
      SemanticAssignment.getOp_bind_op_self,
      SemanticAssignment.getType_bind_type_self,
      SemanticAssignment.getProperty_bind_property_self,
      SemanticAssignment.getValue_bind_value_of_eq,
      SemanticAssignment.getOp_bind_op_of_eq,
      SemanticAssignment.getType_bind_type_of_eq,
      SemanticAssignment.getProperty_bind_property_of_eq,
      SemanticAssignment.getValue_bind_value_id,
      SemanticAssignment.getOp_bind_op_id,
      SemanticAssignment.getType_bind_type_id,
      SemanticAssignment.getProperty_bind_property_id,
      SemanticAssignment.getValue_bindValues_singleton,
      Replacement.refinesRoot,
      RuntimeValue.isRefinedBy_refl, RuntimeValue.arrayIsRefinedBy_refl,
      Option.bind_eq_some_iff,
      SemanticAssignment.getValues, SemanticAssignment.getTypes,
      Array.mapM_eq_mapM_toList,
      default, instInhabitedBool.default,
      bind, pure]
    all_goals puddle_cases_models
    all_goals subst_vars
    all_goals try simp_all
    all_goals puddle_cases_models
    all_goals subst_vars
    all_goals try simp_all
    all_goals puddle_cases_models
    all_goals subst_vars
    all_goals try simp_all
    all_goals try simp_all [interpretOp', Arith.interpretOp', bind, pure]
    all_goals puddle_cases_models
    all_goals subst_vars
    all_goals try simp_all [interpretOp', Arith.interpretOp', bind, pure]
    all_goals puddle_cases_models
    all_goals subst_vars
    all_goals try exact RuntimeValue.isRefinedBy_refl _
    all_goals try simp_all [SemanticAssignment.getValue_bindValues_singleton,
      RuntimeValue.isRefinedBy]))


end

end Veir.Puddle
