module

public import Veir.PatternRewriter.Puddle.Runner
public import Veir.PatternRewriter.Puddle.Builders
public import Veir.Interpreter.Evaluate
public import Veir.PatternRewriter.Semantics

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

/-! Denotational semantics and the author-facing validity obligation for Puddle rules. -/

namespace Veir.Puddle

public section

variable {OpInfo : Type} [HasOpInfo OpInfo]

/--
Whether a matcher property has an interpreter correspondence in the prototype.

Any single-result operation is admitted when every property value accepted by the matcher is
declared to have no memory effects.
-/
@[expose]
def PropertyMatcher.Supported {opCode : OpCode} (property : PropertyMatcher opCode)
  (_numOperands numResults : Nat) : Prop :=
  numResults = 1 ∧
    ∀ actual, property actual = true →
      HasOpInfo.getEffects opCode actual == .none

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

theorem PropertyMatcher.Supported.pure
    {opCode : OpCode} {property : PropertyMatcher opCode}
    {numOperands numResults : Nat}
    {op : OperationPtr} {ctx : IRContext OpCode}
    (hsupported : property.Supported numOperands numResults)
    (hOpCode : op.getOpType! ctx = opCode)
    (hproperty : property (op.getProperties! ctx opCode) = true) :
    op.Pure ctx := by
  apply OperationPtr.Pure.of_getEffects_eq_none
  subst opCode
  exact hsupported.2 _ hproperty

/-- Syntactic support boundary for declarations admitted by denotational validity. -/
@[expose]
def MatchDecl.Supported (decl : MatchDecl OpCode) : Prop :=
  match decl with
  | .operation _opCode operands returnTypes property _ _ results =>
    property.Supported operands.size returnTypes.size ∧
      (results.size = returnTypes.size ∨ results = #[])
  | _ => True


/-! ## Denotational validity

This interpretation is deliberately separate from `Pattern`: pattern authors only write the matcher
and replacement. The interpreter below turns those two pieces of syntax into the proposition they
must prove. -/

inductive SemanticBinding where
| op (results : Array RuntimeValue)
| value (value : RuntimeValue)
| type (type : TypeAttr)
| property (opCode : OpCode) (value : propertiesOf opCode)

abbrev SemanticAssignment := Array (Option SemanticBinding)

@[expose]
def SemanticAssignment.empty (size : Nat) : SemanticAssignment :=
  Array.replicate size none

@[expose]
def SemanticAssignment.bind (assignment : SemanticAssignment)
    (id : Nat) (binding : SemanticBinding) : SemanticAssignment :=
  assignment.setIfInBounds id (some binding)

@[expose]
def SemanticAssignment.bindOp (assignment : SemanticAssignment)
    (handle : Handle OpCode .op) (results : Array RuntimeValue) : SemanticAssignment :=
  assignment.bind handle.id (.op results)

@[expose]
def SemanticAssignment.bindValue (assignment : SemanticAssignment)
    (handle : Handle OpCode .value) (value : RuntimeValue) : SemanticAssignment :=
  assignment.bind handle.id (.value value)

@[expose]
def SemanticAssignment.bindType (assignment : SemanticAssignment)
    (handle : Handle OpCode .type) (type : TypeAttr) : SemanticAssignment :=
  assignment.bind handle.id (.type type)

@[expose]
def SemanticAssignment.bindProperty (assignment : SemanticAssignment)
    (handle : Handle OpCode (.prop opCode)) (value : propertiesOf opCode) : SemanticAssignment :=
  assignment.bind handle.id (.property opCode value)

@[expose]
def SemanticAssignment.bindValues (assignment : SemanticAssignment)
    (handles : List (Handle OpCode .value)) (values : List RuntimeValue) : SemanticAssignment :=
  match handles, values with
  | handle :: handles, value :: values =>
    (assignment.bindValue handle value).bindValues handles values
  | _, _ => assignment

@[expose]
def SemanticAssignment.getOp (assignment : SemanticAssignment)
    (handle : Handle OpCode .op) : Option (Array RuntimeValue) :=
  match assignment[handle.id]? with
  | some (some (.op results)) => some results
  | _ => none

@[expose]
def SemanticAssignment.getValue (assignment : SemanticAssignment)
    (handle : Handle OpCode .value) : Option RuntimeValue :=
  match assignment[handle.id]? with
  | some (some (.value value)) => some value
  | _ => none

@[expose]
def SemanticAssignment.getType (assignment : SemanticAssignment)
    (handle : Handle OpCode .type) : Option TypeAttr :=
  match assignment[handle.id]? with
  | some (some (.type type)) => some type
  | _ => none

@[expose]
def SemanticAssignment.getProperty (assignment : SemanticAssignment)
    (handle : Handle OpCode (.prop opCode)) : Option (propertiesOf opCode) :=
  match assignment[handle.id]? with
  | some (some (.property actualOpCode value)) =>
    if h : actualOpCode = opCode then
      some (h ▸ value)
    else none
  | _ => none

@[expose]
def SemanticAssignment.getValues (assignment : SemanticAssignment)
    (handles : Array (Handle OpCode .value)) : Option (Array RuntimeValue) :=
  handles.mapM assignment.getValue

@[expose]
def SemanticAssignment.getTypes (assignment : SemanticAssignment)
    (handles : Array (Handle OpCode .type)) : Option (Array TypeAttr) :=
  handles.mapM assignment.getType

abbrev SemanticCreateBinding := SemanticBinding
abbrev SemanticCreateAssignment := SemanticAssignment

@[expose]
def SemanticCreateAssignment.bind (assignment : SemanticCreateAssignment)
    (id : Nat) (binding : SemanticCreateBinding) : SemanticCreateAssignment :=
  if h : id < assignment.size then
    assignment.set id (some binding)
  else
    assignment ++ Array.replicate (id - assignment.size) none ++ #[some binding]

@[expose]
def SemanticCreateAssignment.bindOp (assignment : SemanticCreateAssignment)
    (handle : Handle OpCode .op) (results : Array RuntimeValue) : SemanticCreateAssignment :=
  assignment.bind handle.id (.op results)

@[expose]
def SemanticCreateAssignment.bindValue (assignment : SemanticCreateAssignment)
    (handle : Handle OpCode .value) (value : RuntimeValue) : SemanticCreateAssignment :=
  assignment.bind handle.id (.value value)

@[expose]
def SemanticCreateAssignment.bindType (assignment : SemanticCreateAssignment)
    (handle : Handle OpCode .type) (type : TypeAttr) : SemanticCreateAssignment :=
  assignment.bind handle.id (.type type)

@[expose]
def SemanticCreateAssignment.bindProperty (assignment : SemanticCreateAssignment)
    (handle : Handle OpCode (.prop opCode)) (value : propertiesOf opCode) :
    SemanticCreateAssignment :=
  assignment.bind handle.id (.property opCode value)

@[expose, simp]
def SemanticCreateAssignment.bindValues (assignment : SemanticCreateAssignment)
    (handles : List (Handle OpCode .value)) (values : List RuntimeValue) :
    SemanticCreateAssignment :=
  match handles, values with
  | handle :: handles, value :: values =>
    (assignment.bindValue handle value).bindValues handles values
  | _, _ => assignment

@[expose]
def SemanticCreateAssignment.getOp (assignment : SemanticCreateAssignment)
    (handle : Handle OpCode .op) : Option (Array RuntimeValue) :=
  match assignment[handle.id]? with
  | some (some (.op results)) => some results
  | _ => none

@[expose]
def SemanticCreateAssignment.getValue (assignment : SemanticCreateAssignment)
    (handle : Handle OpCode .value) : Option RuntimeValue :=
  match assignment[handle.id]? with
  | some (some (.value value)) => some value
  | _ => none

@[expose, simp]
def SemanticCreateAssignment.getType (assignment : SemanticCreateAssignment)
    (handle : Handle OpCode .type) : Option TypeAttr :=
  SemanticAssignment.getType assignment handle

@[expose, simp]
def SemanticCreateAssignment.getProperty (assignment : SemanticCreateAssignment)
    (handle : Handle OpCode (.prop opCode)) : Option (propertiesOf opCode) :=
  SemanticAssignment.getProperty assignment handle

@[simp]
theorem SemanticCreateAssignment.getType_bindOp_of_ne
    (assignment : SemanticCreateAssignment) (bound : Handle OpCode .op)
    (query : Handle OpCode .type) (results : Array RuntimeValue)
    (hneq : query.id ≠ bound.id) :
    (assignment.bindOp bound results).getType query = assignment.getType query := by
  simp only [SemanticCreateAssignment.bindOp]
  unfold SemanticCreateAssignment.bind
  split
  · rename_i h
    unfold SemanticCreateAssignment.getType SemanticAssignment.getType
    rw [Array.getElem?_set_ne h (Ne.symm hneq)]
  · rename_i h
    have hs : assignment.size ≤ bound.id := Nat.le_of_not_gt h
    have hsize : assignment.size + (bound.id - assignment.size) = bound.id :=
      Nat.add_sub_of_le hs
    unfold SemanticCreateAssignment.getType SemanticAssignment.getType
    simp only [Array.size_append, Array.size_replicate,
      Array.getElem?_append, Array.getElem?_replicate]
    rw [hsize]
    by_cases hquery : query.id < assignment.size
    · have hqb : query.id < bound.id := Nat.lt_of_lt_of_le hquery hs
      simp [hquery, hqb]
    · have hqs : assignment.size ≤ query.id := Nat.le_of_not_gt hquery
      by_cases hqb : query.id < bound.id
      · have hgap : query.id - assignment.size < bound.id - assignment.size :=
          Nat.sub_lt_sub_right hqs hqb
        simp [hquery, hqb, hgap]
      · have hbq : bound.id < query.id := by omega
        have hdiff : query.id - bound.id ≠ 0 := by omega
        simp [hquery, hqb, hdiff]

@[simp]
theorem SemanticCreateAssignment.getType_bindValue_of_ne
    (assignment : SemanticCreateAssignment) (bound : Handle OpCode .value)
    (query : Handle OpCode .type) (value : RuntimeValue)
    (hneq : query.id ≠ bound.id) :
    (assignment.bindValue bound value).getType query = assignment.getType query := by
  simp only [SemanticCreateAssignment.bindValue]
  unfold SemanticCreateAssignment.bind
  split
  · rename_i h
    unfold SemanticCreateAssignment.getType SemanticAssignment.getType
    rw [Array.getElem?_set_ne h (Ne.symm hneq)]
  · rename_i h
    have hs : assignment.size ≤ bound.id := Nat.le_of_not_gt h
    have hsize : assignment.size + (bound.id - assignment.size) = bound.id :=
      Nat.add_sub_of_le hs
    unfold SemanticCreateAssignment.getType SemanticAssignment.getType
    simp only [Array.size_append, Array.size_replicate,
      Array.getElem?_append, Array.getElem?_replicate]
    rw [hsize]
    by_cases hquery : query.id < assignment.size
    · have hqb : query.id < bound.id := Nat.lt_of_lt_of_le hquery hs
      simp [hquery, hqb]
    · have hqs : assignment.size ≤ query.id := Nat.le_of_not_gt hquery
      by_cases hqb : query.id < bound.id
      · have hgap : query.id - assignment.size < bound.id - assignment.size :=
          Nat.sub_lt_sub_right hqs hqb
        simp [hquery, hqb, hgap]
      · have hbq : bound.id < query.id := by omega
        have hdiff : query.id - bound.id ≠ 0 := by omega
        simp [hquery, hqb, hdiff]

@[simp]
theorem SemanticAssignment.getType_bindCreatedOp_of_ne
    (assignment : SemanticCreateAssignment) (bound : Handle OpCode .op)
    (query : Handle OpCode .type) (results : Array RuntimeValue)
    (hneq : query.id ≠ bound.id) :
    SemanticAssignment.getType (SemanticCreateAssignment.bindOp assignment bound results) query =
      SemanticAssignment.getType assignment query := by
  exact SemanticCreateAssignment.getType_bindOp_of_ne assignment bound query results hneq

@[simp]
theorem SemanticAssignment.getType_bindCreatedValue_of_ne
    (assignment : SemanticCreateAssignment) (bound : Handle OpCode .value)
    (query : Handle OpCode .type) (value : RuntimeValue)
    (hneq : query.id ≠ bound.id) :
    SemanticAssignment.getType (SemanticCreateAssignment.bindValue assignment bound value) query =
      SemanticAssignment.getType assignment query := by
  exact SemanticCreateAssignment.getType_bindValue_of_ne assignment bound query value hneq

instance : MetadataStore OpCode SemanticCreateAssignment where
  getType := SemanticCreateAssignment.getType
  getProperty := fun store {_opCode} propertyHandle =>
    SemanticCreateAssignment.getProperty store propertyHandle
  bindType := fun store typeHandle value =>
    some (SemanticCreateAssignment.bindType store typeHandle value)
  bindProperty := fun store {_opCode} propertyHandle value =>
    some (SemanticCreateAssignment.bindProperty store propertyHandle value)

/-! Keep native metadata evaluation at the public assignment API during validity simplification. -/

@[simp]
theorem MetadataStore.getType_semantic (assignment : SemanticCreateAssignment)
    (handle : Handle OpCode .type) :
    MetadataStore.getType assignment handle = assignment.getType handle := by
  rfl

@[simp]
theorem MetadataStore.getProperty_semantic (assignment : SemanticCreateAssignment)
    (handle : Handle OpCode (.prop opCode)) :
    MetadataStore.getProperty assignment handle = assignment.getProperty handle := by
  rfl

@[simp]
theorem MetadataStore.bindType_semantic (assignment : SemanticCreateAssignment)
    (handle : Handle OpCode .type) (value : TypeAttr) :
    MetadataStore.bindType assignment handle value =
      some (assignment.bindType handle value) := by
  rfl

@[simp]
theorem MetadataStore.bindProperty_semantic (assignment : SemanticCreateAssignment)
    (handle : Handle OpCode (.prop opCode)) (value : propertiesOf opCode) :
    MetadataStore.bindProperty assignment handle value =
      some (assignment.bindProperty handle value) := by
  rfl

theorem SemanticCreateAssignment.getValue_bindValue_of_eq
    (assignment : SemanticCreateAssignment) (bound query : Handle OpCode .value)
    (value : RuntimeValue) (heq : query.id = bound.id) :
    (assignment.bindValue bound value).getValue query = some value := by
  rcases bound with ⟨bound⟩
  rcases query with ⟨query⟩
  simp only at heq
  subst query
  simp only [SemanticCreateAssignment.bindValue]
  unfold SemanticCreateAssignment.bind
  split
  · rename_i h
    simp [SemanticCreateAssignment.getValue, h]
  · rename_i h
    have hs : assignment.size ≤ bound := Nat.le_of_not_gt h
    simp only [SemanticCreateAssignment.getValue, Array.getElem?_append]
    simp [hs]

theorem SemanticCreateAssignment.getValue_bindValue_of_ne
    (assignment : SemanticCreateAssignment) (bound query : Handle OpCode .value)
    (value : RuntimeValue) (hneq : query.id ≠ bound.id) :
    (assignment.bindValue bound value).getValue query = assignment.getValue query := by
  simp only [SemanticCreateAssignment.bindValue]
  unfold SemanticCreateAssignment.bind
  split
  · rename_i h
    unfold SemanticCreateAssignment.getValue
    rw [Array.getElem?_set_ne h (Ne.symm hneq)]
  · rename_i h
    have hs : assignment.size ≤ bound.id := Nat.le_of_not_gt h
    have hsize : assignment.size + (bound.id - assignment.size) = bound.id :=
      Nat.add_sub_of_le hs
    unfold SemanticCreateAssignment.getValue
    simp only [Array.size_append, Array.size_replicate,
      Array.getElem?_append, Array.getElem?_replicate]
    rw [hsize]
    by_cases hquery : query.id < assignment.size
    · have hqb : query.id < bound.id := Nat.lt_of_lt_of_le hquery hs
      simp [hquery, hqb]
    · have hqs : assignment.size ≤ query.id := Nat.le_of_not_gt hquery
      by_cases hqb : query.id < bound.id
      · have hgap : query.id - assignment.size < bound.id - assignment.size :=
          Nat.sub_lt_sub_right hqs hqb
        simp [hquery, hqb, hgap]
      · have hbq : bound.id < query.id := by omega
        have hdiff : query.id - bound.id ≠ 0 := by omega
        simp [hquery, hqb, hdiff]

theorem SemanticCreateAssignment.getValue_bindOp_of_eq
    (assignment : SemanticCreateAssignment) (bound : Handle OpCode .op) (query : Handle OpCode .value)
    (results : Array RuntimeValue) (heq : query.id = bound.id) :
    (assignment.bindOp bound results).getValue query = none := by
  simp only [SemanticCreateAssignment.bindOp]
  unfold SemanticCreateAssignment.bind
  split
  · rename_i h
    unfold SemanticCreateAssignment.getValue
    rw [Array.getElem?_set]
    simp [heq]
  · rename_i h
    have hs : assignment.size ≤ bound.id := Nat.le_of_not_gt h
    unfold SemanticCreateAssignment.getValue
    simp only [Array.getElem?_append]
    simp [hs, heq]

theorem SemanticCreateAssignment.getValue_bindOp_of_ne
    (assignment : SemanticCreateAssignment) (bound : Handle OpCode .op) (query : Handle OpCode .value)
    (results : Array RuntimeValue) (hneq : query.id ≠ bound.id) :
    (assignment.bindOp bound results).getValue query = assignment.getValue query := by
  simp only [SemanticCreateAssignment.bindOp]
  unfold SemanticCreateAssignment.bind
  split
  · rename_i h
    unfold SemanticCreateAssignment.getValue
    rw [Array.getElem?_set_ne h (Ne.symm hneq)]
  · rename_i h
    have hs : assignment.size ≤ bound.id := Nat.le_of_not_gt h
    have hsize : assignment.size + (bound.id - assignment.size) = bound.id :=
      Nat.add_sub_of_le hs
    unfold SemanticCreateAssignment.getValue
    simp only [Array.size_append, Array.size_replicate,
      Array.getElem?_append, Array.getElem?_replicate]
    rw [hsize]
    by_cases hquery : query.id < assignment.size
    · have hqb : query.id < bound.id := Nat.lt_of_lt_of_le hquery hs
      simp [hquery, hqb]
    · have hqs : assignment.size ≤ query.id := Nat.le_of_not_gt hquery
      by_cases hqb : query.id < bound.id
      · have hgap : query.id - assignment.size < bound.id - assignment.size :=
          Nat.sub_lt_sub_right hqs hqb
        simp [hquery, hqb, hgap]
      · have hbq : bound.id < query.id := by omega
        have hdiff : query.id - bound.id ≠ 0 := by omega
        simp [hquery, hqb, hdiff]

theorem SemanticCreateAssignment.getValue_bindProperty_of_ne
    (assignment : SemanticCreateAssignment) (bound : Handle OpCode (.prop opCode))
    (query : Handle OpCode .value) (value : propertiesOf opCode)
    (hneq : query.id ≠ bound.id) :
    (assignment.bindProperty bound value).getValue query = assignment.getValue query := by
  simp only [SemanticCreateAssignment.bindProperty]
  unfold SemanticCreateAssignment.bind
  split
  · rename_i h
    unfold SemanticCreateAssignment.getValue
    rw [Array.getElem?_set_ne h (Ne.symm hneq)]
  · rename_i h
    have hs : assignment.size ≤ bound.id := Nat.le_of_not_gt h
    have hsize : assignment.size + (bound.id - assignment.size) = bound.id :=
      Nat.add_sub_of_le hs
    unfold SemanticCreateAssignment.getValue
    simp only [Array.size_append, Array.size_replicate,
      Array.getElem?_append, Array.getElem?_replicate]
    rw [hsize]
    by_cases hquery : query.id < assignment.size
    · have hqb : query.id < bound.id := Nat.lt_of_lt_of_le hquery hs
      simp [hquery, hqb]
    · have hqs : assignment.size ≤ query.id := Nat.le_of_not_gt hquery
      by_cases hqb : query.id < bound.id
      · have hgap : query.id - assignment.size < bound.id - assignment.size :=
          Nat.sub_lt_sub_right hqs hqb
        simp [hquery, hqb, hgap]
      · have hbq : bound.id < query.id := by omega
        have hdiff : query.id - bound.id ≠ 0 := by omega
        simp [hquery, hqb, hdiff]

@[simp]
theorem SemanticCreateAssignment.getOp_bindProperty_of_ne
    (assignment : SemanticCreateAssignment) (bound : Handle OpCode (.prop opCode))
    (query : Handle OpCode .op) (value : propertiesOf opCode)
    (hneq : query.id ≠ bound.id) :
    (assignment.bindProperty bound value).getOp query = assignment.getOp query := by
  simp only [SemanticCreateAssignment.bindProperty]
  unfold SemanticCreateAssignment.bind
  split
  · rename_i h
    unfold SemanticCreateAssignment.getOp
    rw [Array.getElem?_set_ne h (Ne.symm hneq)]
  · rename_i h
    have hs : assignment.size ≤ bound.id := Nat.le_of_not_gt h
    have hsize : assignment.size + (bound.id - assignment.size) = bound.id :=
      Nat.add_sub_of_le hs
    unfold SemanticCreateAssignment.getOp
    simp only [Array.size_append, Array.size_replicate,
      Array.getElem?_append, Array.getElem?_replicate]
    rw [hsize]
    by_cases hquery : query.id < assignment.size
    · have hqb : query.id < bound.id := Nat.lt_of_lt_of_le hquery hs
      simp [hquery, hqb]
    · have hqs : assignment.size ≤ query.id := Nat.le_of_not_gt hquery
      by_cases hqb : query.id < bound.id
      · have hgap : query.id - assignment.size < bound.id - assignment.size :=
          Nat.sub_lt_sub_right hqs hqb
        simp [hquery, hqb, hgap]
      · have hbq : bound.id < query.id := by omega
        have hdiff : query.id - bound.id ≠ 0 := by omega
        simp [hquery, hqb, hdiff]

@[simp]
theorem SemanticCreateAssignment.getType_bindProperty_of_ne
    (assignment : SemanticCreateAssignment) (bound : Handle OpCode (.prop opCode))
    (query : Handle OpCode .type) (value : propertiesOf opCode)
    (hneq : query.id ≠ bound.id) :
    (assignment.bindProperty bound value).getType query = assignment.getType query := by
  simp only [SemanticCreateAssignment.bindProperty]
  unfold SemanticCreateAssignment.bind
  split
  · rename_i h
    unfold SemanticCreateAssignment.getType SemanticAssignment.getType
    rw [Array.getElem?_set_ne h (Ne.symm hneq)]
  · rename_i h
    have hs : assignment.size ≤ bound.id := Nat.le_of_not_gt h
    have hsize : assignment.size + (bound.id - assignment.size) = bound.id :=
      Nat.add_sub_of_le hs
    unfold SemanticCreateAssignment.getType SemanticAssignment.getType
    simp only [Array.size_append, Array.size_replicate,
      Array.getElem?_append, Array.getElem?_replicate]
    rw [hsize]
    by_cases hquery : query.id < assignment.size
    · have hqb : query.id < bound.id := Nat.lt_of_lt_of_le hquery hs
      simp [hquery, hqb]
    · have hqs : assignment.size ≤ query.id := Nat.le_of_not_gt hquery
      by_cases hqb : query.id < bound.id
      · have hgap : query.id - assignment.size < bound.id - assignment.size :=
          Nat.sub_lt_sub_right hqs hqb
        simp [hquery, hqb, hgap]
      · have hbq : bound.id < query.id := by omega
        have hdiff : query.id - bound.id ≠ 0 := by omega
        simp [hquery, hqb, hdiff]

@[simp]
theorem SemanticAssignment.getType_bindCreatedProperty_of_ne
    (assignment : SemanticCreateAssignment) (bound : Handle OpCode (.prop opCode))
    (query : Handle OpCode .type) (value : propertiesOf opCode)
    (hneq : query.id ≠ bound.id) :
    SemanticAssignment.getType
        (SemanticCreateAssignment.bindProperty assignment bound value) query =
      SemanticAssignment.getType assignment query := by
  exact SemanticCreateAssignment.getType_bindProperty_of_ne
    assignment bound query value hneq

theorem SemanticCreateAssignment.getProperty_bindProperty_of_eq
    (assignment : SemanticCreateAssignment) (bound query : Handle OpCode (.prop opCode))
    (value : propertiesOf opCode) (heq : query.id = bound.id) :
    (assignment.bindProperty bound value).getProperty query = some value := by
  rcases bound with ⟨bound⟩
  rcases query with ⟨query⟩
  simp only at heq
  subst query
  simp only [SemanticCreateAssignment.bindProperty]
  unfold SemanticCreateAssignment.bind
  split
  · rename_i h
    simp [SemanticCreateAssignment.getProperty, SemanticAssignment.getProperty, h]
  · rename_i h
    have hs : assignment.size ≤ bound := Nat.le_of_not_gt h
    simp only [SemanticCreateAssignment.getProperty, SemanticAssignment.getProperty,
      Array.getElem?_append]
    simp [hs]

theorem SemanticAssignment.getElem?_bind_of_ne
    (assignment : SemanticAssignment) (bound query : Nat)
    (binding : SemanticBinding) (hneq : query ≠ bound) :
    (assignment.bind bound binding)[query]? = assignment[query]? := by
  unfold SemanticAssignment.bind Array.setIfInBounds
  split
  · rename_i h
    rw [Array.getElem?_set_ne h (Ne.symm hneq)]
  · rfl

theorem SemanticAssignment.getElem?_bind_of_eq
    (assignment : SemanticAssignment) (id : Nat)
    (binding : SemanticBinding) (hbound : id < assignment.size) :
    (assignment.bind id binding)[id]? = some (some binding) := by
  unfold SemanticAssignment.bind Array.setIfInBounds
  simp [hbound]

@[simp] theorem SemanticAssignment.size_bind
    (assignment : SemanticAssignment) (id : Nat) (binding : SemanticBinding) :
    (assignment.bind id binding).size = assignment.size := by
  unfold SemanticAssignment.bind Array.setIfInBounds
  split <;> simp_all

@[simp] theorem SemanticAssignment.size_bindOp
    (assignment : SemanticAssignment) (handle : Handle OpCode .op) (results : Array RuntimeValue) :
    (assignment.bindOp handle results).size = assignment.size := by
  simp [SemanticAssignment.bindOp]

@[simp] theorem SemanticAssignment.size_bindValue
    (assignment : SemanticAssignment) (handle : Handle OpCode .value) (value : RuntimeValue) :
    (assignment.bindValue handle value).size = assignment.size := by
  simp [SemanticAssignment.bindValue]

@[simp] theorem SemanticAssignment.size_bindType
    (assignment : SemanticAssignment) (handle : Handle OpCode .type) (value : TypeAttr) :
    (assignment.bindType handle value).size = assignment.size := by
  simp [SemanticAssignment.bindType]

@[simp] theorem SemanticAssignment.size_bindProperty
    (assignment : SemanticAssignment) (handle : Handle OpCode (.prop opCode))
    (value : propertiesOf opCode) :
    (assignment.bindProperty handle value).size = assignment.size := by
  simp [SemanticAssignment.bindProperty]

@[simp] theorem SemanticAssignment.getValue_bindMatchedValue_of_eq
    (assignment : SemanticAssignment) (bound query : Handle OpCode .value)
    (value : RuntimeValue) (heq : query.id = bound.id)
    (hbound : bound.id < assignment.size) :
    (assignment.bindValue bound value).getValue query = some value := by
  rcases bound with ⟨bound⟩
  rcases query with ⟨query⟩
  simp only at heq hbound ⊢
  subst query
  unfold SemanticAssignment.bindValue SemanticAssignment.getValue
  rw [SemanticAssignment.getElem?_bind_of_eq assignment bound _ hbound]

@[simp] theorem SemanticAssignment.getValue_bindMatchedValue_of_ne
    (assignment : SemanticAssignment) (bound query : Handle OpCode .value)
    (value : RuntimeValue) (hneq : query.id ≠ bound.id) :
    (assignment.bindValue bound value).getValue query = assignment.getValue query := by
  unfold SemanticAssignment.bindValue SemanticAssignment.getValue
  rw [SemanticAssignment.getElem?_bind_of_ne assignment bound.id query.id _ hneq]

@[simp] theorem SemanticAssignment.getValue_bindMatchedOp_of_ne
    (assignment : SemanticAssignment) (bound : Handle OpCode .op) (query : Handle OpCode .value)
    (results : Array RuntimeValue) (hneq : query.id ≠ bound.id) :
    (assignment.bindOp bound results).getValue query = assignment.getValue query := by
  unfold SemanticAssignment.bindOp SemanticAssignment.getValue
  rw [SemanticAssignment.getElem?_bind_of_ne assignment bound.id query.id _ hneq]

@[simp] theorem SemanticAssignment.getValue_bindMatchedType_of_ne
    (assignment : SemanticAssignment) (bound : Handle OpCode .type) (query : Handle OpCode .value)
    (value : TypeAttr) (hneq : query.id ≠ bound.id) :
    (assignment.bindType bound value).getValue query = assignment.getValue query := by
  unfold SemanticAssignment.bindType SemanticAssignment.getValue
  rw [SemanticAssignment.getElem?_bind_of_ne assignment bound.id query.id _ hneq]

@[simp] theorem SemanticAssignment.getType_bindMatchedType_of_eq
    (assignment : SemanticAssignment) (bound query : Handle OpCode .type)
    (value : TypeAttr) (heq : query.id = bound.id)
    (hbound : bound.id < assignment.size) :
    (assignment.bindType bound value).getType query = some value := by
  rcases bound with ⟨bound⟩
  rcases query with ⟨query⟩
  simp only at heq hbound ⊢
  subst query
  unfold SemanticAssignment.bindType SemanticAssignment.getType
  rw [SemanticAssignment.getElem?_bind_of_eq assignment bound _ hbound]

@[simp] theorem SemanticAssignment.getType_bindMatchedValue_of_ne
    (assignment : SemanticAssignment) (bound : Handle OpCode .value) (query : Handle OpCode .type)
    (value : RuntimeValue) (hneq : query.id ≠ bound.id) :
    (assignment.bindValue bound value).getType query = assignment.getType query := by
  unfold SemanticAssignment.bindValue SemanticAssignment.getType
  rw [SemanticAssignment.getElem?_bind_of_ne assignment bound.id query.id _ hneq]

@[simp] theorem SemanticAssignment.getType_bindMatchedOp_of_ne
    (assignment : SemanticAssignment) (bound : Handle OpCode .op) (query : Handle OpCode .type)
    (results : Array RuntimeValue) (hneq : query.id ≠ bound.id) :
    (assignment.bindOp bound results).getType query = assignment.getType query := by
  unfold SemanticAssignment.bindOp SemanticAssignment.getType
  rw [SemanticAssignment.getElem?_bind_of_ne assignment bound.id query.id _ hneq]

@[simp] theorem SemanticAssignment.getOp_bindMatchedOp_of_eq
    (assignment : SemanticAssignment) (bound query : Handle OpCode .op)
    (results : Array RuntimeValue) (heq : query.id = bound.id)
    (hbound : bound.id < assignment.size) :
    (assignment.bindOp bound results).getOp query = some results := by
  rcases bound with ⟨bound⟩
  rcases query with ⟨query⟩
  simp only at heq hbound ⊢
  subst query
  unfold SemanticAssignment.bindOp SemanticAssignment.getOp
  rw [SemanticAssignment.getElem?_bind_of_eq assignment bound _ hbound]

@[simp] theorem SemanticAssignment.getProperty_bindMatchedOp_of_ne
    (assignment : SemanticAssignment) (bound : Handle OpCode .op)
    (query : Handle OpCode (.prop opCode)) (results : Array RuntimeValue)
    (hneq : query.id ≠ bound.id) :
    (assignment.bindOp bound results).getProperty query = assignment.getProperty query := by
  unfold SemanticAssignment.bindOp SemanticAssignment.getProperty
  rw [SemanticAssignment.getElem?_bind_of_ne assignment bound.id query.id _ hneq]

@[simp]
theorem SemanticAssignment.getValue_bindMatchedProperty_of_ne
    (assignment : SemanticAssignment) (bound : Handle OpCode (.prop opCode))
    (query : Handle OpCode .value) (value : propertiesOf opCode)
    (hneq : query.id ≠ bound.id) :
    (assignment.bindProperty bound value).getValue query = assignment.getValue query := by
  unfold SemanticAssignment.bindProperty SemanticAssignment.getValue
  rw [SemanticAssignment.getElem?_bind_of_ne assignment bound.id query.id _ hneq]

@[simp]
theorem SemanticAssignment.getOp_bindMatchedProperty_of_ne
    (assignment : SemanticAssignment) (bound : Handle OpCode (.prop opCode))
    (query : Handle OpCode .op) (value : propertiesOf opCode)
    (hneq : query.id ≠ bound.id) :
    (assignment.bindProperty bound value).getOp query = assignment.getOp query := by
  unfold SemanticAssignment.bindProperty SemanticAssignment.getOp
  rw [SemanticAssignment.getElem?_bind_of_ne assignment bound.id query.id _ hneq]

@[simp]
theorem SemanticAssignment.getType_bindMatchedProperty_of_ne
    (assignment : SemanticAssignment) (bound : Handle OpCode (.prop opCode))
    (query : Handle OpCode .type) (value : propertiesOf opCode)
    (hneq : query.id ≠ bound.id) :
    (assignment.bindProperty bound value).getType query = assignment.getType query := by
  unfold SemanticAssignment.bindProperty SemanticAssignment.getType
  rw [SemanticAssignment.getElem?_bind_of_ne assignment bound.id query.id _ hneq]

@[simp]
theorem SemanticAssignment.getProperty_bindMatchedProperty_of_eq
    (assignment : SemanticAssignment) (bound query : Handle OpCode (.prop opCode))
    (value : propertiesOf opCode) (heq : query.id = bound.id)
    (hbound : bound.id < assignment.size) :
    (assignment.bindProperty bound value).getProperty query = some value := by
  rcases bound with ⟨bound⟩
  rcases query with ⟨query⟩
  simp only at heq hbound ⊢
  subst query
  unfold SemanticAssignment.bindProperty SemanticAssignment.bind
  simp [SemanticAssignment.getProperty, Array.setIfInBounds, hbound]

/-!
`CreateDecl` is phrased in terms of `SemanticAssignment`, while the update lemmas above use the
creation-assignment API.  Keep these forwarding equations opaque and high-level so simplification
never expands the backing array representation.
-/

@[simp]
theorem SemanticAssignment.getValue_bindValue_of_eq
    (assignment : SemanticAssignment) (bound query : Handle OpCode .value)
    (value : RuntimeValue) (heq : query.id = bound.id) :
    SemanticAssignment.getValue (SemanticCreateAssignment.bindValue assignment bound value) query =
      some value := by
  exact SemanticCreateAssignment.getValue_bindValue_of_eq assignment bound query value heq

@[simp]
theorem SemanticAssignment.getValue_bindValue_of_ne
    (assignment : SemanticAssignment) (bound query : Handle OpCode .value)
    (value : RuntimeValue) (hneq : query.id ≠ bound.id) :
    SemanticAssignment.getValue (SemanticCreateAssignment.bindValue assignment bound value) query =
      SemanticAssignment.getValue assignment query := by
  exact SemanticCreateAssignment.getValue_bindValue_of_ne assignment bound query value hneq

@[simp]
theorem SemanticAssignment.getValue_bindOp_of_eq
    (assignment : SemanticAssignment) (bound : Handle OpCode .op) (query : Handle OpCode .value)
    (results : Array RuntimeValue) (heq : query.id = bound.id) :
    SemanticAssignment.getValue (SemanticCreateAssignment.bindOp assignment bound results) query =
      none := by
  exact SemanticCreateAssignment.getValue_bindOp_of_eq assignment bound query results heq

@[simp]
theorem SemanticAssignment.getValue_bindOp_of_ne
    (assignment : SemanticAssignment) (bound : Handle OpCode .op) (query : Handle OpCode .value)
    (results : Array RuntimeValue) (hneq : query.id ≠ bound.id) :
    SemanticAssignment.getValue (SemanticCreateAssignment.bindOp assignment bound results) query =
      SemanticAssignment.getValue assignment query := by
  exact SemanticCreateAssignment.getValue_bindOp_of_ne assignment bound query results hneq

@[simp]
theorem SemanticAssignment.getValue_bindProperty_of_ne
    (assignment : SemanticAssignment) (bound : Handle OpCode (.prop opCode))
    (query : Handle OpCode .value) (value : propertiesOf opCode)
    (hneq : query.id ≠ bound.id) :
    SemanticAssignment.getValue (SemanticCreateAssignment.bindProperty assignment bound value) query =
      SemanticAssignment.getValue assignment query := by
  exact SemanticCreateAssignment.getValue_bindProperty_of_ne assignment bound query value hneq

@[simp]
theorem SemanticAssignment.getProperty_bindProperty_of_eq
    (assignment : SemanticAssignment) (bound query : Handle OpCode (.prop opCode))
    (value : propertiesOf opCode) (heq : query.id = bound.id) :
    SemanticAssignment.getProperty
        (SemanticCreateAssignment.bindProperty assignment bound value) query = some value := by
  exact SemanticCreateAssignment.getProperty_bindProperty_of_eq assignment bound query value heq

@[expose]
def CreateOperand.getValue (operand : CreateOperand OpCode)
    (assignment : SemanticAssignment) : Option RuntimeValue :=
  SemanticAssignment.getValue assignment operand.value

@[expose]
def CreateOperand.getValues (operands : Array (CreateOperand OpCode))
    (assignment : SemanticAssignment) : Option (Array RuntimeValue) :=
  operands.mapM fun operand => operand.getValue assignment

/-- Interpreter-backed denotation used for effect-free operations without a specialized Puddle
denotation.  Successors and control flow are existential because matcher syntax records neither;
the result values are the observable part used by a rewrite. -/
@[expose]
def PropertyMatcher.Interprets (opCode : OpCode) (actual : propertiesOf opCode)
    (resultTypes : Array TypeAttr) (operands results : Array RuntimeValue) : Prop :=
  ∃ successors memory controlFlow,
    interpretOp' opCode actual resultTypes operands successors memory =
      .ok (results, memory, controlFlow)

private theorem Array.exists_eq_singleton_of_size_eq_one {values : Array α}
    (hsize : values.size = 1) : ∃ value, values = #[value] := by
  rcases values with ⟨values⟩
  simp only [List.size_toArray] at hsize
  match values, hsize with
  | [value], _ => exact ⟨value, rfl⟩

/-- A successful single-integer-result interpretation exposes exactly one typed value.

This is the normalization that lets `puddle_simp` erase the array and assignment machinery
before presenting an operation's semantic obligation to a pattern author. -/
theorem PropertyMatcher.Interprets.exists_integer_result
    (hinterpret : PropertyMatcher.Interprets opCode actual
      #[(IntegerType.mk bitwidth : TypeAttr)] operands results) :
    ∃ result : Data.LLVM.Int bitwidth, results = #[.int bitwidth result] := by
  rcases hinterpret with ⟨successors, memory, controlFlow, hinterpret⟩
  have hconforms := interpretOp'_results_conform_of_eq_some hinterpret
  have hsize : results.size = 1 := by
    simpa [RuntimeValue.ArrayConforms] using hconforms.1
  rcases Array.exists_eq_singleton_of_size_eq_one hsize with ⟨result, rfl⟩
  have hresult := hconforms.2 0 (by simp)
  simp at hresult
  rcases RuntimeValue.Conforms.integerType hresult with ⟨result, rfl⟩
  exact ⟨result, rfl⟩

/-- A successful single-result interpretation exposes one value conforming to its result type. -/
private theorem PropertyMatcher.Interprets.exists_conforming_single_result
    (hinterpret : PropertyMatcher.Interprets opCode actual #[resultType] operands results) :
    ∃ result, results = #[result] ∧ RuntimeValue.Conforms result resultType := by
  rcases hinterpret with ⟨successors, memory, controlFlow, hinterpret⟩
  have hconforms := interpretOp'_results_conform_of_eq_some hinterpret
  have hsize : results.size = 1 := by
    simpa [RuntimeValue.ArrayConforms] using hconforms.1
  rcases Array.exists_eq_singleton_of_size_eq_one hsize with ⟨result, rfl⟩
  exact ⟨result, rfl, hconforms.2 0 (by simp)⟩

theorem PropertyMatcher.Interprets.exists_float_result
    (hinterpret : PropertyMatcher.Interprets opCode actual
      #[(FloatType.mk bitwidth : TypeAttr)] operands results) :
    ∃ result : Float, results = #[.float bitwidth result] := by
  rcases hinterpret.exists_conforming_single_result with ⟨result, rfl, hresult⟩
  rcases RuntimeValue.Conforms.floatType hresult with ⟨result, rfl⟩
  exact ⟨result, rfl⟩

theorem PropertyMatcher.Interprets.exists_byte_result
    (hinterpret : PropertyMatcher.Interprets opCode actual
      #[(LLVM.ByteType.mk bitwidth : TypeAttr)] operands results) :
    ∃ result : Data.LLVM.Byte bitwidth, results = #[.byte bitwidth result] := by
  rcases hinterpret.exists_conforming_single_result with ⟨result, rfl, hresult⟩
  rcases RuntimeValue.Conforms.byteType hresult with ⟨result, rfl⟩
  exact ⟨result, rfl⟩

theorem PropertyMatcher.Interprets.exists_modArith_result
    {type : ModArithType}
    (hinterpret : PropertyMatcher.Interprets opCode actual #[(type : TypeAttr)] operands results) :
    ∃ result : Data.LLVM.Int type.modulus.type.bitwidth,
      results = #[.int type.modulus.type.bitwidth result] := by
  rcases hinterpret.exists_conforming_single_result with ⟨result, rfl, hresult⟩
  rcases RuntimeValue.Conforms.modArithType hresult with ⟨result, rfl⟩
  exact ⟨result, rfl⟩

theorem PropertyMatcher.Interprets.exists_register_result
    {type : RegisterType}
    (hinterpret : PropertyMatcher.Interprets opCode actual #[(type : TypeAttr)] operands results) :
    ∃ result : Data.RISCV.Reg, results = #[.reg result] := by
  rcases hinterpret.exists_conforming_single_result with ⟨result, rfl, hresult⟩
  rcases RuntimeValue.Conforms.registerType hresult with ⟨result, rfl⟩
  exact ⟨result, rfl⟩

theorem PropertyMatcher.Interprets.exists_pointer_result
    {type : LLVM.PointerType}
    (hinterpret : PropertyMatcher.Interprets opCode actual #[(type : TypeAttr)] operands results) :
    ∃ result : UInt64, results = #[.addr result] := by
  rcases hinterpret.exists_conforming_single_result with ⟨result, rfl, hresult⟩
  rcases RuntimeValue.Conforms.llvmPointerType hresult with ⟨result, rfl⟩
  exact ⟨result, rfl⟩

@[expose]
def PropertyMatcher.denote {opCode : OpCode} (property : PropertyMatcher opCode)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue)
    (next : propertiesOf opCode → Array RuntimeValue → Prop) : Prop :=
  ∀ actual, property actual = true →
    ∀ results, PropertyMatcher.Interprets opCode actual resultTypes operands results →
      next actual results

/-- Author-facing form of a property denotation for Puddle's single integer result. -/
theorem PropertyMatcher.denote_single_integer
    (property : PropertyMatcher opCode) (operands : Array RuntimeValue)
    (next : propertiesOf opCode → Array RuntimeValue → Prop) :
    property.denote #[(IntegerType.mk bitwidth : TypeAttr)] operands next ↔
      ∀ actual, property actual = true →
        ∀ result : Data.LLVM.Int bitwidth,
          PropertyMatcher.Interprets opCode actual
            #[(IntegerType.mk bitwidth : TypeAttr)] operands #[.int bitwidth result] →
          next actual #[.int bitwidth result] := by
  constructor
  · intro hdenote actual hproperty result hinterpret
    exact hdenote actual hproperty _ hinterpret
  · intro hdenote actual hproperty results hinterpret
    rcases hinterpret.exists_integer_result with ⟨result, rfl⟩
    exact hdenote actual hproperty result hinterpret

theorem PropertyMatcher.denote_single_float
    (property : PropertyMatcher opCode) (operands : Array RuntimeValue)
    (next : propertiesOf opCode → Array RuntimeValue → Prop) :
    property.denote #[(FloatType.mk bitwidth : TypeAttr)] operands next ↔
      ∀ actual, property actual = true → ∀ result : Float,
        PropertyMatcher.Interprets opCode actual #[(FloatType.mk bitwidth : TypeAttr)] operands
          #[.float bitwidth result] → next actual #[.float bitwidth result] := by
  constructor
  · intro h actual hp result hi; exact h actual hp _ hi
  · intro h actual hp results hi
    rcases hi.exists_float_result with ⟨result, rfl⟩
    exact h actual hp result hi

theorem PropertyMatcher.denote_single_byte
    (property : PropertyMatcher opCode) (operands : Array RuntimeValue)
    (next : propertiesOf opCode → Array RuntimeValue → Prop) :
    property.denote #[(LLVM.ByteType.mk bitwidth : TypeAttr)] operands next ↔
      ∀ actual, property actual = true → ∀ result : Data.LLVM.Byte bitwidth,
        PropertyMatcher.Interprets opCode actual #[(LLVM.ByteType.mk bitwidth : TypeAttr)] operands
          #[.byte bitwidth result] → next actual #[.byte bitwidth result] := by
  constructor
  · intro h actual hp result hi; exact h actual hp _ hi
  · intro h actual hp results hi
    rcases hi.exists_byte_result with ⟨result, rfl⟩
    exact h actual hp result hi

theorem PropertyMatcher.denote_single_modArith
    {type : ModArithType} (property : PropertyMatcher opCode) (operands : Array RuntimeValue)
    (next : propertiesOf opCode → Array RuntimeValue → Prop) :
    property.denote #[(type : TypeAttr)] operands next ↔
      ∀ actual, property actual = true →
        ∀ result : Data.LLVM.Int type.modulus.type.bitwidth,
          PropertyMatcher.Interprets opCode actual #[(type : TypeAttr)] operands
            #[.int type.modulus.type.bitwidth result] →
          next actual #[.int type.modulus.type.bitwidth result] := by
  constructor
  · intro h actual hp result hi; exact h actual hp _ hi
  · intro h actual hp results hi
    rcases hi.exists_modArith_result with ⟨result, rfl⟩
    exact h actual hp result hi

theorem PropertyMatcher.denote_single_register
    {type : RegisterType} (property : PropertyMatcher opCode) (operands : Array RuntimeValue)
    (next : propertiesOf opCode → Array RuntimeValue → Prop) :
    property.denote #[(type : TypeAttr)] operands next ↔
      ∀ actual, property actual = true → ∀ result : Data.RISCV.Reg,
        PropertyMatcher.Interprets opCode actual #[(type : TypeAttr)] operands #[.reg result] →
          next actual #[.reg result] := by
  constructor
  · intro h actual hp result hi; exact h actual hp _ hi
  · intro h actual hp results hi
    rcases hi.exists_register_result with ⟨result, rfl⟩
    exact h actual hp result hi

theorem PropertyMatcher.denote_single_pointer
    {type : LLVM.PointerType} (property : PropertyMatcher opCode) (operands : Array RuntimeValue)
    (next : propertiesOf opCode → Array RuntimeValue → Prop) :
    property.denote #[(type : TypeAttr)] operands next ↔
      ∀ actual, property actual = true → ∀ result : UInt64,
        PropertyMatcher.Interprets opCode actual #[(type : TypeAttr)] operands #[.addr result] →
          next actual #[.addr result] := by
  constructor
  · intro h actual hp result hi; exact h actual hp _ hi
  · intro h actual hp results hi
    rcases hi.exists_pointer_result with ⟨result, rfl⟩
    exact h actual hp result hi

def TypeMatcher.denote (matcher : TypeMatcher) (next : TypeAttr → Prop) : Prop :=
  ∀ type, matcher type = true → next type

theorem TypeMatcher.denote_type {Attr : Type} [IsTypeAttr Attr]
    (matcher : Attr → Bool) (next : TypeAttr → Prop) :
    TypeMatcher.denote
        (fun attr => ((attr.cast? Attr).map matcher).getD false) next ↔
      ∀ specificAttr : Attr, matcher specificAttr = true →
        next (specificAttr : TypeAttr) := by
  unfold TypeMatcher.denote
  constructor
  · intro h specificAttr hmatcher
    apply h (specificAttr : TypeAttr)
    have hcast : ((specificAttr : TypeAttr).cast? Attr) = some specificAttr := by
      change (TypeAttr.of Attr specificAttr).cast? Attr = some specificAttr
      exact IsTypeAttr.cast?_of specificAttr
    simp [hcast, hmatcher]
  · intro h attr hmatcher
    cases hcast : attr.cast? Attr with
    | none => simp [hcast] at hmatcher
    | some specificAttr =>
      simp [hcast] at hmatcher
      have heq : (specificAttr : TypeAttr) = attr := by
        change TypeAttr.of Attr specificAttr = attr
        exact (IsTypeAttr.cast?_eq_some_iff attr specificAttr).mp hcast
      rw [← heq]
      exact h specificAttr hmatcher

@[simp 2000]
theorem TypeMatcher.denote_integer (matcher : IntegerType → Bool)
    (next : TypeAttr → Prop) :
    TypeMatcher.denote
        (fun attr => ((attr.cast? IntegerType).map matcher).getD false) next ↔
      ∀ bitwidth, matcher (IntegerType.mk bitwidth) = true →
        next (IntegerType.mk bitwidth : TypeAttr) := by
  rw [TypeMatcher.denote_type]
  constructor
  · intro h bitwidth hmatcher
    exact h (IntegerType.mk bitwidth) hmatcher
  · intro h type hmatcher
    rcases type with ⟨bitwidth⟩
    exact h bitwidth hmatcher

@[simp 2000]
theorem TypeMatcher.denote_float (matcher : FloatType → Bool)
    (next : TypeAttr → Prop) :
    TypeMatcher.denote
        (fun attr => ((attr.cast? FloatType).map matcher).getD false) next ↔
      ∀ bitwidth, matcher (FloatType.mk bitwidth) = true →
        next (FloatType.mk bitwidth : TypeAttr) := by
  rw [TypeMatcher.denote_type]
  constructor
  · intro h bitwidth hmatcher
    exact h (FloatType.mk bitwidth) hmatcher
  · intro h type hmatcher
    rcases type with ⟨bitwidth⟩
    exact h bitwidth hmatcher

@[simp 2000]
theorem TypeMatcher.denote_byte (matcher : LLVM.ByteType → Bool)
    (next : TypeAttr → Prop) :
    TypeMatcher.denote
        (fun attr => ((attr.cast? LLVM.ByteType).map matcher).getD false) next ↔
      ∀ bitwidth, matcher (LLVM.ByteType.mk bitwidth) = true →
        next (LLVM.ByteType.mk bitwidth : TypeAttr) := by
  rw [TypeMatcher.denote_type]
  constructor
  · intro h bitwidth hmatcher
    exact h (LLVM.ByteType.mk bitwidth) hmatcher
  · intro h type hmatcher
    rcases type with ⟨bitwidth⟩
    exact h bitwidth hmatcher

@[simp 2000]
theorem TypeMatcher.denote_modArith (matcher : ModArithType → Bool)
    (next : TypeAttr → Prop) :
    TypeMatcher.denote
        (fun attr => ((attr.cast? ModArithType).map matcher).getD false) next ↔
      ∀ type : ModArithType, matcher type = true → next type := by
  exact TypeMatcher.denote_type matcher next

@[simp 2000]
theorem TypeMatcher.denote_register (matcher : RegisterType → Bool)
    (next : TypeAttr → Prop) :
    TypeMatcher.denote
        (fun attr => ((attr.cast? RegisterType).map matcher).getD false) next ↔
      ∀ type : RegisterType, matcher type = true → next type := by
  exact TypeMatcher.denote_type matcher next

@[simp 2000]
theorem TypeMatcher.denote_pointer (matcher : LLVM.PointerType → Bool)
    (next : TypeAttr → Prop) :
    TypeMatcher.denote
        (fun attr => ((attr.cast? LLVM.PointerType).map matcher).getD false) next ↔
      ∀ type : LLVM.PointerType, matcher type = true → next type := by
  exact TypeMatcher.denote_type matcher next

/-- Interpret one matcher declaration, passing its semantic binding to the rest of the program.

An unsupported or ill-formed semantic path is rejected with `False`; it cannot make validity
vacuously true. -/
@[expose]
def MatchDecl.denote (decl : MatchDecl OpCode) (assignment : SemanticAssignment)
    (next : SemanticAssignment → Prop) : Prop :=
  match decl with
  | .root _ _ _ _ _ _ => next assignment
  | .type matcher handle =>
      matcher.denote fun type => next (assignment.bindType handle type)
  | .value typeHandle handle =>
    match assignment.getType typeHandle with
    | some typeAttr =>
      match typeAttr.val with
      | .integerType intType => ∀ value : Data.LLVM.Int intType.bitwidth,
          next (assignment.bindValue handle (.int intType.bitwidth value))
      | .floatType floatType => ∀ value : Float,
          next (assignment.bindValue handle (.float floatType.bitwidth value))
      | .byteType byteType => ∀ value : Data.LLVM.Byte byteType.bitwidth,
          next (assignment.bindValue handle (.byte byteType.bitwidth value))
      | Attribute.modArithType modType =>
          ∀ value : Data.LLVM.Int modType.modulus.type.bitwidth,
            next (assignment.bindValue handle (.int modType.modulus.type.bitwidth value))
      | Attribute.registerType _ => ∀ value : Data.RISCV.Reg,
          next (assignment.bindValue handle (.reg value))
      | Attribute.llvmPointerType _ => ∀ value : UInt64,
          next (assignment.bindValue handle (.addr value))
      | _ => False
    | none => False
  | .operation _opCode operandHandles returnTypeHandles property propertyHandle handle resultHandles =>
    match assignment.getValues operandHandles, assignment.getTypes returnTypeHandles with
    | some operands, some returnTypes =>
      property.denote returnTypes operands fun actualProperty results =>
        next (((assignment.bindProperty propertyHandle actualProperty).bindOp handle results).bindValues
          resultHandles.toList results.toList)
    | _, _ => False
  | @MatchDecl.guard _ _ _ inputBundle inputs predicate =>
    match MetadataTuple.resolve (self := inputBundle) assignment inputs with
    | some values => predicate values = true → next assignment
    | none => False

@[expose]
def MatchProg.denoteDecls (decls : List (MatchDecl OpCode))
    (assignment : SemanticAssignment) (result : SemanticAssignment → Prop) : Prop :=
  match decls with
  | [] => result assignment
  | (@MatchDecl.guard _ _ Inputs inputBundle inputs predicate) :: decls =>
      MatchProg.denoteDecls decls assignment fun assignment =>
        (@MatchDecl.guard _ _ Inputs inputBundle inputs predicate).denote assignment result
  | decl :: decls => decl.denote assignment fun assignment =>
      MatchProg.denoteDecls decls assignment result

@[expose]
def MatchProg.root? (prog : MatchProg OpCode α) : Option (Handle OpCode .op) :=
  prog.decls.findSome? fun
    | .root _ _ _ _ _ root => some root
    | _ => none


@[expose]
def PropertyMatcher.Models {opCode : OpCode} (property : PropertyMatcher opCode)
    (actual : propertiesOf opCode)
    (_resultTypes : Array TypeAttr) (operands results : Array RuntimeValue) : Prop :=
  property actual = true ∧
    PropertyMatcher.Interprets opCode actual _resultTypes operands results

@[expose]
def MatchDecl.ResultsModel (assignment : SemanticAssignment)
    (resultHandles : Array (Handle OpCode .value)) (results : Array RuntimeValue) : Prop :=
  resultHandles = #[] ∨ assignment.getValues resultHandles = some results

@[expose]
def MatchDecl.Models (decl : MatchDecl OpCode) (assignment : SemanticAssignment) : Prop :=
  match decl with
  | .root _ _ _ _ _ handle => (assignment.getOp handle).isSome
  | .type _ _ => True
  | .value _ handle =>
    ∃ value, assignment.getValue handle = some value
  | .operation _opCode operandHandles returnTypeHandles property propertyHandle handle resultHandles =>
    ∃ operands resultTypes results actualProperty,
      assignment.getValues operandHandles = some operands ∧
      assignment.getTypes returnTypeHandles = some resultTypes ∧
      assignment.getOp handle = some results ∧
      assignment.getProperty propertyHandle = some actualProperty ∧
      MatchDecl.ResultsModel assignment resultHandles results ∧
      property.Models actualProperty resultTypes operands results
  | @MatchDecl.guard _ _ _ inputBundle inputs predicate =>
    ∃ values,
      MetadataTuple.resolve (self := inputBundle) assignment inputs = some values ∧
      predicate values = true

@[expose]
def MatchProg.Models (prog : MatchProg OpCode α) (assignment : SemanticAssignment) : Prop :=
  ∀ decl ∈ prog.decls, decl.Models assignment

/-- Every declaration in the matcher is covered by the prototype's denotation. -/
@[expose]
def MatchProg.Supported (prog : MatchProg OpCode α) : Prop :=
  (∀ decl ∈ prog.decls, decl.Supported) ∧
  (∀ opCode operands returnTypes property propertyHandle rootHandle,
      .root opCode operands returnTypes property propertyHandle rootHandle ∈ prog.decls →
        .operation opCode operands returnTypes property propertyHandle rootHandle #[] ∈ prog.decls) ∧
  (∀ opCode operands returnTypes property propertyHandle rootHandle,
      .root opCode operands returnTypes property propertyHandle rootHandle ∈ prog.decls →
        HasOpInfo.isTerminator opCode = false)


@[expose]
def Replacement.refinesRoot (replacement : Replacement OpCode) (root : Handle OpCode .op)
    (matched final : SemanticAssignment) : Prop :=
  match matched.getOp root, final.getValues replacement with
  | some rootResults, some replacementValues => rootResults ⊒ replacementValues
  | _, _ => False

/-- Creation is supported for effect-free operations with ordinary fallthrough control flow. -/
@[expose]
def CreateDecl.Supported : CreateDecl OpCode → Prop
  | .operation opCode _ _ _ _ _ =>
    HasOpInfo.isTerminator opCode = false ∧
      ∀ actual, HasOpInfo.getEffects opCode actual == .none
  | @CreateDecl.applyNative _ _ _ _ _ _ _ _ _ => True

/-- Every declaration in a creation program is supported. -/
@[expose]
def CreateProg.DeclsSupported : List (CreateDecl OpCode) → Prop
  | [] => True
  | decl :: decls => decl.Supported ∧ CreateProg.DeclsSupported decls

@[expose]
def CreateProg.Supported (prog : CreateProg OpCode α) : Prop :=
  CreateProg.DeclsSupported prog.decls

theorem CreateProg.Supported.of_mem
    {prog : CreateProg OpCode α} (hsupported : prog.Supported)
    {decl : CreateDecl OpCode} (hmem : decl ∈ prog.decls) : decl.Supported := by
  have aux : ∀ decls : List (CreateDecl OpCode),
      CreateProg.DeclsSupported decls → decl ∈ decls → decl.Supported := by
    intro decls hsupported hmem
    induction decls with
    | nil => simp at hmem
    | cons head tail ih =>
      simp only [CreateProg.DeclsSupported] at hsupported
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact hsupported.1
      · exact ih hsupported.2 hmem
  exact aux prog.decls hsupported hmem

/-- Resolve creation properties in the semantic assignment. -/
@[expose]
def CreateProperty.resolveSemantic (property : CreateProperty OpCode opCode)
    (assignment : SemanticAssignment) : Option (propertiesOf opCode) :=
  match property with
  | CreateProperty.literal value => some value
  | CreateProperty.handle propertyHandle => assignment.getProperty propertyHandle

/-- Evaluate a created operation using the generic interpreter and a canonical empty memory. -/
@[expose]
def CreateDecl.denoteResults :
    CreateDecl OpCode → SemanticAssignment → Option (Array RuntimeValue)
  | .operation opCode operands resultTypeHandles properties _ _, assignment => do
      let values ← CreateOperand.getValues operands assignment
      let resultTypes ← assignment.getTypes resultTypeHandles
      let properties ← properties.resolveSemantic assignment
      match interpretOp' opCode properties resultTypes values #[] .empty with
      | .ok (results, _, none) => some results
      | _ => none
  | _, _ => none

theorem CreateDecl.denoteResults_operation_eq_some_iff :
    CreateDecl.denoteResults
        (.operation opCode operands resultTypeHandles property opHandle resultHandles) assignment =
      some results ↔
    ∃ operandValues resultTypes actual memory,
      CreateOperand.getValues operands assignment = some operandValues ∧
      assignment.getTypes resultTypeHandles = some resultTypes ∧
      property.resolveSemantic assignment = some actual ∧
      interpretOp' opCode actual resultTypes operandValues #[] .empty =
        .ok (results, memory, none) := by
  constructor
  · intro h
    simp only [CreateDecl.denoteResults] at h
    cases hoperands : CreateOperand.getValues operands assignment with
    | none => simp [hoperands] at h
    | some operandValues =>
      rw [hoperands] at h
      cases htypes : assignment.getTypes resultTypeHandles with
      | none => simp [htypes] at h
      | some resultTypes =>
        rw [htypes] at h
        cases hactual : property.resolveSemantic assignment with
        | none => simp [hactual] at h
        | some actual =>
          rw [hactual] at h
          simp at h
          generalize hinterpret :
              interpretOp' opCode actual resultTypes operandValues #[] .empty = interpreted at h
          cases interpreted with
          | fail => simp at h
          | ub => simp at h
          | ok result =>
            rcases result with ⟨interpretedResults, memory, controlFlow⟩
            cases controlFlow with
            | some action => simp at h
            | none =>
              simp only [Option.some.injEq] at h
              subst interpretedResults
              exact ⟨operandValues, resultTypes, actual, memory,
                rfl, rfl, rfl, hinterpret⟩
  · rintro ⟨operandValues, resultTypes, actual, memory,
      hoperands, htypes, hactual, hinterpret⟩
    simp [CreateDecl.denoteResults, hoperands, htypes, hactual, hinterpret]

/-- Evaluate one declaration and bind its semantic operation and result handles. -/
@[expose]
def CreateDecl.eval (decl : CreateDecl OpCode) (assignment : SemanticAssignment) :
    Option SemanticAssignment :=
  match decl with
  | .operation _ _ _ _ opHandle resultHandles =>
    match decl.denoteResults assignment with
    | some results =>
      some ((SemanticCreateAssignment.bindOp assignment opHandle results).bindValues
        resultHandles.toList results.toList)
    | none => none
  | @CreateDecl.applyNative _ _ _ _ inputBundle outputBundle inputs rewrite outputs => do
    let values ← MetadataTuple.resolve (self := inputBundle) assignment inputs
    let outputValues ← rewrite values
    MetadataTuple.bind (self := outputBundle) assignment outputs outputValues

/-- Evaluate declarations in creation order. -/
@[expose]
def CreateProg.evalDecls (decls : List (CreateDecl OpCode)) (assignment : SemanticAssignment) :
    Option SemanticAssignment :=
  match decls with
  | [] => some assignment
  | decl :: decls => do
    let assignment ← decl.eval assignment
    CreateProg.evalDecls decls assignment

/-- Pass the completed semantic creation assignment to the terminal validity obligation. -/
@[expose]
def CreateProg.denote (prog : CreateProg OpCode α) (assignment : SemanticAssignment)
    (next : SemanticAssignment → Prop) : Prop :=
  match CreateProg.evalDecls prog.decls assignment with
  | some assignment => next assignment
  | none => True

/-- The denotational proposition derived from a rule's matcher and replacement.

No operational preservation proof is stored here. Pattern authors prove only this algebraic
obligation; the generic compiler theorem derives `PreservesSemantics`. -/
@[expose]
def Pattern.DenotationallyValid (rule : Pattern OpCode) : Prop :=
  rule.matcher.Supported ∧
    rule.creation.Supported ∧
    match rule.matcher.root? with
    | none => False
    | some root =>
      ∀ assignment, rule.matcher.Models assignment →
        rule.creation.denote assignment fun final =>
          rule.replacement.refinesRoot root assignment final

/-- Public rule validity. `puddle_simp` keeps the semantic assignment used by this definition
entirely behind the tactic boundary. -/
@[expose]
def Pattern.Valid (rule : Pattern OpCode) : Prop :=
  rule.DenotationallyValid

/-- Bridge from the syntax-directed denotation used by `puddle_simp` to the model-based
validity statement consumed by correctness.  Keeping this bridge here ensures that pattern
authors never have to manipulate `SemanticAssignment`s in their proofs. -/
axiom Pattern.modelsValid_of_denote (rule : Pattern OpCode)
    (hdenote :
      match rule.matcher.root? with
      | none => False
      | some root =>
        MatchProg.denoteDecls rule.matcher.decls.reverse
          (SemanticAssignment.empty rule.matcher.numHandles)
          (fun assignment =>
            rule.creation.denote assignment fun final =>
              rule.replacement.refinesRoot root assignment final)) :
    match rule.matcher.root? with
    | none => False
    | some root =>
      ∀ assignment, rule.matcher.Models assignment →
        rule.creation.denote assignment fun final =>
          rule.replacement.refinesRoot root assignment final

/-- Reduce syntax-derived denotational validity to the algebraic obligation written by the rule
author. -/
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

macro "puddle_simp" "[" rule:ident "]" : tactic =>
  `(tactic| (
    unfold Pattern.Valid Pattern.DenotationallyValid
    constructor
    · unfold $rule
      puddle_unfold_rule_matcher $rule
      simp [MatchProg.Supported, MatchDecl.Supported, PropertyMatcher.Supported,
        Pattern.Builder, MatchProg.build, MatchProg.typedType, MatchProg.type, MatchProg.value,
        MatchProg.operation, MatchProg.guard, MatchProg.root, bind, pure]
      all_goals subst_vars <;> simp_all
      all_goals grind
    constructor
    · unfold $rule
      puddle_unfold_rule_matcher $rule
      simp [CreateProg.Supported, CreateProg.DeclsSupported, CreateDecl.Supported,
        Pattern.Builder, CreateProg.empty, CreateProg.build, CreateProg.operation,
        CreateProg.applyNative,
        Replacement.ofValue, bind, pure]
      all_goals native_decide
    refine Pattern.modelsValid_of_denote ($rule) ?_
    unfold $rule
    puddle_unfold_rule_matcher $rule
    simp (config := { maxSteps := 300000 })
      [MatchProg.root?, MatchProg.denoteDecls, MatchDecl.denote,
      PropertyMatcher.denote_single_integer, PropertyMatcher.denote_single_float,
      PropertyMatcher.denote_single_byte, PropertyMatcher.denote_single_modArith,
      PropertyMatcher.denote_single_register, PropertyMatcher.denote_single_pointer,
      PropertyMatcher.Interprets,
      Pattern.Builder, MatchProg.build, MatchProg.typedType, MatchProg.type, MatchProg.value,
      MatchProg.operation, MatchProg.guard, MatchProg.root,
      CreateProg.empty, CreateProg.build, CreateProg.operation, CreateProg.applyNative,
      CreateProg.denote, CreateProg.evalDecls,
      CreateDecl.eval, CreateDecl.denoteResults, CreateProperty.resolveSemantic,
      CreateOperand.getValue, CreateOperand.getValues,
      Replacement.refinesRoot, Replacement.ofValue,
      RuntimeValue.isRefinedBy, Option.bind_eq_some_iff,
      SemanticAssignment.empty, SemanticAssignment.bindValues,
      SemanticAssignment.getValues, SemanticAssignment.getTypes,
      Array.mapM_eq_mapM_toList,
      SemanticCreateAssignment.bindValues,
      SemanticCreateAssignment.getOp, SemanticCreateAssignment.getValue,
      SemanticCreateAssignment.getType, SemanticCreateAssignment.getProperty,
      SemanticCreateAssignment.getValue_bindValue_of_eq,
      SemanticCreateAssignment.getValue_bindValue_of_ne,
      SemanticCreateAssignment.getValue_bindOp_of_eq,
      SemanticCreateAssignment.getValue_bindOp_of_ne,
      SemanticCreateAssignment.getValue_bindProperty_of_ne,
      SemanticCreateAssignment.getOp_bindProperty_of_ne,
      SemanticCreateAssignment.getType_bindProperty_of_ne,
      SemanticCreateAssignment.getProperty_bindProperty_of_eq,
      SemanticAssignment.getValue_bindValue_of_eq,
      SemanticAssignment.getValue_bindValue_of_ne,
      SemanticAssignment.getValue_bindOp_of_eq,
      SemanticAssignment.getValue_bindOp_of_ne,
      SemanticAssignment.getValue_bindProperty_of_ne,
      SemanticAssignment.getProperty_bindProperty_of_eq,
      instMetadataStoreSemanticCreateAssignment,
      CreatePropertyArg.toCreateProperty,
      instCreatePropertyArgHandleOpCodeProp,
      instCreatePropertyArgPropertiesOfOpCode,
      default, instInhabitedBool.default,
      bind, pure]))


end

end Veir.Puddle
