module

public import Veir.PatternRewriter.Puddle.AssignmentLemmas
public import Veir.PatternRewriter.Puddle.Validity

namespace Veir.Puddle

public section

/-- Interpret a concrete binding using a partial resolver for SSA values. -/
@[expose]
def Binding.denote (resolve : ValuePtr → Option RuntimeValue)
    (typeOf : ValuePtr → TypeAttr) :
    Binding OpCode → Option SemanticBinding
  | .op _ => none
  | .value ptr => (resolve ptr).map (fun value => SemanticBinding.value value (typeOf ptr))
  | .type ty => some (.type ty)
  | .property code props => some (.property code props)

/-- The semantic view of an assignment at a particular program execution. -/
@[expose]
def Assignment.denote (assignment : Assignment OpCode)
    (resolve : ValuePtr → Option RuntimeValue)
    (typeOf : ValuePtr → TypeAttr) : SemanticAssignment :=
  fun id => assignment.bindings[id]?.join >>= Binding.denote resolve typeOf

namespace Assignment

theorem denote_getValue (assignment : Assignment OpCode)
    (resolve : ValuePtr → Option RuntimeValue) (handle : Handle OpCode .value)
    (typeOf : ValuePtr → TypeAttr) :
    (assignment.denote resolve typeOf).getValue handle = assignment.getValue handle >>= resolve := by
  simp only [denote, SemanticAssignment.getValue, getValue, getBinding]
  cases assignment.bindings[handle.id]?.join with
  | none => rfl
  | some binding =>
    cases binding with
    | value ptr => cases hr : resolve ptr <;> simp [Binding.denote, hr]
    | op _ => rfl
    | type _ => rfl
    | property _ _ => rfl

/-- A value's type metadata is available precisely when its runtime value resolves. -/
theorem denote_getValueType (assignment : Assignment OpCode)
    (resolve : ValuePtr → Option RuntimeValue) (handle : Handle OpCode .value)
    (typeOf : ValuePtr → TypeAttr) :
    (assignment.denote resolve typeOf).getValueType handle =
      (assignment.getValue handle >>= fun ptr => resolve ptr >>= fun _ => some (typeOf ptr)) := by
  simp only [denote, SemanticAssignment.getValueType, getValue, getBinding]
  cases assignment.bindings[handle.id]?.join with
  | none => rfl
  | some binding =>
    cases binding with
    | value ptr => cases hr : resolve ptr <;> simp [Binding.denote, hr]
    | op _ => rfl
    | type _ => rfl
    | property _ _ => rfl

/-- Transport a concrete pointer's declared type once its value is resolved. -/
theorem denote_getValueType_of_getValue (assignment : Assignment OpCode)
    (resolve : ValuePtr → Option RuntimeValue) (handle : Handle OpCode .value)
    {ptr : ValuePtr} {value : RuntimeValue}
    (hptr : assignment.getValue handle = some ptr) (hresolve : resolve ptr = some value)
    (typeOf : ValuePtr → TypeAttr) :
    (assignment.denote resolve typeOf).getValueType handle = some (typeOf ptr) := by
  simp [denote_getValueType, hptr, hresolve]

theorem denote_getType (assignment : Assignment OpCode)
    (resolve : ValuePtr → Option RuntimeValue) (handle : Handle OpCode .type)
    (typeOf : ValuePtr → TypeAttr) :
    (assignment.denote resolve typeOf).getType handle = assignment.getType handle := by
  simp only [denote, SemanticAssignment.getType, getType, getBinding]
  cases assignment.bindings[handle.id]?.join with
  | none => rfl
  | some binding =>
    cases binding with
    | value ptr => cases resolve ptr <;> simp [Binding.denote, *]
    | op _ => rfl
    | type _ => rfl
    | property _ _ => simp [Binding.denote]

theorem denote_getProperty (assignment : Assignment OpCode)
    (resolve : ValuePtr → Option RuntimeValue) {code : OpCode}
    (handle : Handle OpCode (.prop code))
    (typeOf : ValuePtr → TypeAttr) :
    (assignment.denote resolve typeOf).getProperty handle = assignment.getProperty handle := by
  simp only [denote, SemanticAssignment.getProperty, getProperty, getBinding]
  cases assignment.bindings[handle.id]?.join with
  | none => rfl
  | some binding =>
    cases binding with
    | value ptr => cases resolve ptr <;> simp [Binding.denote, *]
    | op _ => rfl
    | type _ => rfl
    | property _ _ =>
      simp [Binding.denote]
      split <;> rfl

/-- Metadata lookup agrees after translating the concrete array to a semantic list. -/
theorem denote_getTypes (assignment : Assignment OpCode)
    (resolve : ValuePtr → Option RuntimeValue) (handles : Array (Handle OpCode .type))
    (typeOf : ValuePtr → TypeAttr) :
    (assignment.denote resolve typeOf).getTypes handles.toList =
      (assignment.getTypes handles).map Array.toList := by
  have heq : (assignment.denote resolve typeOf).getType = assignment.getType := by
    funext handle; exact denote_getType assignment resolve handle typeOf
  simp only [SemanticAssignment.getTypes, getTypes, heq, Array.mapM_eq_mapM_toList]
  cases handles.toList.mapM assignment.getType <;> simp

private theorem list_mapM_comp {α β γ : Type} (f : α → Option β) (g : β → Option γ)
    (xs : List α) :
    xs.mapM (fun x => f x >>= g) = xs.mapM f >>= List.mapM g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons, ih]
    cases hf : f x with
    | none => simp
    | some y =>
      cases hg : g y <;> cases ht : xs.mapM f <;> simp [List.mapM_cons, hg]

/-- Resolving concrete SSA values is equivalent to semantic list lookup. -/
theorem denote_getValues (assignment : Assignment OpCode)
    (resolve : ValuePtr → Option RuntimeValue) (handles : Array (Handle OpCode .value))
    (typeOf : ValuePtr → TypeAttr) :
    (assignment.denote resolve typeOf).getValues handles.toList =
      (assignment.getValues handles >>= fun pointers => pointers.toList.mapM resolve) := by
  have heq : (assignment.denote resolve typeOf).getValue =
      fun handle => assignment.getValue handle >>= resolve := by
    funext handle; exact denote_getValue assignment resolve handle typeOf
  simp only [SemanticAssignment.getValues, heq, getValues,
    Array.mapM_eq_mapM_toList]
  rw [list_mapM_comp]
  cases handles.toList.mapM assignment.getValue <;> simp

/-- Resolving concrete pointer types agrees with semantic operand type lookup. -/
theorem denote_getValueTypes (assignment : Assignment OpCode)
    (resolve : ValuePtr → Option RuntimeValue) (handles : Array (Handle OpCode .value))
    (typeOf : ValuePtr → TypeAttr) :
    (assignment.denote resolve typeOf).getValueTypes handles.toList =
      (assignment.getValues handles >>= fun pointers =>
        pointers.toList.mapM (fun ptr => resolve ptr >>= fun _ => some (typeOf ptr))) := by
  have heq : (assignment.denote resolve typeOf).getValueType =
      fun handle => assignment.getValue handle >>= fun ptr => resolve ptr >>= fun _ => some (typeOf ptr) := by
    funext handle; exact denote_getValueType assignment resolve handle typeOf
  simp only [SemanticAssignment.getValueTypes, heq, getValues,
    Array.mapM_eq_mapM_toList]
  rw [list_mapM_comp]
  cases handles.toList.mapM assignment.getValue <;> simp

private theorem list_mapM_guard {α β γ : Type} (f : α → Option β) (g : α → Option γ)
    (xs : List α) {ys : List β} (h : xs.mapM f = some ys) :
    xs.mapM (fun x => f x >>= fun _ => g x) = xs.mapM g := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih =>
    cases hf : f x with
    | none => simp [List.mapM_cons, hf] at h
    | some value =>
      cases ht : xs.mapM f with
      | none => simp [List.mapM_cons, hf, ht] at h
      | some values =>
        rw [List.mapM_cons, List.mapM_cons, hf]
        rw [ih ht]
        rfl

/-- Successfully resolved operand values expose the types of the same concrete pointers. -/
theorem denote_getValueTypes_of_getValues (assignment : Assignment OpCode)
    (resolve : ValuePtr → Option RuntimeValue) (handles : Array (Handle OpCode .value))
    {pointers : Array ValuePtr} {values : List RuntimeValue}
    (hptrs : assignment.getValues handles = some pointers)
    (hresolve : pointers.toList.mapM resolve = some values)
    (typeOf : ValuePtr → TypeAttr) :
    (assignment.denote resolve typeOf).getValueTypes handles.toList =
      some (pointers.toList.map typeOf) := by
  rw [denote_getValueTypes assignment resolve handles typeOf, hptrs]
  simpa [← Option.pure_def, List.mapM_pure] using list_mapM_guard resolve (fun p => some (typeOf p)) pointers.toList hresolve

/-- The denotation of every pre-existing successful binding is preserved by concrete binding. -/
theorem denote_preserved_of_bind {a b : Assignment OpCode}
    {kind otherKind : HandleType OpCode} {handle : Handle OpCode kind}
    {other : Handle OpCode otherKind} {binding existing : Binding OpCode}
    (resolve : ValuePtr → Option RuntimeValue)
    (h : a.bind handle binding = some b) (hold : a.getBinding other = some existing)
    (typeOf : ValuePtr → TypeAttr) :
    b.denote resolve typeOf other.id = a.denote resolve typeOf other.id := by
  have hb := getBinding_preserved_of_bind h hold
  change (b.getBinding other >>= Binding.denote resolve typeOf) =
    (a.getBinding other >>= Binding.denote resolve typeOf)
  rw [hb, hold]

end Assignment

end

end Veir.Puddle
