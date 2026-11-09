module

public import Veir.PatternRewriter.Puddle.Execution

namespace Veir.Puddle.Assignment

public section

variable {OpInfo : Type} [HasOpInfo OpInfo]

/-- A successful binding installs the requested binding. -/
theorem getBinding_of_bind {a b : Assignment OpInfo} {kind : HandleType OpInfo}
    {handle : Handle OpInfo kind} {binding : Binding OpInfo}
    (h : a.bind handle binding = some b) : b.getBinding handle = some binding := by
  unfold bind at h
  split at h
  · split at h
    · cases h
      simp [getBinding]
    · split at h
      · cases h
        simp_all [getBinding]
      · contradiction
  · cases h
    have hsize : (a.bindings ++ Array.replicate (handle.id - a.bindings.size) none).size = handle.id := by
      simp; omega
    simp only [getBinding, Array.getElem?_push, hsize, ↓reduceIte, Option.join_some]

/-- A successful binding retains every previously populated slot. -/
theorem getBinding_preserved_of_bind {a b : Assignment OpInfo}
    {kind otherKind : HandleType OpInfo} {handle : Handle OpInfo kind}
    {other : Handle OpInfo otherKind} {binding existing : Binding OpInfo}
    (h : a.bind handle binding = some b) (hold : a.getBinding other = some existing) :
    b.getBinding other = some existing := by
  unfold bind at h
  split at h
  · split at h
    · cases h
      simp only [getBinding_eq_some_iff] at hold ⊢
      grind
    · split at h
      · cases h; exact hold
      · contradiction
  · cases h
    simp only [getBinding_eq_some_iff] at hold ⊢
    have hi : other.id < a.bindings.size := by
      grind
    simp only [Array.getElem?_push, Array.getElem?_append]
    split <;> simp_all
    all_goals grind


/-- Typed operation lookup after a successful operation binding. -/
theorem getOp_of_bindOp {a b : Assignment OpInfo} {handle : Handle OpInfo .op}
    {value : OperationPtr} (h : a.bindOp handle value = some b) :
    b.getOp handle = some value := by
  simp [getOp, getBinding_of_bind h]

/-- Typed value lookup after a successful value binding. -/
theorem getValue_of_bindValue {a b : Assignment OpInfo} {handle : Handle OpInfo .value}
    {value : ValuePtr} (h : a.bindValue handle value = some b) :
    b.getValue handle = some value := by
  simp [getValue, getBinding_of_bind h]

/-- Typed type lookup after a successful type binding. -/
theorem getType_of_bindType {a b : Assignment OpInfo} {handle : Handle OpInfo .type}
    {value : TypeAttr} (h : a.bindType handle value = some b) :
    b.getType handle = some value := by
  simp [getType, getBinding_of_bind h]

/-- Typed property lookup after a successful property binding. -/
theorem getProperty_of_bindProperty {a b : Assignment OpInfo} {code : OpInfo}
    {handle : Handle OpInfo (.prop code)} {value : propertiesOf code}
    (h : a.bindProperty handle value = some b) : b.getProperty handle = some value := by
  simp [getProperty, getBinding_of_bind h]

/-- Successful list binding requires equal list lengths. -/
theorem bindValues_length {a b : Assignment OpInfo} {handles : List (Handle OpInfo .value)}
    {values : List ValuePtr} (h : a.bindValues handles values = some b) :
    handles.length = values.length := by
  induction handles generalizing a values with
  | nil => cases values <;> simp_all [bindValues]
  | cons handle handles ih =>
    cases values with
    | nil => simp [bindValues] at h
    | cons value values =>
      simp only [bindValues, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨middle, _, h⟩ := h
      simpa using ih h

/-- Successful list binding requires equal list lengths. -/
theorem bindTypes_length {a b : Assignment OpInfo} {handles : List (Handle OpInfo .type)}
    {values : List TypeAttr} (h : a.bindTypes handles values = some b) :
    handles.length = values.length := by
  induction handles generalizing a values with
  | nil => cases values <;> simp_all [bindTypes]
  | cons handle handles ih =>
    cases values with
    | nil => simp [bindTypes] at h
    | cons value values =>
      simp only [bindTypes, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨middle, _, h⟩ := h
      simpa using ih h

/-- List binding retains every existing binding, including handles repeated in the list. -/
theorem getBinding_preserved_of_bindValues {a b : Assignment OpInfo}
    {handles : List (Handle OpInfo .value)} {values : List ValuePtr}
    {kind : HandleType OpInfo} {handle : Handle OpInfo kind} {existing : Binding OpInfo}
    (h : a.bindValues handles values = some b) (hold : a.getBinding handle = some existing) :
    b.getBinding handle = some existing := by
  induction handles generalizing a values with
  | nil => cases values <;> simp_all [bindValues]
  | cons first rest ih =>
    cases values with
    | nil => simp [bindValues] at h
    | cons value values =>
      simp only [bindValues, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨middle, hb, hr⟩ := h
      exact ih hr (getBinding_preserved_of_bind hb hold)

/-- List binding retains every existing binding, including handles repeated in the list. -/
theorem getBinding_preserved_of_bindTypes {a b : Assignment OpInfo}
    {handles : List (Handle OpInfo .type)} {values : List TypeAttr}
    {kind : HandleType OpInfo} {handle : Handle OpInfo kind} {existing : Binding OpInfo}
    (h : a.bindTypes handles values = some b) (hold : a.getBinding handle = some existing) :
    b.getBinding handle = some existing := by
  induction handles generalizing a values with
  | nil => cases values <;> simp_all [bindTypes]
  | cons first rest ih =>
    cases values with
    | nil => simp [bindTypes] at h
    | cons value values =>
      simp only [bindTypes, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨middle, hb, hr⟩ := h
      exact ih hr (getBinding_preserved_of_bind hb hold)

/-- Every successfully bound list entry can be read from the final assignment. -/
theorem getValue_of_bindValues_getElem {a b : Assignment OpInfo}
    {handles : List (Handle OpInfo .value)} {values : List ValuePtr}
    (h : a.bindValues handles values = some b) (i : Nat) (hi : i < handles.length) :
    b.getValue handles[i] = some values[i]! := by
  induction handles generalizing a values i with
  | nil => simp at hi
  | cons first rest ih =>
    cases values with
    | nil => simp [bindValues] at h
    | cons value values =>
      simp only [bindValues, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨middle, hb, hr⟩ := h
      cases i with
      | zero =>
        have hbound := getBinding_preserved_of_bindValues hr (getBinding_of_bind hb)
        simp [getValue, hbound]
      | succ i =>
        simpa using ih hr i (by simpa using hi)

/-- Reading a successfully bound list recovers the supplied array, even with repeated handles. -/
theorem getValues_of_bindValues {a b : Assignment OpInfo}
    {handles : List (Handle OpInfo .value)} {values : List ValuePtr}
    (h : a.bindValues handles values = some b) :
    b.getValues handles.toArray = some values.toArray := by
  apply (Array.mapM_eq_some_iff_of_size_eq (by simpa using bindValues_length h)).mpr
  intro i hi
  have hv : i < values.length := by have := bindValues_length h; simp_all
  have hh : i < handles.length := by simpa using hi
  simpa [List.getElem?_eq_getElem, hv, hh] using getValue_of_bindValues_getElem h i (by simpa using hi)

/-- Every successfully bound list entry can be read from the final assignment. -/
theorem getType_of_bindTypes_getElem {a b : Assignment OpInfo}
    {handles : List (Handle OpInfo .type)} {values : List TypeAttr}
    (h : a.bindTypes handles values = some b) (i : Nat) (hi : i < handles.length) :
    b.getType handles[i] = some values[i]! := by
  induction handles generalizing a values i with
  | nil => simp at hi
  | cons first rest ih =>
    cases values with
    | nil => simp [bindTypes] at h
    | cons value values =>
      simp only [bindTypes, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨middle, hb, hr⟩ := h
      cases i with
      | zero =>
        have hbound := getBinding_preserved_of_bindTypes hr (getBinding_of_bind hb)
        simp [getType, hbound]
      | succ i =>
        simpa using ih hr i (by simpa using hi)

/-- Reading a successfully bound list recovers the supplied array, even with repeated handles. -/
theorem getTypes_of_bindTypes {a b : Assignment OpInfo}
    {handles : List (Handle OpInfo .type)} {values : List TypeAttr}
    (h : a.bindTypes handles values = some b) :
    b.getTypes handles.toArray = some values.toArray := by
  apply (Array.mapM_eq_some_iff_of_size_eq (by simpa using bindTypes_length h)).mpr
  intro i hi
  have hv : i < values.length := by have := bindTypes_length h; simp_all
  have hh : i < handles.length := by simpa using hi
  simpa [List.getElem?_eq_getElem, hv, hh] using getType_of_bindTypes_getElem h i (by simpa using hi)

end

end Veir.Puddle.Assignment
