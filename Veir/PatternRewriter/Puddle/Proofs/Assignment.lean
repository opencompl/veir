module

public import Veir.PatternRewriter.Puddle.Execution

/-! Elementary lemmas about Puddle runtime assignments. -/

namespace Veir.Puddle

public section

variable {OpInfo : Type} [HasOpInfo OpInfo]

@[simp]
theorem Array.getElem?_append_replicate_singleton_self
    (array : Array α) (id : Nat) (fill value : α) (h : ¬id < array.size) :
    (array ++ Array.replicate (id - array.size) fill ++ #[value])[id]? = some value := by
  have hs : array.size ≤ id := Nat.le_of_not_gt h
  simp only [Array.getElem?_append]
  simp [hs]

@[simp]
theorem Array.getElem?_append_replicate_singleton_ne
    (array : Array (Option α)) (id query : Nat) (value : α) (h : ¬id < array.size)
    (hne : query ≠ id) :
    ((array ++ Array.replicate (id - array.size) none ++ #[some value])[query]?).join =
      array[query]?.join := by
  have hs : array.size ≤ id := Nat.le_of_not_gt h
  have hsize : array.size + (id - array.size) = id := Nat.add_sub_of_le hs
  simp only [Array.size_append, Array.size_replicate, Array.getElem?_append,
    Array.getElem?_replicate]
  rw [hsize]
  by_cases hquery : query < array.size
  · have hqi : query < id := Nat.lt_of_lt_of_le hquery hs
    simp [hquery, hqi]
  · have hqs : array.size ≤ query := Nat.le_of_not_gt hquery
    by_cases hqi : query < id
    · have hgap : query - array.size < id - array.size :=
        Nat.sub_lt_sub_right hqs hqi
      simp [hquery, hqi, hgap]
    · have hdiff : query - id ≠ 0 := by omega
      simp [hquery, hqi, hdiff]

theorem Assignment.bind_get
    {assignment assignment' : Assignment OpInfo} {handleType : HandleType OpInfo}
    {handle : Handle OpInfo handleType} {binding : Binding OpInfo}
    (hbind : Assignment.bind assignment handle binding = some assignment') :
    assignment'.bindings[handle.id]? = some (some binding) := by
  unfold Assignment.bind at hbind
  split at hbind
  · rename_i h
    split at hbind
    · simp only [Option.some.injEq] at hbind
      subst assignment'
      rw [Array.getElem?_set]
      simp
    · split at hbind
      · simp only [Option.some.injEq] at hbind
        subst assignment'
        simp_all
      · simp at hbind
  · rename_i h
    simp only [Option.some.injEq] at hbind
    subst assignment'
    rw [Array.push_eq_append]
    exact
      Array.getElem?_append_replicate_singleton_self
        assignment.bindings handle.id none (some binding) h

theorem Assignment.bind_get_of_ne
    {assignment assignment' : Assignment OpInfo} {handleType : HandleType OpInfo}
    {handle : Handle OpInfo handleType} {query : Nat} {binding : Binding OpInfo}
    (hbind : Assignment.bind assignment handle binding = some assignment')
    (hne : query ≠ handle.id) :
    assignment'.bindings[query]?.join = assignment.bindings[query]?.join := by
  unfold Assignment.bind at hbind
  split at hbind
  · rename_i h
    split at hbind
    · simp only [Option.some.injEq] at hbind
      subst assignment'
      rw [Array.getElem?_set_ne h (Ne.symm hne)]
    · split at hbind <;> simp_all
  · rename_i h
    simp only [Option.some.injEq] at hbind
    subst assignment'
    rw [Array.push_eq_append]
    exact
      Array.getElem?_append_replicate_singleton_ne
        assignment.bindings handle.id query binding h hne

theorem Assignment.getValue_bindValue_of_eq
    {assignment assignment' : Assignment OpInfo}
    (bound query : Handle OpInfo .value) (value : ValuePtr)
    (hbind : Assignment.bindValue assignment bound value = some assignment')
    (heq : query.id = bound.id) :
    Assignment.getValue assignment' query = some value := by
  unfold Assignment.bindValue at hbind
  unfold Assignment.getValue Assignment.getBinding
  rw [heq, Assignment.bind_get hbind]
  rfl

@[simp]
theorem Assignment.getValue_bindValue_of_ne
    {assignment assignment' : Assignment OpInfo}
    (bound query : Handle OpInfo .value) (value : ValuePtr)
    (hbind : Assignment.bindValue assignment bound value = some assignment')
    (hneq : query.id ≠ bound.id) :
    Assignment.getValue assignment' query = Assignment.getValue assignment query := by
  unfold Assignment.bindValue at hbind
  unfold Assignment.getValue Assignment.getBinding
  rw [Assignment.bind_get_of_ne hbind hneq]

@[simp]
theorem Assignment.getValue_bindOp_of_eq
    {assignment assignment' : Assignment OpInfo}
    (bound : Handle OpInfo .op) (query : Handle OpInfo .value)
    (operation : OperationPtr) (hbind : Assignment.bindOp assignment bound operation = some assignment')
    (heq : query.id = bound.id) :
    Assignment.getValue assignment' query = none := by
  unfold Assignment.bindOp at hbind
  unfold Assignment.getValue Assignment.getBinding
  rw [heq, Assignment.bind_get hbind]
  rfl

@[simp]
theorem Assignment.getValue_bindOp_of_ne
    {assignment assignment' : Assignment OpInfo}
    (bound : Handle OpInfo .op) (query : Handle OpInfo .value)
    (operation : OperationPtr) (hbind : Assignment.bindOp assignment bound operation = some assignment')
    (hneq : query.id ≠ bound.id) :
    Assignment.getValue assignment' query = Assignment.getValue assignment query := by
  unfold Assignment.bindOp at hbind
  unfold Assignment.getValue Assignment.getBinding
  rw [Assignment.bind_get_of_ne hbind hneq]

end

end Veir.Puddle
