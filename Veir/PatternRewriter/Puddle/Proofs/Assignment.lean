module

public import Veir.PatternRewriter.Puddle.Runner

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

@[simp]
theorem Assignment.getValue_bindValue_self
    (assignment : Assignment OpInfo) (handle : Handle OpInfo .value) (value : ValuePtr) :
    Assignment.getValue (Assignment.bindValue assignment handle value) handle =
      some value := by
  simp only [Assignment.bindValue]
  unfold Assignment.bind
  split
  · rename_i h
    unfold Assignment.getValue Assignment.getBinding
    rw [Array.getElem?_set]
    simp
  · rename_i h
    unfold Assignment.getValue Assignment.getBinding
    rw [Array.getElem?_append_replicate_singleton_self _ _ _ _ h]
    simp

theorem Assignment.getValue_bindValue_of_eq
    (assignment : Assignment OpInfo) (bound query : Handle OpInfo .value) (value : ValuePtr)
    (heq : query.id = bound.id) :
    Assignment.getValue (Assignment.bindValue assignment bound value) query =
      some value := by
  rcases bound with ⟨bound⟩
  rcases query with ⟨query⟩
  simp only at heq
  subst query
  exact Assignment.getValue_bindValue_self assignment ⟨bound⟩ value

@[simp]
theorem Assignment.getValue_bindValue_of_ne
    (assignment : Assignment OpInfo) (bound query : Handle OpInfo .value) (value : ValuePtr)
    (hneq : query.id ≠ bound.id) :
    Assignment.getValue (Assignment.bindValue assignment bound value) query =
      Assignment.getValue assignment query := by
  simp only [Assignment.bindValue]
  unfold Assignment.bind
  split
  · rename_i h
    unfold Assignment.getValue Assignment.getBinding
    rw [Array.getElem?_set_ne h (Ne.symm hneq)]
  · rename_i h
    unfold Assignment.getValue Assignment.getBinding
    rw [Array.getElem?_append_replicate_singleton_ne _ _ _ _ h hneq]

@[simp]
theorem Assignment.getValue_bindOp_of_eq
    (assignment : Assignment OpInfo) (bound : Handle OpInfo .op) (query : Handle OpInfo .value)
    (operation : OperationPtr) (heq : query.id = bound.id) :
    Assignment.getValue (Assignment.bindOp assignment bound operation) query = none := by
  simp only [Assignment.bindOp]
  unfold Assignment.bind
  split
  · rename_i h
    unfold Assignment.getValue Assignment.getBinding
    rw [Array.getElem?_set]
    simp [heq]
  · rename_i h
    unfold Assignment.getValue Assignment.getBinding
    rw [heq, Array.getElem?_append_replicate_singleton_self _ _ _ _ h]
    simp

@[simp]
theorem Assignment.getValue_bindOp_of_ne
    (assignment : Assignment OpInfo) (bound : Handle OpInfo .op) (query : Handle OpInfo .value)
    (operation : OperationPtr) (hneq : query.id ≠ bound.id) :
    Assignment.getValue (Assignment.bindOp assignment bound operation) query =
      Assignment.getValue assignment query := by
  simp only [Assignment.bindOp]
  unfold Assignment.bind
  split
  · rename_i h
    unfold Assignment.getValue Assignment.getBinding
    rw [Array.getElem?_set_ne h (Ne.symm hneq)]
  · rename_i h
    unfold Assignment.getValue Assignment.getBinding
    rw [Array.getElem?_append_replicate_singleton_ne _ _ _ _ h hneq]

end

end Veir.Puddle
