module

public import Veir.Passes.DCE.MacroNormalForm
import all Veir.Passes.DCE.MacroNormalForm
import all Veir.Passes.DCE.MacroSteps
import all Veir.Interpreter.CTreeRefinement.Iteration
import all Veir.Interpreter.CTree

public section

namespace Veir.DCE

/-- The continuation added by one chronological deletion. -/
def spliceContinuation (body : ι → Tree (ι ⊕ α)) (selected : ι → Bool) :
    (ι ⊕ α) → Tree (ι ⊕ α)
  | .inl next => if selected next then CTree.CTree.tau1 (body next) else pure (.inl next)
  | .inr value => pure (.inr value)

/-- The finite deleted-operation suffix following one original CFG step. -/
def macroSuffix (operationAt : ι → Option OperationPtr) (body : ι → Tree (ι ⊕ α))
    (operations : List OperationPtr) : (ι ⊕ α) → Tree (ι ⊕ α) :=
  operations.foldl (fun suffix operation => fun result =>
    suffix result >>= spliceContinuation (fun next => body next >>= suffix)
      (deletionPredicate operationAt operation)) pure

theorem macroSuffix_nil (operationAt : ι → Option OperationPtr) (body : ι → Tree (ι ⊕ α)) :
    macroSuffix operationAt body [] = pure := by simp [macroSuffix]

theorem macroSuffix_snoc (operationAt : ι → Option OperationPtr) (body : ι → Tree (ι ⊕ α))
    (operations : List OperationPtr) (operation : OperationPtr) :
    macroSuffix operationAt body (operations ++ [operation]) = fun result =>
      macroSuffix operationAt body operations result >>=
        spliceContinuation (fun next => body next >>= macroSuffix operationAt body operations)
          (deletionPredicate operationAt operation) := by
  simp [macroSuffix, List.foldl_append]

/-- Factor the first original source step out of every normalized macrostep. -/
theorem macroBody_eq_bind_suffix (operationAt : ι → Option OperationPtr)
    (body : ι → Tree (ι ⊕ α)) (operations : List OperationPtr) :
    ∀ state, macroBody operationAt body operations state =
      body state >>= macroSuffix operationAt body operations := by
  apply list_snoc_induction (P := fun operations => ∀ state,
    macroBody operationAt body operations state = body state >>= macroSuffix operationAt body operations)
  · intro state
    simp [macroBody_nil, macroSuffix_nil]
  · intro operations operation ih state
    rw [macroBody_snoc, macroSuffix_snoc]
    simp only [Tree.spliceIterBody]
    rw [ih state, bind_assoc]
    congr 1
    funext result
    congr 1
    funext middle
    cases middle with
    | inl next =>
      simp only [spliceContinuation]
      rw [ih next]
    | inr value => rfl

theorem macroSuffix_finite (operationAt : ι → Option OperationPtr)
    (body : ι → Tree (ι ⊕ α)) (finite : ∀ state, PureOrErr (body state))
    (operations : List OperationPtr) :
    ∀ result, PureOrErr (macroSuffix operationAt body operations result) := by
  apply list_snoc_induction (P := fun operations =>
    ∀ result, PureOrErr (macroSuffix operationAt body operations result))
  · intro result; rw [macroSuffix_nil]; exact .ret _
  · intro operations operation ih result
    rw [macroSuffix_snoc]
    apply PureOrErr.bind _ _ (ih result)
    intro middle
    cases middle with
    | inl next =>
      dsimp only [spliceContinuation]
      split
      · apply PureOrErr.tau _ _
        intro _
        exact PureOrErr.bind _ _ (finite next) ih
      · exact .ret _
    | inr value => exact .ret _

theorem spliceContinuation_success_iff (body : ι → Tree (ι ⊕ α)) (selected : ι → Bool)
    (initial result : ι ⊕ α) :
    PureOrErr.CanInterpretTo (spliceContinuation body selected initial) (.ok result) ↔
      match initial with
      | .inl next => if selected next then
          PureOrErr.CanInterpretTo (body next) (.ok result) else result = .inl next
      | .inr value => result = .inr value := by
  cases initial with
  | inl next =>
    dsimp only [spliceContinuation]
    split
    · simp only [CTree.CTree.tau1, PureOrErr.CanInterpretTo.tauG_iff]
      constructor
      · rintro ⟨_, executes⟩; exact executes
      · intro executes; exact ⟨PUnit.unit, executes⟩
    · simp
  | inr value => simp [spliceContinuation]

/-- A suffix may leave the first outcome untouched, or continue from a deleted
operation through a grouped execution of original source steps. -/
inductive SuffixRun (operationAt : ι → Option OperationPtr) (body : ι → Tree (ι ⊕ α))
    (allowed : OperationPtr → Prop) : (ι ⊕ α) → (ι ⊕ α) → Prop where
| stop (result) : SuffixRun operationAt body allowed result result
| splice {initial middle result operation} :
    SuffixRun operationAt body allowed initial (.inl middle) →
    operationAt middle = some operation → allowed operation →
    MacroRun operationAt body allowed middle result →
    SuffixRun operationAt body allowed initial result

theorem SuffixRun.weaken {operationAt : ι → Option OperationPtr} {body : ι → Tree (ι ⊕ α)}
    {allowed more : OperationPtr → Prop} {initial result}
    (run : SuffixRun operationAt body allowed initial result)
    (includes : ∀ operation, allowed operation → more operation) :
    SuffixRun operationAt body more initial result := by
  induction run with
  | stop => exact .stop _
  | splice first identifies admitted rest ih =>
    exact .splice ih identifies (includes _ admitted) (rest.weaken includes)

theorem macroSuffix_success_run (operationAt : ι → Option OperationPtr)
    (body : ι → Tree (ι ⊕ α)) (operations : List OperationPtr) :
    ∀ initial result, PureOrErr.CanInterpretTo (macroSuffix operationAt body operations initial) (.ok result) →
      SuffixRun operationAt body (fun operation => operation ∈ operations) initial result := by
  apply list_snoc_induction (P := fun operations => ∀ initial result,
    PureOrErr.CanInterpretTo (macroSuffix operationAt body operations initial) (.ok result) →
      SuffixRun operationAt body (fun operation => operation ∈ operations) initial result)
  · intro initial result executes
    rw [macroSuffix_nil] at executes
    have equal := (PureOrErr.CanInterpretTo.pure_iff _ _).mp executes
    cases equal
    exact .stop _
  · intro operations operation ih initial result executes
    rw [macroSuffix_snoc] at executes
    simp only [Bind.bind, PureOrErr.CanInterpretTo.bind_iff, reduceCtorEq,
      and_false, or_false] at executes
    obtain ⟨middle, first, rest⟩ := executes
    have firstRun : SuffixRun operationAt body (fun op => op ∈ operations ++ [operation]) initial middle :=
      (ih initial middle first).weaken (fun op member => by simp [member])
    have continued := (spliceContinuation_success_iff _ _ _ _).mp rest
    cases middle with
    | inr value => subst result; exact firstRun
    | inl next =>
      by_cases selected : deletionPredicate operationAt operation next = true
      · simp only [selected, ↓reduceIte] at continued
        have continued' : PureOrErr.CanInterpretTo
            (macroBody operationAt body operations next) (.ok result) := by
          simpa only [macroBody_eq_bind_suffix, Bind.bind] using continued
        apply SuffixRun.splice (operation := operation) firstRun
        · simpa only [deletionPredicate, beq_iff_eq] using selected
        · simp
        · exact (macroBody_success_run operationAt body operations next result continued').weaken
            (fun op member => by simp [member])
      · simp only [selected, Bool.false_eq_true, ↓reduceIte] at continued
        subst result
        exact firstRun

/-- The finite suffix also ends outside the entire chronological deletion list. -/
theorem macroSuffix_endpoint_not_deleted (operationAt : ι → Option OperationPtr)
    (body : ι → Tree (ι ⊕ α)) (eligible : OperationPtr → Prop) (rank : OperationPtr → Nat)
    (progress : ∀ state next operation nextOperation,
      operationAt state = some operation → eligible operation →
      PureOrErr.CanInterpretTo (body state) (.ok (.inl next)) →
      operationAt next = some nextOperation → rank nextOperation < rank operation)
    (operations : List OperationPtr) :
    (∀ operation ∈ operations, eligible operation) →
    ∀ initial next operation,
      PureOrErr.CanInterpretTo (macroSuffix operationAt body operations initial) (.ok (.inl next)) →
      operationAt next = some operation → operation ∉ operations := by
  apply list_snoc_induction (P := fun operations =>
    (∀ operation ∈ operations, eligible operation) →
    ∀ initial next operation,
      PureOrErr.CanInterpretTo (macroSuffix operationAt body operations initial) (.ok (.inl next)) →
      operationAt next = some operation → operation ∉ operations)
  · simp
  · intro operations removed ih admitted initial next operation executes identifies
    have admittedBefore : ∀ operation ∈ operations, eligible operation :=
      fun operation member => admitted operation (by simp [member])
    rw [macroSuffix_snoc] at executes
    simp only [Bind.bind, PureOrErr.CanInterpretTo.bind_iff, reduceCtorEq,
      and_false, or_false] at executes
    obtain ⟨middle, first, rest⟩ := executes
    have continued := (spliceContinuation_success_iff _ _ _ _).mp rest
    cases middle with
    | inr value => cases continued
    | inl middle =>
      by_cases selected : deletionPredicate operationAt removed middle = true
      · simp only [selected, ↓reduceIte] at continued
        have continued' : PureOrErr.CanInterpretTo
            (macroBody operationAt body operations middle) (.ok (.inl next)) := by
          simpa only [macroBody_eq_bind_suffix, Bind.bind] using continued
        have outsideBefore := macroBody_endpoint_not_deleted operationAt body eligible rank progress
          operations admittedBefore middle next operation continued' identifies
        have identifiesMiddle : operationAt middle = some removed := by
          simpa only [deletionPredicate, beq_iff_eq] using selected
        have decreased := macroBody_rank_decreases operationAt body eligible rank progress
          operations admittedBefore middle next removed operation identifiesMiddle
          (admitted removed (by simp)) continued' identifies
        have different : operation ≠ removed := by intro equal; subst operation; omega
        simpa only [List.mem_append, List.mem_singleton, not_or] using And.intro outsideBefore different
      · simp only [selected, Bool.false_eq_true, ↓reduceIte, Sum.inl.injEq] at continued
        subst next
        have outsideBefore := ih admittedBefore initial middle operation first identifies
        have different : operation ≠ removed := by
          intro equal
          subst operation
          apply selected
          simp [deletionPredicate, identifies]
        simpa only [List.mem_append, List.mem_singleton, not_or] using And.intro outsideBefore different

/-- Return values have no current operation. -/
def outcomeOperationAt (operationAt : ι → Option OperationPtr) : (ι ⊕ α) → Option OperationPtr
  | .inl state => operationAt state
  | .inr _ => none

/-- A result that identifies no listed operation needs no suffix execution. -/
theorem macroSuffix_eq_pure_of_not_deleted (operationAt : ι → Option OperationPtr)
    (body : ι → Tree (ι ⊕ α)) (operations : List OperationPtr) (initial : ι ⊕ α) :
    (∀ operation ∈ operations, outcomeOperationAt operationAt initial ≠ some operation) →
      macroSuffix operationAt body operations initial = pure initial := by
  apply list_snoc_induction (P := fun operations =>
    (∀ operation ∈ operations, outcomeOperationAt operationAt initial ≠ some operation) →
      macroSuffix operationAt body operations initial = pure initial)
  · intro _; rw [macroSuffix_nil]
  · intro operations operation ih notSelected
    have notSelectedBefore : ∀ op ∈ operations, outcomeOperationAt operationAt initial ≠ some op :=
      fun op member => notSelected op (by simp [member])
    rw [macroSuffix_snoc]
    dsimp only
    rw [ih notSelectedBefore, pure_bind]
    cases initial with
    | inr value => rfl
    | inl state =>
      have different : operationAt state ≠ some operation := notSelected operation (by simp)
      have notSelectedHere : deletionPredicate operationAt operation state = false := by
        simp only [deletionPredicate, beq_eq_false_iff_ne]
        exact different
      simp only [spliceContinuation, notSelectedHere, Bool.false_eq_true, ↓reduceIte]

theorem macroSuffix_return (operationAt : ι → Option OperationPtr)
    (body : ι → Tree (ι ⊕ α)) (operations : List OperationPtr) (value : α) :
    macroSuffix operationAt body operations (.inr value) = pure (.inr value) :=
  macroSuffix_eq_pure_of_not_deleted operationAt body operations (.inr value) (by simp [outcomeOperationAt])

end Veir.DCE
