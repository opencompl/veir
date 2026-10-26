module

public import Veir.Passes.DCE.MacroSteps
import all Veir.Passes.DCE.MacroSteps
import all Veir.Interpreter.CTreeRefinement.Iteration
import all Veir.Interpreter.CTree

public section

namespace Veir.DCE

private theorem list_snoc_induction {P : List α → Prop} (nil : P [])
    (snoc : ∀ xs x, P xs → P (xs ++ [x])) (xs : List α) : P xs := by
  have reversed : ∀ ys : List α, P ys.reverse := by
    intro ys
    induction ys with
    | nil => simpa using nil
    | cons x xs ih => simpa using snoc xs.reverse x ih
  simpa using reversed xs.reverse

/-- Successful grouped execution consists of original steps joined only at
deleted operations. The constructor retains the chronological grouping shape. -/
inductive MacroRun (operationAt : ι → Option OperationPtr) (body : ι → Tree (ι ⊕ α))
    (allowed : OperationPtr → Prop) : ι → (ι ⊕ α) → Prop where
| base {state result} : PureOrErr.CanInterpretTo (body state) (.ok result) →
    MacroRun operationAt body allowed state result
| splice {state middle result operation} :
    MacroRun operationAt body allowed state (.inl middle) →
    operationAt middle = some operation → allowed operation →
    MacroRun operationAt body allowed middle result →
    MacroRun operationAt body allowed state result

theorem MacroRun.weaken {operationAt : ι → Option OperationPtr} {body : ι → Tree (ι ⊕ α)}
    {allowed more : OperationPtr → Prop} {state result}
    (run : MacroRun operationAt body allowed state result)
    (includes : ∀ operation, allowed operation → more operation) :
    MacroRun operationAt body more state result := by
  induction run with
  | base executes => exact .base executes
  | splice first identifies admitted rest ihFirst ihRest =>
    exact .splice ihFirst identifies (includes _ admitted) ihRest

/-- A grouped step's successful outcomes expose its first grouped execution
and, exactly when selected, the execution at its next location. -/
theorem spliceIterBody_success_iff (body : ι → Tree (ι ⊕ α)) (selected : ι → Bool)
    (state : ι) (result : ι ⊕ α) :
    PureOrErr.CanInterpretTo (Tree.spliceIterBody body selected state) (.ok result) ↔
      ∃ middle, PureOrErr.CanInterpretTo (body state) (.ok middle) ∧
        match middle with
        | .inl next => if selected next then
            PureOrErr.CanInterpretTo (body next) (.ok result) else result = .inl next
        | .inr value => result = .inr value := by
  simp only [Tree.spliceIterBody, Bind.bind, PureOrErr.CanInterpretTo.bind_iff]
  simp only [reduceCtorEq, and_false, or_false]
  apply exists_congr
  intro middle
  cases middle with
  | inl next =>
    cases h : selected next
    · simp [h]
    · simp only [h, ↓reduceIte, CTree.CTree.tau1, PureOrErr.CanInterpretTo.tauG_iff]
      constructor
      · rintro ⟨first, _, executes⟩; exact ⟨first, executes⟩
      · rintro ⟨first, executes⟩; exact ⟨first, PUnit.unit, executes⟩
  | inr value => simp

theorem macroBody_finite (operationAt : ι → Option OperationPtr) (body : ι → Tree (ι ⊕ α))
    (finite : ∀ state, PureOrErr (body state)) (operations : List OperationPtr) :
    ∀ state, PureOrErr (macroBody operationAt body operations state) := by
  apply list_snoc_induction (P := fun operations =>
    ∀ state, PureOrErr (macroBody operationAt body operations state))
  · simpa only [macroBody_nil] using finite
  · intro operations operation ih state
    rw [macroBody_snoc]
    unfold Tree.spliceIterBody
    apply PureOrErr.bind _ _ (ih state)
    intro result
    cases result with
    | inl next =>
      dsimp only
      split
      · exact .tau _ _ (fun _ => ih next)
      · exact .ret _
    | inr value => exact .ret _

theorem macroBody_success_run (operationAt : ι → Option OperationPtr)
    (body : ι → Tree (ι ⊕ α)) (operations : List OperationPtr) :
    ∀ state result, PureOrErr.CanInterpretTo (macroBody operationAt body operations state) (.ok result) →
      MacroRun operationAt body (fun operation => operation ∈ operations) state result := by
  apply list_snoc_induction (P := fun operations =>
    ∀ state result, PureOrErr.CanInterpretTo (macroBody operationAt body operations state) (.ok result) →
      MacroRun operationAt body (fun operation => operation ∈ operations) state result)
  · intro state result executes
    rw [macroBody_nil] at executes
    exact .base executes
  · intro operations operation ih state result executes
    rw [macroBody_snoc] at executes
    obtain ⟨middle, first, rest⟩ := (spliceIterBody_success_iff _ _ _ _).mp executes
    have firstRun : MacroRun operationAt body (fun op => op ∈ operations ++ [operation]) state middle :=
      (ih state middle first).weaken (fun op member => by simp [member])
    cases middle with
    | inr value =>
      subst result
      exact firstRun
    | inl next =>
      by_cases selected : deletionPredicate operationAt operation next = true
      · simp only [selected, ↓reduceIte] at rest
        apply MacroRun.splice (operation := operation) firstRun
        · simpa only [deletionPredicate, beq_iff_eq] using selected
        · simp
        · exact (ih next result rest).weaken (fun op member => by simp [member])
      · simp only [selected, Bool.false_eq_true, ↓reduceIte] at rest
        subst result
        exact firstRun

/-- Strict source-list progress survives every chronological grouping. -/
theorem MacroRun.rank_decreases {operationAt : ι → Option OperationPtr}
    {body : ι → Tree (ι ⊕ α)} {allowed eligible : OperationPtr → Prop}
    (rank : OperationPtr → Nat)
    (progress : ∀ state next operation nextOperation,
      operationAt state = some operation → eligible operation →
      PureOrErr.CanInterpretTo (body state) (.ok (.inl next)) →
      operationAt next = some nextOperation → rank nextOperation < rank operation)
    (includes : ∀ operation, allowed operation → eligible operation)
    {state result} (run : MacroRun operationAt body allowed state result) :
    ∀ operation, operationAt state = some operation → eligible operation →
      ∀ next nextOperation, result = .inl next → operationAt next = some nextOperation →
        rank nextOperation < rank operation := by
  induction run with
  | base executes =>
    intro operation identifies admitted next nextOperation resultEq identifiesNext
    rw [resultEq] at executes
    exact progress _ _ _ _ identifies admitted executes identifiesNext
  | @splice state middle result middleOperation first identifies admitted rest ihFirst ihRest =>
    intro operation identifiesStart admittedStart next nextOperation resultEq identifiesNext
    have firstProgress := ihFirst operation identifiesStart admittedStart
      middle middleOperation rfl identifies
    have restProgress := ihRest middleOperation identifies (includes _ admitted)
      next nextOperation resultEq identifiesNext
    omega

theorem macroBody_rank_decreases (operationAt : ι → Option OperationPtr)
    (body : ι → Tree (ι ⊕ α)) (eligible : OperationPtr → Prop) (rank : OperationPtr → Nat)
    (progress : ∀ state next operation nextOperation,
      operationAt state = some operation → eligible operation →
      PureOrErr.CanInterpretTo (body state) (.ok (.inl next)) →
      operationAt next = some nextOperation → rank nextOperation < rank operation)
    (operations : List OperationPtr) (admitted : ∀ operation ∈ operations, eligible operation)
    (state next : ι) (operation nextOperation : OperationPtr)
    (identifies : operationAt state = some operation) (eligibleStart : eligible operation)
    (executes : PureOrErr.CanInterpretTo (macroBody operationAt body operations state) (.ok (.inl next)))
    (identifiesNext : operationAt next = some nextOperation) :
    rank nextOperation < rank operation :=
  (macroBody_success_run operationAt body operations state (.inl next) executes).rank_decreases
    rank progress admitted operation identifies eligibleStart next nextOperation rfl identifiesNext

/-- A successfully grouped next location is outside the entire deletion list.
Strict source-list progress is needed only when execution starts at a deleted
operation; ordinary surviving steps may branch or return freely. -/
theorem macroBody_endpoint_not_deleted (operationAt : ι → Option OperationPtr)
    (body : ι → Tree (ι ⊕ α)) (eligible : OperationPtr → Prop) (rank : OperationPtr → Nat)
    (progress : ∀ state next operation nextOperation,
      operationAt state = some operation → eligible operation →
      PureOrErr.CanInterpretTo (body state) (.ok (.inl next)) →
      operationAt next = some nextOperation → rank nextOperation < rank operation)
    (operations : List OperationPtr) :
    (∀ operation ∈ operations, eligible operation) →
    ∀ state next operation,
      PureOrErr.CanInterpretTo (macroBody operationAt body operations state) (.ok (.inl next)) →
      operationAt next = some operation → operation ∉ operations := by
  apply list_snoc_induction (P := fun operations =>
    (∀ operation ∈ operations, eligible operation) →
    ∀ state next operation,
      PureOrErr.CanInterpretTo (macroBody operationAt body operations state) (.ok (.inl next)) →
      operationAt next = some operation → operation ∉ operations)
  · simp
  · intro operations removed ih admitted state next operation executes identifies
    have admittedBefore : ∀ operation ∈ operations, eligible operation :=
      fun operation member => admitted operation (by simp [member])
    rw [macroBody_snoc] at executes
    obtain ⟨middle, first, rest⟩ := (spliceIterBody_success_iff _ _ _ _).mp executes
    cases middle with
    | inr value => cases rest
    | inl middle =>
      by_cases selected : deletionPredicate operationAt removed middle = true
      · simp only [selected, ↓reduceIte] at rest
        have outsideBefore := ih admittedBefore middle next operation rest identifies
        have identifiesMiddle : operationAt middle = some removed := by
          simpa only [deletionPredicate, beq_iff_eq] using selected
        have decreased := macroBody_rank_decreases operationAt body eligible rank progress
          operations admittedBefore middle next removed operation identifiesMiddle
          (admitted removed (by simp)) rest identifies
        have different : operation ≠ removed := by intro equal; subst operation; omega
        simpa only [List.mem_append, List.mem_singleton, not_or] using And.intro outsideBefore different
      · simp only [selected, Bool.false_eq_true, ↓reduceIte, Sum.inl.injEq] at rest
        subst next
        have outsideBefore := ih admittedBefore state middle operation first identifies
        have different : operation ≠ removed := by
          intro equal
          subst operation
          apply selected
          simp [deletionPredicate, identifies]
        simpa only [List.mem_append, List.mem_singleton, not_or] using And.intro outsideBefore different

end Veir.DCE
