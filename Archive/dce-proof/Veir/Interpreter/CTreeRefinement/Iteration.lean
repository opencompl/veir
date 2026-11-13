module

public import Veir.Interpreter.CTreeRefinement

import all Veir.Interpreter.CTreeRefinement
import all CTree.Defs
import all CTree.Iter

public section

namespace Veir.Tree

open CTree

/-- Error-aware iteration closure for possibly infinite executions. -/
def IterationCompatible : Prop :=
  ∀ {ι κ α β : Type} (stateRelation : ι → κ → Prop) (relation : α → β → Prop)
    (bodySource : ι → Tree (ι ⊕ α)) (bodyTarget : κ → Tree (κ ⊕ β)),
    (∀ source target, stateRelation source target →
      Refines (Sum.LiftRel stateRelation relation) (bodySource source) (bodyTarget target)) →
    ∀ source target, stateRelation source target →
      Refines relation (CTree.iter bodySource source) (CTree.iter bodyTarget target)

/-- Refining loop bodies produce refining executions, with UB and failure
following the same convention as `Tree.Refines`. This is the explicit iteration
compositionality assumption; no transitivity assumption is made. -/
axiom refines_iter : IterationCompatible

/-- Reify a loop body's terminal errors while retaining its next-state results. -/
def interpIterBody (body : ι → Tree (ι ⊕ α)) (state : ι) : Tree (ι ⊕ Interp α) := do
  match ← interp_ub_and_error (body state) with
  | .ok (.inl state) => return .inl state
  | .ok (.inr value) => return .inr (.ok value)
  | .fail error => return .inr (.fail error)
  | .ub error => return .inr (.ub error)

private theorem iter_interpIterBody (body : ι → Tree (ι ⊕ α)) (state : ι) :
    CTree.iter (interpIterBody body) state = (do
      match ← interp_ub_and_error (body state) with
      | .ok (.inl state) => CTree.CTree.tau1 (CTree.iter (interpIterBody body) state)
      | .ok (.inr value) => pure (.ok value)
      | .fail error => pure (.fail error)
      | .ub error => pure (.ub error)) := by
  rw [CTree.iter]
  simp only [interpIterBody, bind_assoc]
  congr 1
  funext result
  cases result with
  | fail error => simp
  | ub error => simp
  | ok result => cases result <;> simp

/-- Reifying terminal errors commutes with iteration, including infinite loops. -/
theorem interp_ub_and_error_iter (body : ι → Tree (ι ⊕ α)) (state : ι) :
    interp_ub_and_error (CTree.iter body state) =
      CTree.iter (interpIterBody body) state := by
  have hnext : ∀ n (tree : Tree (ι ⊕ α)),
      (interp_ub_and_error (tree >>= fun
        | .inl state => CTree.CTree.tau1 (CTree.iter body state)
        | .inr value => pure value)).approx n =
      ((interp_ub_and_error tree >>= fun
        | .ok (.inl state) => CTree.CTree.tau1 (CTree.iter (interpIterBody body) state)
        | .ok (.inr value) => pure (.ok value)
        | .fail error => pure (.fail error)
        | .ub error => pure (.ub error))).approx n := by
    intro n
    induction n with
    | zero => intro tree; rfl
    | succ n ih =>
      intro tree
      cases tree using CTree.CTree.cases with
      | ret result =>
        cases result with
        | inl state =>
          simp only [Bind.bind, bind_pure_left,
            interp_ub_and_error_pure, CTree.CTree.tau1, interp_ub_and_error_tau,
            approx_tau_succ]
          congr 1
          funext value
          rw [CTree.iter, iter_interpIterBody]
          exact ih (body state)
        | inr value => simp [Bind.bind]
      | tau choice next =>
        simp only [Bind.bind, CTree.CTree.bind_tau, interp_ub_and_error_tau,
          approx_tau_succ]
        congr 1
        funext value
        exact ih (next value)
      | vis event next =>
        cases event <;>
          simp only [Bind.bind, CTree.CTree.bind_vis] <;>
          rw [interp_ub_and_error, unfold_vis, interp_ub_and_error, unfold_vis] <;>
          simp
  ext n
  rw [CTree.iter, iter_interpIterBody]
  exact hnext n (body state)

/-- Combine a loop step with its successor when the successor is marked for
splicing. Retaining the intermediate silent step preserves the original tree. -/
def spliceIterBody (body : ι → Tree (ι ⊕ α)) (splice : ι → Bool)
    (state : ι) : Tree (ι ⊕ α) := do
  match ← body state with
  | .inl next =>
    if splice next then CTree.CTree.tau1 (body next) else pure (.inl next)
  | .inr value => pure (.inr value)

/-- Grouping a selected successor into the current iteration preserves all
choices, terminal errors, and silent steps, including on infinite executions. -/
theorem iter_spliceIterBody (body : ι → Tree (ι ⊕ α)) (splice : ι → Bool) (state : ι) :
    CTree.iter body state = CTree.iter (spliceIterBody body splice) state := by
  let next : Bool → ι ⊕ α → Tree α := fun enabled result =>
    match result with
    | .inl state =>
      if enabled && splice state then
        CTree.CTree.tau1 (body state >>= fun
          | .inl state => CTree.CTree.tau1 (CTree.iter (spliceIterBody body splice) state)
          | .inr value => pure value)
      else CTree.CTree.tau1 (CTree.iter (spliceIterBody body splice) state)
    | .inr value => pure value
  have hstep (state : ι) :
      CTree.iter (spliceIterBody body splice) state = body state >>= next true := by
    rw [CTree.iter]
    simp only [spliceIterBody, bind_assoc]
    congr 1
    funext result
    cases result with
    | inr value => simp [next]
    | inl state =>
      simp only [next, Bool.true_and]
      split <;> simp [Bind.bind, CTree.CTree.tau1] <;> rfl
  have hnext : ∀ n enabled (tree : Tree (ι ⊕ α)),
      ((tree >>= fun
        | .inl state => CTree.CTree.tau1 (CTree.iter body state)
        | .inr value => pure value)).approx n = (tree >>= next enabled).approx n := by
    intro n
    induction n with
    | zero => intro enabled tree; rfl
    | succ n ih =>
      intro enabled tree
      cases tree using CTree.CTree.cases with
      | ret result =>
        cases result with
        | inr value => simp [next, Bind.bind]
        | inl state =>
          simp only [Bind.bind, bind_pure_left]
          dsimp only [next]
          split
          · simp only [CTree.CTree.tau1, approx_tau_succ]
            congr 1
            funext value
            rw [CTree.iter]
            exact ih false (body state)
          · simp only [CTree.CTree.tau1, approx_tau_succ]
            congr 1
            funext value
            rw [CTree.iter, hstep]
            exact ih true (body state)
      | tau choice cont =>
        simp only [Bind.bind, CTree.CTree.bind_tau, approx_tau_succ]
        congr 1
        funext value
        exact ih enabled (cont value)
      | vis event cont =>
        simp only [Bind.bind, CTree.CTree.bind_vis, approx_vis_succ]
        congr 1
        funext value
        exact ih enabled (cont value)
  ext n
  rw [CTree.iter, hstep]
  exact hnext n true (body state)

/-- Group successors selected by a finite sequence of deletion predicates. -/
def spliceIterBodies (body : ι → Tree (ι ⊕ α)) (splices : List (ι → Bool)) :
    ι → Tree (ι ⊕ α) :=
  splices.foldl spliceIterBody body

/-- A finite sequence of successor groupings preserves exact execution trees.
Only equality transitivity is used; no transitivity law for refinement is needed. -/
theorem iter_spliceIterBodies (body : ι → Tree (ι ⊕ α))
    (splices : List (ι → Bool)) (state : ι) :
    CTree.iter body state = CTree.iter (spliceIterBodies body splices) state := by
  induction splices generalizing body with
  | nil => rfl
  | cons splice splices ih =>
    exact (iter_spliceIterBody body splice state).trans (ih (spliceIterBody body splice))

end Veir.Tree
