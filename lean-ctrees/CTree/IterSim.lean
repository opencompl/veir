module

public import CTree.Sim
import all CTree.Defs
import all CTree.Iter
import all CTree.Interp

public section

namespace CTree

variable {EIn CIn : Type u} {E : EIn → Type u} {C : CIn → Type u}

/-- Binding preserves equality through any fixed finite approximation depth. -/
theorem bind_approx_congr {A B : Type u} (n : Nat) (tree : CTree E C A)
    (left right : A → CTree E C B)
    (same : ∀ a m, m ≤ n → (left a).approx m = (right a).approx m) :
    (tree >>= left).approx n = (tree >>= right).approx n := by
  induction n generalizing tree with
  | zero => rfl
  | succ n ih =>
    cases tree with
    | ret value => simpa only [Bind.bind, Pure.pure, CTree.bind_ret] using same value (n + 1) (by omega)
    | tau choice next =>
      simp only [Bind.bind, CTree.bind_tau, approx_tau_succ]
      congr 1
      funext x
      exact ih (next x) (fun a m hm => same a m (by omega))
    | vis event next =>
      simp only [Bind.bind, CTree.bind_vis, approx_vis_succ]
      congr 1
      funext x
      exact ih (next x) (fun a m hm => same a m (by omega))

/-- Guarding recursive calls by a silent step makes the loop equation unique,
independently of the order-theoretic construction used to define `iter`. -/
theorem iter_unique' {I X : Type u} (body : I → CTree E C (I ⊕ X))
    (solution : I → CTree E C X)
    (equation : ∀ i, solution i = (body i >>= fun result => match result with
      | .inl j => CTree.tau1 (solution j)
      | .inr x => pure x)) :
    ∀ i, solution i = iter.{u, u} body i := by
  have approximations : ∀ n i, (solution i).approx n = (iter.{u, u} body i).approx n := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro i
      rw [equation i, iter.eq_def]
      apply bind_approx_congr
      intro result m hm
      cases result with
      | inl j =>
        cases m with
        | zero => rfl
        | succ m =>
          simp only [CTree.tau1_def, approx_tau_succ]
          congr 1
          funext _
          exact ih m (by omega) j
      | inr x => rfl
  intro i
  apply Coinductive.CoInd.ext
  exact fun n => approximations n i

theorem interp_mrec_ret_step {FIn A : Type u} {F : FIn → Type u}
    (handler : (event : EIn) → CTree (E ⊕ₑ F) C (E event)) (value : A) :
    interp_mrec handler (CTree.ret value) = pure value := by
  unfold interp_mrec
  rw [iter.eq_def]
  simp

theorem interp_mrec_tau_step {FIn A : Type u} {F : FIn → Type u}
    (handler : (event : EIn) → CTree (E ⊕ₑ F) C (E event))
    (choice : C1In ⊕ CIn) (next : (C1 ⊕ₑ C) choice → CTree (E ⊕ₑ F) C A) :
    interp_mrec handler (CTree.tauG choice next) =
      CTree.tauG choice (fun x => CTree.tau1 (interp_mrec handler (next x))) := by
  unfold interp_mrec
  rw [iter.eq_def]
  simp

theorem interp_mrec_call_step {FIn A : Type u} {F : FIn → Type u}
    (handler : (event : EIn) → CTree (E ⊕ₑ F) C (E event)) (event : EIn)
    (next : E event → CTree (E ⊕ₑ F) C A) :
    interp_mrec handler (CTree.vis (.inl event) next) =
      CTree.tau1 (interp_mrec handler (handler event >>= next)) := by
  unfold interp_mrec
  rw [iter.eq_def]
  simp

theorem interp_mrec_external_step {FIn A : Type u} {F : FIn → Type u}
    (handler : (event : EIn) → CTree (E ⊕ₑ F) C (E event)) (event : FIn)
    (next : F event → CTree (E ⊕ₑ F) C A) :
    interp_mrec handler (CTree.vis (.inr event) next) =
      CTree.vis event (fun x => CTree.tau1 (interp_mrec handler (next x))) := by
  unfold interp_mrec
  rw [iter.eq_def]
  simp

/-- Recursive interpretation preserves monadic binding exactly. -/
theorem interp_mrec_bind {FIn A B : Type u} {F : FIn → Type u}
    (handler : (event : EIn) → CTree (E ⊕ₑ F) C (E event))
    (tree : CTree (E ⊕ₑ F) C A) (next : A → CTree (E ⊕ₑ F) C B) :
    interp_mrec handler (tree >>= next) =
      (interp_mrec handler tree >>= fun x => interp_mrec handler (next x)) := by
  have approximations : ∀ n (tree : CTree (E ⊕ₑ F) C A),
      (interp_mrec handler (tree >>= next)).approx n =
        (interp_mrec handler tree >>= fun x => interp_mrec handler (next x)).approx n := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro tree
      cases n with
      | zero => rfl
      | succ n =>
        cases tree with
        | ret value =>
          simp only [Bind.bind, Pure.pure, CTree.bind_ret, interp_mrec_ret_step]
        | tau choice continuation =>
          simp only [Bind.bind, CTree.bind_tau, interp_mrec_tau_step,
            CTree.tau1_def, approx_tau_succ]
          congr 1
          funext x
          cases n with
          | zero => rfl
          | succ n =>
            simp only [approx_tau_succ]
            congr 1
            funext _
            exact ih n (by omega) (continuation x)
        | vis event continuation =>
          cases event with
          | inl event =>
            simp only [Bind.bind, CTree.bind_vis, interp_mrec_call_step,
              CTree.tau1_def, CTree.bind_tau, approx_tau_succ]
            congr 1
            funext _
            have reassociated := ih n (by omega) (handler event >>= continuation)
            rw [bind_assoc] at reassociated
            exact reassociated
          | inr event =>
            simp only [Bind.bind, CTree.bind_vis, interp_mrec_external_step,
              CTree.tau1_def, CTree.bind_tau, approx_vis_succ]
            congr 1
            funext x
            cases n with
            | zero => rfl
            | succ n =>
              simp only [approx_tau_succ]
              congr 1
              funext _
              exact ih n (by omega) (continuation x)
  apply Coinductive.CoInd.ext
  exact fun n => approximations n tree

/-- Interpreting an iterated computation preserves iteration. Each continuation
gets an extra silent guard because recursive interpretation also visits the
original iteration's guard. -/
theorem interp_mrec_iter_eq {FIn I X : Type u} {F : FIn → Type u}
    (handler : (event : EIn) → CTree (E ⊕ₑ F) C (E event))
    (body : I → CTree (E ⊕ₑ F) C (I ⊕ X)) (i : I) :
    interp_mrec handler (iter.{u, u} body i) =
      iter.{u, u} (fun j => do
        match ← interp_mrec handler (body j) with
        | .inl k => CTree.tau1 (pure (.inl k))
        | .inr x => pure (.inr x)) i := by
  refine iter_unique' _ (fun j => interp_mrec handler (iter.{u, u} body j)) ?_ i
  intro j
  rw [iter.eq_def, interp_mrec_bind, bind_assoc]
  congr 1
  funext result
  cases result with
  | inl k =>
    simp only [CTree.tau1_def, interp_mrec_tau_step, Pure.pure,
      Bind.bind, CTree.bind_tau, CTree.bind_ret]
  | inr x => simp only [Pure.pure, interp_mrec_ret_step, Bind.bind, CTree.bind_ret]

/-- Extra guards introduced while interpreting a loop can be removed using the
existing synchronized iteration simulation rule. -/
theorem sim_interp_mrec_iter {FIn I X : Type u} {F : FIn → Type u} [HasUB FIn]
    (handler : (event : EIn) → CTree (E ⊕ₑ F) C (E event))
    (body : I → CTree (E ⊕ₑ F) C (I ⊕ X)) (i : I) :
    Sim Eq (interp_mrec handler (iter.{u, u} body i))
        (iter.{u, u} (fun j => interp_mrec handler (body j)) i) ∧
      Sim Eq (iter.{u, u} (fun j => interp_mrec handler (body j)) i)
        (interp_mrec handler (iter.{u, u} body i)) := by
  rw [interp_mrec_iter_eq]
  constructor
  · apply Sim.iter _ _ _ _ rfl
    intro x y equal
    subst y
    conv => rhs; rw [← _root_.bind_pure (interp_mrec handler (body x))]
    apply Sim.bind _ _ _ _ (Sim.refl Eq (fun _ => rfl) (interp_mrec handler (body x)))
    intro t s equal
    subst s
    cases t with
    | inl j =>
      simp only [CTree.tau1_def, Sim.tau_l]
      intro _
      exact (Sim.pure _ _ _).mpr (.inl rfl)
    | inr r => exact (Sim.pure _ _ _).mpr (.inr rfl)
  · apply Sim.iter _ _ _ _ rfl
    intro x y equal
    subst y
    conv => lhs; rw [← _root_.bind_pure (interp_mrec handler (body x))]
    apply Sim.bind _ _ _ _ (Sim.refl Eq (fun _ => rfl) (interp_mrec handler (body x)))
    intro t s equal
    subst s
    cases t with
    | inl j =>
      apply Sim.tau_r _ (.inl .c1) _ _ .unit
      exact (Sim.pure _ _ _).mpr (.inl rfl)
    | inr r => exact (Sim.pure _ _ _).mpr (.inr rfl)

/-- Run at most `n` loop-body steps, stopping immediately on a final result.
A continuation result records the state at the end of the finite batch. -/
def iterSteps {I X : Type u} (body : I → CTree E C (I ⊕ X)) :
    Nat → I → CTree E C (I ⊕ X)
  | 0, i => pure (.inl i)
  | n + 1, i => do
    match ← body i with
    | .inl j => iterSteps body n j
    | .inr x => pure (.inr x)

@[simp]
theorem iterSteps_one {I X : Type u} (body : I → CTree E C (I ⊕ X)) (i : I) :
    iterSteps body 1 i = body i := by
  simp only [iterSteps]
  have continuation : (fun result : I ⊕ X => match result with
      | .inl j => (pure (.inl j) : CTree E C (I ⊕ X))
      | .inr x => pure (.inr x)) = pure := by
    funext result
    cases result <;> rfl
  change (body i >>= _) = body i
  rw [continuation, _root_.bind_pure]

/-- Finite batches retaining the silent guards between their internal steps. -/
def iterGuardedSteps {I X : Type u} (body : I → CTree E C (I ⊕ X)) :
    Nat → I → CTree E C (I ⊕ X)
  | 0, i => pure (.inl i)
  | 1, i => body i
  | n + 2, i => do
    match ← body i with
    | .inl j => CTree.tau1 (iterGuardedSteps body (n + 1) j)
    | .inr x => pure (.inr x)

/-- A positive guarded batch is exactly a finite unfolding of the original loop. -/
theorem iter_unroll_guardedSteps {I X : Type u}
    (body : I → CTree E C (I ⊕ X)) (n : Nat) (i : I) :
    iter.{u, u} body i = (iterGuardedSteps body (n + 1) i >>= fun result => match result with
      | .inl j => CTree.tau1 (iter.{u, u} body j)
      | .inr x => pure x) := by
  induction n generalizing i with
  | zero => exact iter.eq_def body i
  | succ n ih =>
    rw [iterGuardedSteps, bind_assoc]
    rw [iter.eq_def]
    congr 1
    funext result
    cases result with
    | inl j =>
      simp only [Bind.bind, CTree.tau1_def, CTree.bind_tau]
      congr 1
      funext _
      exact ih j
    | inr x => simp

/-- Regrouping a positive number of guarded steps preserves the CTree exactly. -/
theorem iter_guardedSteps_eq {I X : Type u} (body : I → CTree E C (I ⊕ X))
    (batchSize : I → Nat) (positive : ∀ i, 0 < batchSize i) (i : I) :
    iter.{u, u} (fun i => iterGuardedSteps body (batchSize i) i) i = iter.{u, u} body i := by
  symm
  apply iter_unique'
  intro j
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (positive j))
  simpa only [hn, Nat.succ_eq_add_one] using iter_unroll_guardedSteps body n j

/-- Removing finitely many internal silent guards preserves simulation in both
directions. This finite result does not require a coinduction axiom. -/
theorem sim_iterGuardedSteps [HasUB EIn] {I X : Type u}
    (body : I → CTree E C (I ⊕ X)) (n : Nat) (i : I) :
    Sim Eq (iterGuardedSteps body n i) (iterSteps body n i) ∧
      Sim Eq (iterSteps body n i) (iterGuardedSteps body n i) := by
  induction n generalizing i with
  | zero => exact ⟨Sim.refl _ (fun _ => rfl) _, Sim.refl _ (fun _ => rfl) _⟩
  | succ n ih =>
    cases n with
    | zero =>
      simp only [Nat.zero_add, iterGuardedSteps, iterSteps_one]
      exact ⟨Sim.refl _ (fun _ => rfl) _, Sim.refl _ (fun _ => rfl) _⟩
    | succ n =>
      rw [iterGuardedSteps, iterSteps]
      have same := Sim.refl Eq (fun _ => rfl) (body i)
      constructor
      · apply Sim.bind _ _ _ _ same
        intro t s equal
        subst s
        cases t with
        | inl j =>
          simp only [CTree.tau1_def, Sim.tau_l]
          intro _
          exact (ih j).1
        | inr x => exact Sim.refl _ (fun _ => rfl) _
      · apply Sim.bind _ _ _ _ same
        intro t s equal
        subst s
        cases t with
        | inl j =>
          apply Sim.tau_r _ (.inl .c1) _ _ .unit
          exact (ih j).2
        | inr x => exact Sim.refl _ (fun _ => rfl) _

/-- Every positive state-dependent finite grouping is equivalent to the original
loop under simulation. `Sim.iter` handles the grouped bodies; the guarded grouping
is strongly equal to the original loop. -/
theorem sim_iterSteps_iter [HasUB EIn] {I X : Type u}
    (body : I → CTree E C (I ⊕ X)) (batchSize : I → Nat)
    (positive : ∀ i, 0 < batchSize i) (i : I) :
    Sim Eq (iter.{u, u} (fun j => iterSteps body (batchSize j) j) i) (iter.{u, u} body i) ∧
      Sim Eq (iter.{u, u} body i) (iter.{u, u} (fun j => iterSteps body (batchSize j) j) i) := by
  have grouped := iter_guardedSteps_eq body batchSize positive i
  constructor
  · rw [← grouped]
    apply Sim.iter _ _ _ _ rfl
    intro x y equal
    subst y
    exact ((sim_iterGuardedSteps body (batchSize x) x).2).mono
      (fun a b equal => by subst b; cases a <;> first | exact Sum.LiftRel.inl rfl | exact Sum.LiftRel.inr rfl)
  · rw [← grouped]
    apply Sim.iter _ _ _ _ rfl
    intro x y equal
    subst y
    exact ((sim_iterGuardedSteps body (batchSize x) x).1).mono
      (fun a b equal => by subst b; cases a <;> first | exact Sum.LiftRel.inl rfl | exact Sum.LiftRel.inr rfl)

/-- Synchronized local simulations compose over every finite batch. -/
theorem Sim.iterSteps [HasUB EIn] {I J X Y : Type u}
    (reachable : I → J → Prop) (results : X → Y → Prop)
    (target : I → CTree E C (I ⊕ X)) (source : J → CTree E C (J ⊕ Y))
    (step : ∀ i j, reachable i j →
      Sim (Sum.LiftRel reachable results) (target i) (source j))
    (n : Nat) {i : I} {j : J} (initial : reachable i j) :
    Sim (Sum.LiftRel reachable results)
      (iterSteps target n i) (iterSteps source n j) := by
  induction n generalizing i j with
  | zero => exact (Sim.pure _ _ _).mpr (.inl initial)
  | succ n ih =>
    unfold _root_.CTree.iterSteps
    apply Sim.bind _ _ _ _ (step i j initial)
    intro t s related
    cases related with
    | inl h => exact ih h
    | inr h => exact (Sim.pure _ _ _).mpr (.inr h)

/-- Positive finite batching follows from the existing synchronized `Sim.iter`.
Batch schedules depend on each machine's own state, allowing instruction-location
based regrouping without extending the trusted simulation theory. -/
theorem Sim.iter_batched [HasUB EIn] {I J X Y : Type u}
    (target : I → CTree E C (I ⊕ X)) (source : J → CTree E C (J ⊕ Y))
    (targetBatch : I → Nat) (sourceBatch : J → Nat)
    (targetPositive : ∀ i, 0 < targetBatch i) (sourcePositive : ∀ j, 0 < sourceBatch j)
    (reachable : I → J → Prop) (results : X → Y → Prop)
    (step : ∀ i j, reachable i j →
      Sim (Sum.LiftRel reachable results)
        (_root_.CTree.iterSteps target (targetBatch i) i) (_root_.CTree.iterSteps source (sourceBatch j) j))
    {i : I} {j : J} (initial : reachable i j) :
    Sim results (_root_.CTree.iter.{u, u} target i) (_root_.CTree.iter.{u, u} source j) := by
  have batches := Sim.iter (fun i => _root_.CTree.iterSteps target (targetBatch i) i)
    (fun j => _root_.CTree.iterSteps source (sourceBatch j) j) i j initial step
  have targetGrouping := (sim_iterSteps_iter target targetBatch targetPositive i).2
  have sourceGrouping := (sim_iterSteps_iter source sourceBatch sourcePositive j).1
  exact Sim.trans (Sim.trans targetGrouping batches
    (fun _ _ _ equal related => equal ▸ related)) sourceGrouping
    (fun _ _ _ related equal => equal ▸ related)

/-- A local invariant allowing a positive finite number of body steps on each
side. Positivity prevents an invariant justified solely by zero-step stuttering. -/
structure IterBatchedSimulation [HasUB EIn] {I J X Y : Type u}
    (target : I → CTree E C (I ⊕ X)) (source : J → CTree E C (J ⊕ Y))
    (reachable : I → J → Prop) (results : X → Y → Prop) where
  targetBatchSize : I → J → Nat
  sourceBatchSize : I → J → Nat
  targetPositive : ∀ i j, reachable i j → 0 < targetBatchSize i j
  sourcePositive : ∀ i j, reachable i j → 0 < sourceBatchSize i j
  step : ∀ i j, reachable i j →
    Sim (Sum.LiftRel reachable results)
      (iterSteps target (targetBatchSize i j) i)
      (iterSteps source (sourceBatchSize i j) j)

/-- Unit batches recover the existing synchronized iteration premise. -/
def IterBatchedSimulation.of_step [HasUB EIn] {I J X Y : Type u}
    {target : I → CTree E C (I ⊕ X)} {source : J → CTree E C (J ⊕ Y)}
    {reachable : I → J → Prop} {results : X → Y → Prop}
    (step : ∀ i j, reachable i j →
      Sim (Sum.LiftRel reachable results) (target i) (source j)) :
    IterBatchedSimulation target source reachable results where
  targetBatchSize := fun _ _ => 1
  sourceBatchSize := fun _ _ => 1
  targetPositive := by intros; decide
  sourcePositive := by intros; decide
  step := by simpa only [iterSteps_one] using step

end CTree
