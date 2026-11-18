module

public import Veir.Interpreter.CTreeRefinement.ClosedCFG

import all Veir.Interpreter.CTree
import all CTree.Defs
import all CTree.Iter
import all CTree.Interp
import all Veir.Interpreter.CTreeRefinement.ClosedCFG

public section

/-!
# Embedding closed trees into region trees

`embedRegion` views a closed `Tree` as a `RegionTree` that never calls a region, without adding
silent steps. It commutes with `bind` and `iter`, and event handlers applied to an embedded tree
reduce to `inflate`.
-/

open CTree

namespace Veir.CTree

/-- Embed a closed interpreter tree into the region-effect signature without
introducing additional silent steps. -/
def embedRegion (ctx : WfIRContext OpCode) (σ : Type) (tree : Tree α) : RegionTree ctx σ α :=
  match tree.unfold with
  | .ret value => pure value
  | .tau choice next => .tauG choice (fun value => embedRegion ctx σ (next value))
  | .vis (.inl _) _ => fail
  | .vis (.inr _) _ => ub
partial_fixpoint

@[simp]
theorem embedRegion_pure (ctx : WfIRContext OpCode) (σ : Type) (value : α) :
    embedRegion ctx σ (pure value) = pure value := by
  rw [embedRegion]
  simp

@[simp]
theorem embedRegion_tau (ctx : WfIRContext OpCode) (σ : Type)
    (choice : C1In ⊕ FreezeCIn) (next : (C1 ⊕ₑ FreezeC) choice → Tree α) :
    embedRegion ctx σ (.tauG choice next) =
      .tauG choice (fun value => embedRegion ctx σ (next value)) := by
  rw [embedRegion]
  simp

@[simp]
theorem embedRegion_fail (ctx : WfIRContext OpCode) (σ : Type) :
    embedRegion ctx σ (fail : Tree α) = fail := by
  rw [embedRegion]
  simp [fail, CTree.trigger, Bind.bind]

@[simp]
theorem embedRegion_ub (ctx : WfIRContext OpCode) (σ : Type) :
    embedRegion ctx σ (ub : Tree α) = ub := by
  rw [embedRegion]
  simp [ub, CTree.trigger, Bind.bind]

/-- Structural embedding commutes with sequencing. -/
theorem embedRegion_bind (ctx : WfIRContext OpCode) (σ : Type)
    (tree : Tree α) (next : α → Tree β) :
    embedRegion ctx σ (CTree.bind tree next) =
      CTree.bind (embedRegion ctx σ tree) (fun value => embedRegion ctx σ (next value)) := by
  ext n
  induction n generalizing tree with
  | zero => rfl
  | succ n ih =>
    cases tree using CTree.CTree.cases with
    | ret value => simp only [_root_.CTree.bind_pure, embedRegion_pure]
    | tau choice cont =>
      simp only [CTree.CTree.bind_tau, embedRegion_tau, approx_tau_succ]
      congr 1
      funext value
      exact ih (cont value)
    | vis event cont =>
      simp only [CTree.CTree.bind_vis]
      cases event <;>
        rw [embedRegion, unfold_vis, embedRegion, unfold_vis] <;>
        simp

/-- Structural event embedding commutes with potentially infinite iteration. -/
theorem embedRegion_iter (ctx : WfIRContext OpCode) (σ : Type)
    (body : ι → Tree (ι ⊕ α)) (state : ι) :
    embedRegion ctx σ (CTree.iter body state) =
      CTree.iter (fun state => embedRegion ctx σ (body state)) state := by
  have hnext : ∀ n (tree : Tree (ι ⊕ α)),
      (embedRegion ctx σ (tree >>= fun
        | .inl state => CTree.CTree.tau1 (CTree.iter body state)
        | .inr value => pure value)).approx n =
      ((embedRegion ctx σ tree >>= fun
        | .inl state => CTree.CTree.tau1
            (CTree.iter (fun state => embedRegion ctx σ (body state)) state)
        | .inr value => pure value)).approx n := by
    intro n
    induction n with
    | zero => intro tree; rfl
    | succ n ih =>
      intro tree
      cases tree using CTree.CTree.cases with
      | ret result =>
        cases result with
        | inl state =>
          simp only [Bind.bind, _root_.CTree.bind_pure, embedRegion_pure,
            CTree.CTree.tau1, embedRegion_tau, approx_tau_succ]
          congr 1
          funext value
          rw [CTree.iter, CTree.iter]
          exact ih (body state)
        | inr value => simp only [Bind.bind, _root_.CTree.bind_pure, embedRegion_pure]
      | tau choice next =>
        simp only [Bind.bind, CTree.CTree.bind_tau, embedRegion_tau, approx_tau_succ]
        congr 1
        funext value
        exact ih (next value)
      | vis event next =>
        simp only [Bind.bind, CTree.CTree.bind_vis]
        cases event <;>
          rw [embedRegion, unfold_vis, embedRegion, unfold_vis] <;>
          simp
  ext n
  rw [CTree.iter, CTree.iter]
  exact hnext n (body state)

/-- Interpreting only terminal error events into a region signature is the
structural embedding of the same interpretation in the closed signature. -/
theorem interp_embedRegion (ctx : WfIRContext OpCode) (σ : Type) (tree : Tree α) :
    CTree.interp (fun event => CTree.trigger (SubE := ErrorE ⊕ₑ UBE) event) tree =
      embedRegion ctx σ
        (CTree.interp (fun event => CTree.trigger (SubE := ErrorE ⊕ₑ UBE) event) tree) := by
  unfold CTree.interp
  rw [embedRegion_iter]
  congr 1
  funext current
  cases current.unfold with
  | ret value => simp only [embedRegion_pure]
  | tau choice next => simp only [embedRegion_tau, embedRegion_pure]
  | vis event next =>
    cases event <;>
      simp only [CTree.trigger, Bind.bind, CTree.CTree.bind_vis] <;>
      rw [embedRegion, unfold_vis] <;>
      simp only [fail, ub, CTree.trigger, Bind.bind, CTree.CTree.bind_vis] <;>
      congr 1 <;>
      funext impossible <;>
      exact nomatch impossible

private theorem error_vis_eq_fail (event : ErrorEIn)
    (next : (ErrorE ⊕ₑ UBE) (.inl event) → Tree α) :
    .vis (.inl event) next = (fail : Tree α) := by
  cases event
  simp only [fail, CTree.trigger, Bind.bind, CTree.CTree.bind_vis]
  congr 1
  funext impossible
  exact nomatch impossible

private theorem ub_vis_eq_ub (event : UBEIn)
    (next : (ErrorE ⊕ₑ UBE) (.inr event) → Tree α) :
    .vis (.inr event) next = (ub : Tree α) := by
  cases event
  simp only [ub, CTree.trigger, Bind.bind, CTree.CTree.bind_vis]
  congr 1
  funext impossible
  exact nomatch impossible

variable {EIn CIn : Type} {E : EIn → Type} {C : CIn → Type}

private theorem raw_bind_pure (value : α) (next : α → CTree E C β) :
    CTree.bind (pure value) next = next value := CTree.CTree.bind_ret value next

private theorem raw_bind_assoc (tree : CTree E C α)
    (next : α → CTree E C β) (last : β → CTree E C γ) :
    CTree.bind (CTree.bind tree next) last =
      CTree.bind tree (fun value => CTree.bind (next value) last) :=
  CTree.bind_assoc tree next last

private def loopNext (body : ι → CTree E C (ι ⊕ α)) :
    ι ⊕ α → CTree E C α := fun result =>
  match result with
  | .inl state => CTree.CTree.tau1 (CTree.iter body state)
  | .inr value => pure value

private theorem iter_unroll (body : ι → CTree E C (ι ⊕ α)) (state : ι) :
    CTree.iter body state = CTree.bind (body state) (loopNext body) := by
  rw [CTree.iter]
  rfl

/-- Renaming a loop's internal states preserves its tree when every body agrees
under the renaming. This also covers non-injective state maps. -/
theorem iter_mapState
    (body : ι → CTree E C (ι ⊕ α))
    (body' : κ → CTree E C (κ ⊕ α)) (mapState : ι → κ)
    (hbody : ∀ state, body' (mapState state) = Sum.map mapState id <$> body state)
    (state : ι) : CTree.iter body' (mapState state) = CTree.iter body state := by
  have hnext : ∀ n (tree : CTree E C (ι ⊕ α)),
      (CTree.bind tree (fun result => loopNext body' (Sum.map mapState id result))).approx n =
      (CTree.bind tree (loopNext body)).approx n := by
    intro n
    induction n with
    | zero => intro tree; rfl
    | succ n ih =>
      intro tree
      cases tree using CTree.CTree.cases with
      | ret result =>
        cases result with
        | inr value => simp only [Sum.map_inr, loopNext, id_eq, raw_bind_pure]
        | inl state =>
          simp only [Sum.map_inl, loopNext, raw_bind_pure,
            CTree.CTree.tau1, approx_tau_succ]
          congr 1
          funext value
          rw [iter_unroll body', hbody, iter_unroll body]
          simpa only [map_eq_pure_bind, Bind.bind, raw_bind_assoc, raw_bind_pure] using ih (body state)
      | tau choice cont =>
        simp only [CTree.CTree.bind_tau, approx_tau_succ]
        congr 1
        funext value
        exact ih (cont value)
      | vis event cont =>
        simp only [CTree.CTree.bind_vis, approx_vis_succ]
        congr 1
        funext value
        exact ih (cont value)
  ext n
  rw [iter_unroll body', hbody, iter_unroll body]
  simpa only [map_eq_pure_bind, Bind.bind, raw_bind_assoc, raw_bind_pure] using hnext n (body state)

/-- A second region event handler cannot introduce region requests when its
input is a structurally embedded closed tree. -/
theorem interp_embedRegion_closed
    (sourceCtx targetCtx : WfIRContext OpCode) (sourceState targetState : Type)
    (handler : (event : RunRegionEIn sourceCtx sourceState ⊕ (ErrorEIn ⊕ UBEIn)) →
      RegionTree targetCtx targetState ((RunRegionE sourceCtx sourceState ⊕ₑ (ErrorE ⊕ₑ UBE)) event))
    (herrors : ∀ event, handler (.inr event) =
      CTree.trigger (SubE := ErrorE ⊕ₑ UBE) event)
    (tree : Tree α) :
    CTree.interp handler (embedRegion sourceCtx sourceState tree) =
      embedRegion targetCtx targetState (inflate tree) := by
  rw [show embedRegion targetCtx targetState (inflate tree) =
      CTree.interp (fun event => CTree.trigger (SubE := ErrorE ⊕ₑ UBE) event) tree from
        (interp_embedRegion targetCtx targetState tree).symm]
  unfold CTree.interp
  apply iter_mapState (mapState := embedRegion sourceCtx sourceState)
  intro current
  cases current using CTree.CTree.cases with
  | ret value =>
    simp only [embedRegion_pure]
    simp only [Pure.pure, unfold_ret, map_eq_pure_bind,
      Bind.bind, CTree.CTree.bind_ret]
    rfl
  | tau choice next =>
    simp only [embedRegion_tau, unfold_tauG, map_eq_pure_bind, Bind.bind,
      CTree.CTree.bind_tau, raw_bind_pure]
    rfl
  | vis event next =>
    cases event with
    | inl event =>
      rw [error_vis_eq_fail]
      simp only [embedRegion_fail]
      simp [fail, CTree.trigger, Bind.bind, CTree.CTree.bind_vis, herrors]
      simp only [map_eq_pure_bind, Bind.bind, CTree.CTree.bind_vis]
      congr 1
      funext impossible
      exact nomatch impossible
    | inr event =>
      rw [ub_vis_eq_ub]
      simp only [embedRegion_ub]
      simp [ub, CTree.trigger, Bind.bind, CTree.CTree.bind_vis, herrors]
      simp only [map_eq_pure_bind, Bind.bind, CTree.CTree.bind_vis]
      congr 1
      funext impossible
      exact nomatch impossible

/-! ## `inflate` on finished trees -/

@[simp] theorem inflate_pure (value : α) : inflate (pure value : Tree α) = pure value := by
  unfold inflate CTree.interp
  rw [CTree.iter]
  simp

@[simp] theorem inflate_fail : inflate (fail : Tree α) = fail := by
  unfold inflate CTree.interp
  rw [CTree.iter]
  simp [fail, CTree.trigger, Bind.bind]
  congr 1
  funext impossible
  exact nomatch impossible

@[simp] theorem inflate_ub : inflate (ub : Tree α) = ub := by
  unfold inflate CTree.interp
  rw [CTree.iter]
  simp [ub, CTree.trigger, Bind.bind]
  congr 1
  funext impossible
  exact nomatch impossible

/-- `inflate` leaves the lift of an `Interp` outcome alone. -/
@[simp] theorem inflate_monadLift (outcome : Interp α) :
    inflate (monadLift outcome : Tree α) = monadLift outcome := by
  cases outcome <;> simp [monadLift, MonadLift.monadLift]

end Veir.CTree
