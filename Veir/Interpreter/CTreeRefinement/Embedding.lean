module

public import Veir.Interpreter.CTreeRefinement

import all Veir.Interpreter.CTree
import all CTree.Defs
import all CTree.Iter
import all CTree.Interp

public section

namespace Veir.Tree

open CTree

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

private theorem region_fail_bind (ctx : WfIRContext OpCode) (σ : Type)
    (next : α → RegionTree ctx σ β) : CTree.bind fail next = fail := by
  simp only [fail, CTree.trigger, Bind.bind, CTree.CTree.bind_vis]
  congr 1
  funext impossible
  exact nomatch impossible

private theorem region_ub_bind (ctx : WfIRContext OpCode) (σ : Type)
    (next : α → RegionTree ctx σ β) : CTree.bind ub next = ub := by
  simp only [ub, CTree.trigger, Bind.bind, CTree.CTree.bind_vis]
  congr 1
  funext impossible
  exact nomatch impossible

private theorem region_bind_pure (ctx : WfIRContext OpCode) (σ : Type)
    (value : α) (next : α → RegionTree ctx σ β) :
    CTree.bind (pure value) next = next value := CTree.CTree.bind_ret value next

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
    | ret value => simp only [bind_pure_left, embedRegion_pure, region_bind_pure]
    | tau choice cont =>
      simp only [CTree.CTree.bind_tau, embedRegion_tau, approx_tau_succ]
      congr 1
      funext value
      exact ih (cont value)
    | vis event cont =>
      simp only [CTree.CTree.bind_vis]
      cases event <;>
        rw [embedRegion, unfold_vis, embedRegion, unfold_vis] <;>
        simp [region_fail_bind, region_ub_bind]

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
          simp only [Bind.bind, bind_pure_left, embedRegion_pure, region_bind_pure,
            CTree.CTree.tau1, embedRegion_tau, approx_tau_succ]
          congr 1
          funext value
          rw [CTree.iter, CTree.iter]
          exact ih (body state)
        | inr value => simp only [Bind.bind, bind_pure_left, embedRegion_pure, region_bind_pure]
      | tau choice next =>
        simp only [Bind.bind, CTree.CTree.bind_tau, embedRegion_tau, approx_tau_succ]
        congr 1
        funext value
        exact ih (next value)
      | vis event next =>
        simp only [Bind.bind, CTree.CTree.bind_vis]
        cases event <;>
          rw [embedRegion, unfold_vis, embedRegion, unfold_vis] <;>
          simp [region_fail_bind, region_ub_bind]
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

/-- Re-emit terminal errors with the ordinary CTree event interpreter. This
retains the silent steps inserted by that interpreter. -/
def inflate (tree : Tree α) : Tree α :=
  CTree.interp (fun event => CTree.trigger (SubE := ErrorE ⊕ₑ UBE) event) tree

@[simp] theorem inflate_pure (value : α) : inflate (pure value) = pure value := by
  unfold inflate CTree.interp
  rw [CTree.iter]
  simp

@[simp] theorem inflate_tau (choice : C1In ⊕ FreezeCIn)
    (next : (C1 ⊕ₑ FreezeC) choice → Tree α) :
    inflate (.tauG choice next) =
      .tauG choice (fun value => CTree.CTree.tau1 (inflate (next value))) := by
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

/-- Reifying errors commutes with the silent steps inserted by interpretation. -/
theorem interp_ub_and_error_inflate (tree : Tree α) :
    interp_ub_and_error (inflate tree) = inflate (interp_ub_and_error tree) := by
  ext n
  induction n using Nat.strongRecOn generalizing tree with
  | ind n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      cases tree using CTree.CTree.cases with
      | ret value => simp only [inflate_pure, interp_ub_and_error_pure]
      | tau choice next =>
        simp only [inflate_tau, interp_ub_and_error_tau, approx_tau_succ]
        congr 1
        funext value
        cases n with
        | zero => rfl
        | succ n =>
          simp only [CTree.CTree.tau1, interp_ub_and_error_tau, approx_tau_succ]
          congr 1
          funext ignored
          exact ih n (by omega) (next value)
      | vis event next =>
        cases event with
        | inl event => simp only [error_vis_eq_fail, inflate_fail,
            interp_ub_and_error_fail, inflate_pure]
        | inr event => simp only [ub_vis_eq_ub, inflate_ub,
            interp_ub_and_error_ub, inflate_pure]


/-- The ordinary event interpreter preserves refinement on both sides. -/
theorem refines_inflate {relation : α → β → Prop} {source : Tree α} {target : Tree β}
    (h : Refines relation source target) : Refines relation (inflate source) (inflate target) := by
  unfold Refines at *
  rw [interp_ub_and_error_inflate, interp_ub_and_error_inflate]
  exact Sim.interp _ _ _ h

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

end Veir.Tree
