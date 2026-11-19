import Veir.Interpreter.CTreeStateRefinement

/-!
A Boolean event can be matched by guessing its response before issuing the event.
An interpreter that emits a visible tick before choosing the response distinguishes the trees.
-/

namespace CTreeInterpTest

open CTree LTS Tower
open Veir.CTree (interp_ret_eq interp_vis_eq interp_tau_eq)

private abbrev Bits (_ : Unit) := Bool
private abbrev Ticks (_ : Unit) := Unit
private abbrev Input := CTree Bits Bits
private abbrev Output := CTree Ticks Bits

private def ask : Input Bool := .vis () fun x => .ret x
private def guess : Input Bool := .tauG (.inr ()) fun b => .vis () fun _ => .ret b
private def handler (_ : Unit) : Output Bool :=
  .vis () fun _ => .tauG (.inr ()) fun b => .ret b

private theorem input_sim : Sim Eq ask guess := by
  rw [CTree.Sim, LTS.Sim, gfp_iff_ternary_rel]
  intro R
  apply Chain.apply_ternary_rel _ CTree.MuSimF.mon R
  apply LTS.MuSimF.sim
  constructor
  · intro l t' h
    obtain ⟨b, heq⟩ := trans_vis _ _ _ _ h
    cases heq
    obtain rfl := trans_vis' h
    refine ⟨_, _, ⟨_, Star.once _ (CTree.Trans.tau (C := Bits) (i := .inr ()) (x := b)), CTree.Trans.vis⟩,
      .obs _ _ (.eff _ _), ?_⟩
    exact CTree.MuSimF.ret' Eq R b b rfl
  · intro t' h
    obtain ⟨_, heq⟩ := trans_vis _ _ _ _ h
    cases heq

private theorem no_ub (t : Output Bool) : ¬t.UB := by
  unfold CTree.UB
  split <;> exact id

/-- A weak observable step out of a choice must take one of the choice branches. -/
private theorem choose_before {i : C1In ⊕ Unit} {k : (C1 ⊕ₑ Bits) i → Output Bool}
    {mid next : Output Bool} {l : CTree.Obs (E := Ticks) (α := Bool)}
    (path : (CTree.Trans .tau)^* (.tauG i k) mid) (step : CTree.Trans (.obs l) mid next) :
    ∃ b, (CTree.Trans .tau)^* (k b) mid := by
  cases path with
  | base => cases trans_tau step
  | iter _ _ _ first rest =>
    obtain ⟨b, rfl⟩ := trans_tau' first
    exact ⟨b, rest⟩

private theorem tick_stays {k : Unit → Output Bool} {mid : Output Bool}
    (path : (CTree.Trans .tau)^* (.vis () k) mid) : mid = .vis () k := by
  cases path with
  | base => rfl
  | iter _ _ _ first _ =>
    obtain ⟨_, heq⟩ := trans_vis _ _ _ _ first
    cases heq

private def afterTick (f : Bool → Bool) : Output Bool :=
  .tauG (.inr ()) fun x => .tau1 (.ret (f x))

private def tick (f : Bool → Bool) : Output Bool := .vis () fun _ => afterTick f

private theorem output_not_sim : ¬ Sim Eq (interp handler ask) (interp handler guess) := by
  intro h
  have interp_pure (b : Bool) : interp handler (pure b : Input Bool) = pure b :=
    interp_ret_eq handler b
  have left : interp handler ask = tick id := by
    simp [ask, tick, afterTick, interp_vis_eq, handler, Bind.bind, interp_pure]
  have right : interp handler guess =
      .tauG (.inr ()) (fun b => .tau1 (tick (fun _ => b))) := by
    simp [guess, interp_tau_eq, tick, afterTick, interp_vis_eq, handler, Bind.bind, interp_pure]
  rw [left, right] at h
  have h := gfp_apply_ternary_rel _ _ _ _ h
  rcases LTS.MuSimF.true_iff.mp h with hs | ⟨_, _, hu⟩
  · obtain ⟨_, next, ⟨mid, path, step⟩, label, rest⟩ :=
      hs.1 (.eff () ()) (afterTick id) CTree.Trans.vis
    cases label with
    | obs _ _ matched =>
      cases matched with
      | eff =>
        obtain ⟨b, path⟩ := choose_before path step
        obtain ⟨_, path⟩ := choose_before path step
        obtain rfl := tick_stays path
        obtain rfl := trans_vis' step
        have disagree := (Sim.tau_l Eq _ _ _).mp rest (!b)
        have disagree := (Sim.tau_l Eq _ _ _).mp disagree PUnit.unit
        obtain ⟨_, disagree⟩ := (Sim.pure_tau Eq _ _ _).mp disagree
        obtain ⟨_, disagree⟩ := (Sim.pure_tau Eq _ _ _).mp disagree
        have impossible := (Sim.ret Eq _ _).mp disagree
        cases b <;> contradiction
  · exact no_ub _ hu

/-- A UB-preserving handler can distinguish two trees related by simulation. -/
theorem interp_counterexample :
    ∃ (h : (i : Unit) → Output (Bits i)) (t u : Input Bool),
      (∀ i, HasUB.isUB i → (h i).UB) ∧ Sim Eq t u ∧ ¬ Sim Eq (interp h t) (interp h u) :=
  ⟨handler, ask, guess, fun _ ub => False.elim ub, input_sim, output_not_sim⟩

/-- info: 'CTreeInterpTest.interp_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interp_counterexample

end CTreeInterpTest

/-- info: 'Veir.CTree.sim_interp_mrec_interpretOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Veir.CTree.sim_interp_mrec_interpretOp

/-- info: 'Veir.CTree.sim_interpretOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Veir.CTree.sim_interpretOp
