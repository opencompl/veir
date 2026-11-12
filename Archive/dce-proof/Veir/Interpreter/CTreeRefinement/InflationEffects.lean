module

public import Veir.Interpreter.CTreeRefinement.Embedding
public import Veir.Interpreter.CTreeRefinement.Effects

import all Veir.Interpreter.CTree
import all CTree.Defs

public section

namespace Veir.Tree

open _root_.CTree

/-- Re-emitting terminal errors adds only finite silent padding to finite trees. -/
theorem pureOrErr_inflate {tree : Tree α} (hfinite : PureOrErr tree) :
    PureOrErr (inflate tree) := by
  induction hfinite with
  | ret value => simp
  | tau choice next _ ih =>
    rw [inflate_tau]
    apply PureOrErr.tau
    intro value
    exact PureOrErr.tau _ _ (fun _ => ih value)
  | @fail next =>
    have heq : CTree.CTree.vis (Subeffect.mapEff ErrorE (ErrorE ⊕ₑ UBE) ErrorEIn.mk) next =
        (fail : Tree α) := by
      simp only [fail, CTree.trigger, Bind.bind, CTree.CTree.bind_vis]
      congr 1
      funext impossible
      exact nomatch impossible
    rw [heq, inflate_fail]
    exact PureOrErr.fail_tree
  | @ub next =>
    have heq : CTree.CTree.vis (Subeffect.mapEff UBE (ErrorE ⊕ₑ UBE) UBEIn.mk) next =
        (ub : Tree α) := by
      simp only [ub, CTree.trigger, Bind.bind, CTree.CTree.bind_vis]
      congr 1
      funext impossible
      exact nomatch impossible
    rw [heq, inflate_ub]
    exact PureOrErr.ub_tree

/-- Silent padding preserves the exact outcomes of finite closed trees. -/
theorem canInterpretTo_inflate_iff {tree : Tree α} (hfinite : PureOrErr tree)
    (outcome : Interp α) :
    PureOrErr.CanInterpretTo (inflate tree) outcome ↔ PureOrErr.CanInterpretTo tree outcome := by
  induction hfinite with
  | ret value => simp
  | tau choice next _ ih =>
    simp only [inflate_tau, PureOrErr.CanInterpretTo.tauG_iff, CTree.CTree.tau1, ih]
    constructor
    · rintro ⟨value, _, hvalue⟩
      exact ⟨value, hvalue⟩
    · rintro ⟨value, hvalue⟩
      exact ⟨value, (), hvalue⟩
  | @fail next =>
    have heq : CTree.CTree.vis (Subeffect.mapEff ErrorE (ErrorE ⊕ₑ UBE) ErrorEIn.mk) next =
        (fail : Tree α) := by
      simp only [fail, CTree.trigger, Bind.bind, CTree.CTree.bind_vis]
      congr 1
      funext impossible
      exact nomatch impossible
    rw [heq, inflate_fail]
  | @ub next =>
    have heq : CTree.CTree.vis (Subeffect.mapEff UBE (ErrorE ⊕ₑ UBE) UBEIn.mk) next =
        (ub : Tree α) := by
      simp only [ub, CTree.trigger, Bind.bind, CTree.CTree.bind_vis]
      congr 1
      funext impossible
      exact nomatch impossible
    rw [heq, inflate_ub]

end Veir.Tree
