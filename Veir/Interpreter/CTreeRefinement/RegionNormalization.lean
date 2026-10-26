module

public import Veir.Interpreter.CTreeRefinement.Embedding

import all Veir.Interpreter.CTree
import all Veir.Interpreter.CTreeRefinement.Embedding
import all CTree.Defs
import all CTree.Iter
import all CTree.Interp

public section

namespace Veir.Tree

open CTree

/-- Recursive region interpretation of a closed tree never invokes its region
handler. It retains the silent steps of ordinary event interpretation. -/
theorem interp_mrec_embedRegion (ctx : WfIRContext OpCode) (σ : Type)
    (handler : (event : RunRegionEIn ctx σ) → RegionTree ctx σ (RunRegionE ctx σ event))
    (tree : Tree α) :
    CTree.interp_mrec handler (embedRegion ctx σ tree) = inflate tree := by
  unfold CTree.interp_mrec inflate CTree.interp
  apply iter_mapState (mapState := embedRegion ctx σ)
  intro current
  cases current using CTree.CTree.cases with
  | ret value =>
    simp only [embedRegion_pure]
    simp only [Pure.pure, unfold_ret, map_eq_pure_bind,
      Bind.bind, CTree.CTree.bind_ret]
    rfl
  | tau choice next =>
    simp only [embedRegion_tau, unfold_tauG, map_eq_pure_bind, Bind.bind,
      CTree.CTree.bind_tau, Tree.bind_pure_left]
    rfl
  | vis event next =>
    cases event with
    | inl event =>
      rw [embedRegion, unfold_vis]
      simp [fail, CTree.trigger, Bind.bind, CTree.CTree.bind_vis]
      simp only [map_eq_pure_bind, Bind.bind, CTree.CTree.bind_vis]
      congr 1
      funext impossible
      exact nomatch impossible
    | inr event =>
      rw [embedRegion, unfold_vis]
      simp [ub, CTree.trigger, Bind.bind, CTree.CTree.bind_vis]
      simp only [map_eq_pure_bind, Bind.bind, CTree.CTree.bind_vis]
      congr 1
      funext impossible
      exact nomatch impossible

end Veir.Tree
