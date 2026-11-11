module

public import Veir.Interpreter.CTreeRefinement.Embedding

import all Veir.Interpreter.CTreeInterpreter
import all Veir.Interpreter.CTreeRefinement.Embedding
import all Veir.Interpreter.CTree
import all CTree.Defs
import all CTree.Iter
import all CTree.Interp

public section

/-!
# The region interpreter is a closed CFG loop

No operation calls a region, so the region interpreter `interpretRegion` is the closed CFG loop
`interpretCFGTree` with one ordinary event-handler layer around it.
-/

open CTree

namespace Veir.CTree

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
      CTree.CTree.bind_tau, _root_.CTree.bind_pure]
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

/-- The closed operation interpreter retains both event-handler layers used by
ordinary region interpretation, including their silent steps. -/
theorem interpretOp_eq_embedOperationTree (op : OperationPtr) {ctx : WfIRContext OpCode}
    (state : InterpreterState ctx) (opIn : op.InBounds ctx.raw) :
    interpretOp op state opIn =
      embedRegion ctx (InterpreterState ctx) (interpretOperationTree op state opIn) := by
  cases hoperands : state.variables.getOperandValues op with
  | none => simp [interpretOp, interpretOperationTree, hoperands]
  | some operands =>
    simp only [interpretOp, interpretOperationTree, hoperands]
    rw [interp_embedRegion ctx MemoryState]
    rw [interp_embedRegion_closed ctx ctx MemoryState (InterpreterState ctx) _ (by intro; rfl)]
    simp only [Bind.bind]
    rw [embedRegion_bind]
    congr 1
    funext result
    cases hresults : state.variables.setResultValues? op result.1 opIn <;> simp

/-- No operation calls a region, so a CFG step is an embedded closed step. -/
theorem interpretCFG_iter_eq_embedTreeStep {ctx : WfIRContext OpCode}
    (location : interpretCFG.StateLocation ctx) (state : InterpreterState ctx) :
    interpretCFG.iter location state =
      embedRegion ctx (InterpreterState ctx) (interpretCFGTreeStep location state) := by
  cases location with
  | inl entry =>
    obtain ⟨⟨block, blockIn⟩, values⟩ := entry
    simp only [interpretCFG.iter, interpretCFGTreeStep]
    split
    · simp
    · cases hargs : state.variables.setArgumentValues? block values blockIn with
      | none => simp
      | some variables =>
        simp only
        split <;> split <;> simp_all <;> grind
  | inr operation =>
    obtain ⟨op, opIn⟩ := operation
    simp only [interpretCFG.iter, interpretCFGTreeStep]
    rw [interpretOp_eq_embedOperationTree]
    simp only [Bind.bind]
    rw [embedRegion_bind]
    congr 1
    funext result
    obtain ⟨nextState, action⟩ := result
    simp only [interpretCFGTreeContinue]
    cases action with
    | none =>
      simp only
      split <;> split <;> simp_all <;> grind
    | some action =>
      cases action with
      | «return» results => simp
      | branch args destination =>
        simp only
        split <;> simp_all

/-- No operation calls a region, so the CFG loop is an embedded closed loop. -/
theorem interpretCFG_eq_embedTree (region : RegionPtr) (values : Array RuntimeValue)
    {ctx : WfIRContext OpCode} (state : InterpreterState ctx)
    (regionIn : region.InBounds ctx.raw) :
    interpretCFG region values state regionIn =
      embedRegion ctx (InterpreterState ctx) (interpretCFGTree region values state regionIn) := by
  have hloop (initial : interpretCFG.StateLocation ctx × InterpreterState ctx) :
      CTree.iter (fun (location, state) => interpretCFG.iter location state) initial =
      embedRegion ctx (InterpreterState ctx)
        (CTree.iter (fun (location, state) => interpretCFGTreeStep location state) initial) := by
    rw [embedRegion_iter]
    congr 1
    funext current
    exact interpretCFG_iter_eq_embedTreeStep current.1 current.2
  simp only [interpretCFG, interpretCFGTree]
  split <;> split <;> simp_all only [embedRegion_fail]
  · congr 2 <;> grind
  · grind
  · grind

/-- Recursive region execution is one ordinary event-interpreter layer around the closed CFG
loop, with all silent steps retained. -/
theorem interpretRegion_eq_inflateCFGTree (region : RegionPtr) (values : Array RuntimeValue)
    {ctx : WfIRContext OpCode} (state : InterpreterState ctx)
    (regionIn : region.InBounds ctx.raw) :
    interpretRegion region values state regionIn =
      inflate (interpretCFGTree region values state regionIn) := by
  unfold interpretRegion CTree.mrec
  dsimp only
  rw [interpretCFG_eq_embedTree]
  exact interp_mrec_embedRegion ctx (InterpreterState ctx) _ _

end Veir.CTree
