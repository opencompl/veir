module

public import Veir.Passes.DCE.InterpreterNormalization
public import Veir.Passes.DCE.CFGRefinement

import all Veir.Interpreter.CTreeInterpreter
import all Veir.Interpreter.CTree
import all CTree.Defs
import all CTree.Interp

public section

open CTree

namespace Veir.CTree

/-- The CFG body has no actual region requests for the supported opcodes. -/
theorem interpretCFG_iter_eq_embedTreeStep {ctx : WfIRContext OpCode}
    (location : interpretCFG.StateLocation ctx) (state : InterpreterState ctx) :
    interpretCFG.iter location state =
      Tree.embedRegion ctx (InterpreterState ctx) (interpretCFGTreeStep location state) := by
  cases location with
  | inl entry =>
    obtain ⟨⟨block, blockIn⟩, values⟩ := entry
    simp only [interpretCFG.iter, interpretCFGTreeStep]
    have hcount : block.getNumArguments! ctx.raw = block.getNumArguments ctx.raw := by grind
    rw [hcount]
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
    rw [Tree.embedRegion_bind]
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

/-- Closing the phantom region signature commutes with the entire CFG loop. -/
theorem interpretCFG_eq_embedTree (region : RegionPtr) (values : Array RuntimeValue)
    {ctx : WfIRContext OpCode} (state : InterpreterState ctx)
    (regionIn : region.InBounds ctx.raw) :
    interpretCFG region values state regionIn =
      Tree.embedRegion ctx (InterpreterState ctx) (interpretCFGTree region values state regionIn) := by
  have hloop (initial : interpretCFG.StateLocation ctx × InterpreterState ctx) :
      CTree.iter (fun (location, state) => interpretCFG.iter location state) initial =
      Tree.embedRegion ctx (InterpreterState ctx)
        (CTree.iter (fun (location, state) => interpretCFGTreeStep location state) initial) := by
    rw [Tree.embedRegion_iter]
    congr 1
    funext current
    exact interpretCFG_iter_eq_embedTreeStep current.1 current.2
  simp only [interpretCFG, interpretCFGTree]
  split <;> split <;> simp_all only [Tree.embedRegion_fail]
  · congr 2 <;> grind
  · grind
  · grind

/-- Existing recursive region execution is one ordinary event-interpreter
layer around the closed CFG, with all silent steps retained. -/
theorem interpretRegion_eq_inflateCFGTree (region : RegionPtr) (values : Array RuntimeValue)
    {ctx : WfIRContext OpCode} (state : InterpreterState ctx)
    (regionIn : region.InBounds ctx.raw) :
    interpretRegion region values state regionIn =
      Tree.inflate (interpretCFGTree region values state regionIn) := by
  unfold interpretRegion CTree.mrec
  dsimp only
  rw [interpretCFG_eq_embedTree]
  exact Tree.interp_mrec_embedRegion ctx (InterpreterState ctx) _ _

end Veir.CTree
