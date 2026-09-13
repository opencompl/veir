module

public import Veir.Interpreter.Refinement.Basic

import all Veir.Interpreter.Basic
import all Init.Internal.Order.Basic

namespace Veir

public section

/-- An interpreter configuration at the entry to a basic block. -/
structure CFGState (ctx : WfIRContext OpCode) where
  block : BlockPtr
  arguments : Array RuntimeValue
  state : InterpreterState ctx
  blockIn : block.InBounds ctx.raw

namespace CFGState

variable {ctx : WfIRContext OpCode}

/-- Execute the current block, without following its outgoing branch. -/
def step (s : CFGState ctx) : Interp (InterpreterState ctx × ControlFlowAction) :=
  interpretBlock s.block s.arguments s.state s.blockIn

/-- Execute from the current block until the function returns. -/
def interpret (s : CFGState ctx) : Interp (InterpreterState ctx × Array RuntimeValue) :=
  interpretBlockCFG s.block s.arguments s.state s.blockIn

/-- A finite, returning CFG execution. -/
inductive Returns : CFGState ctx → InterpreterState ctx → Array RuntimeValue → Prop where
  | done {s state values} (h : s.step = .ok (state, .return values)) :
      Returns s state values
  | branch {s state arguments block finalState values}
      (blockIn : block.InBounds ctx.raw)
      (h : s.step = .ok (state, .branch arguments block))
      (tail : Returns ⟨block, arguments, state, blockIn⟩ finalState values) :
      Returns s finalState values

/-- A finite execution produces the corresponding interpreter result. -/
theorem Returns.interpret_eq {s : CFGState ctx} {state values}
    (h : s.Returns state values) : s.interpret = .ok (state, values) := by
  induction h with
  | done h =>
      rw [interpret, interpretBlockCFG.eq_def]
      simp only [step] at h
      simp only [h]
  | branch blockIn h tail ih =>
      rw [interpret, interpretBlockCFG.eq_def]
      simp only [step] at h
      simp only [h, dif_pos blockIn]
      exact ih

/-- Successful CFG interpretation has a finite execution witness. -/
theorem returns_of_interpret_eq {s : CFGState ctx} {state values}
    (h : s.interpret = .ok (state, values)) : s.Returns state values := by
  let motive := fun (f : (block : BlockPtr) → Array RuntimeValue →
      InterpreterState ctx → block.InBounds ctx.raw →
      Interp (InterpreterState ctx × Array RuntimeValue)) =>
    ∀ block arguments initial blockIn state values,
      f block arguments initial blockIn = .ok (state, values) →
      Returns ⟨block, arguments, initial, blockIn⟩ state values
  have hadm : Lean.Order.admissible motive := by
    dsimp only [motive]
    refine Lean.Order.admissible_pi_apply (fun (block : BlockPtr)
      (f : Array RuntimeValue → InterpreterState ctx → block.InBounds ctx.raw →
        Interp (InterpreterState ctx × Array RuntimeValue)) =>
      ∀ arguments initial blockIn state values,
        f arguments initial blockIn = .ok (state, values) →
        Returns ⟨block, arguments, initial, blockIn⟩ state values) ?_
    intro block
    refine Lean.Order.admissible_pi_apply (fun (arguments : Array RuntimeValue)
      (f : InterpreterState ctx → block.InBounds ctx.raw →
        Interp (InterpreterState ctx × Array RuntimeValue)) =>
      ∀ initial blockIn state values,
        f initial blockIn = .ok (state, values) →
        Returns ⟨block, arguments, initial, blockIn⟩ state values) ?_
    intro arguments
    refine Lean.Order.admissible_pi_apply (fun (initial : InterpreterState ctx)
      (f : block.InBounds ctx.raw → Interp (InterpreterState ctx × Array RuntimeValue)) =>
      ∀ blockIn state values,
        f blockIn = .ok (state, values) →
        Returns ⟨block, arguments, initial, blockIn⟩ state values) ?_
    intro initial
    refine Lean.Order.admissible_pi_apply (fun (blockIn : block.InBounds ctx.raw)
      (result : Interp (InterpreterState ctx × Array RuntimeValue)) =>
      ∀ state values, result = .ok (state, values) →
        Returns ⟨block, arguments, initial, blockIn⟩ state values) ?_
    intro blockIn
    apply Lean.Order.admissible_flatOrder (b := Interp.fail)
    intro state values h
    cases h
  have hexec := interpretBlockCFG.fixpoint_induct motive hadm (by
    intro f ih block arguments initial blockIn state values hresult
    cases hstep : interpretBlock block arguments initial blockIn with
    | fail => simp only [hstep] at hresult; contradiction
    | ub => simp only [hstep] at hresult; contradiction
    | ok result =>
      rcases result with ⟨next, action⟩
      cases action with
      | «return» returned =>
        simp only [hstep, Interp.ok.injEq, Prod.mk.injEq] at hresult
        rcases hresult with ⟨rfl, rfl⟩
        exact .done hstep
      | branch forwarded successor =>
        simp only [hstep] at hresult
        split at hresult
        next successorIn =>
          exact .branch successorIn hstep
            (ih successor forwarded next successorIn state values hresult)
        next => contradiction)
  exact hexec s.block s.arguments s.state s.blockIn state values h

theorem interpret_eq_iff_returns {s : CFGState ctx} {state values} :
    s.interpret = .ok (state, values) ↔ s.Returns state values :=
  ⟨returns_of_interpret_eq, Returns.interpret_eq⟩

/-- Zero or more block transitions, stopping before executing the last block. -/
inductive Reaches : CFGState ctx → CFGState ctx → Prop where
  | refl (s) : Reaches s s
  | branch {s state arguments block t}
      (blockIn : block.InBounds ctx.raw)
      (h : s.step = .ok (state, .branch arguments block))
      (tail : Reaches ⟨block, arguments, state, blockIn⟩ t) :
      Reaches s t

/-- Append a returning execution to a finite prefix. -/
theorem Reaches.returns {s t : CFGState ctx} {state values}
    (path : s.Reaches t) (tail : t.Returns state values) :
    s.Returns state values := by
  induction path with
  | refl => exact tail
  | branch blockIn h _ ih => exact .branch blockIn h (ih tail)

/-- A simulation may match a source block transition with zero or more target
    transitions. This permits eliminating empty blocks from a CFG. -/
structure ForwardSimulation {ctx' : WfIRContext OpCode}
    (related : CFGState ctx → CFGState ctx' → Prop)
    (resultRelated : (InterpreterState ctx × Array RuntimeValue) →
      (InterpreterState ctx' × Array RuntimeValue) → Prop) : Prop where
  onReturn : ∀ {s t state values}, related s t →
    s.step = .ok (state, .return values) →
    ∃ state' values', t.Returns state' values' ∧
      resultRelated (state, values) (state', values')
  onBranch : ∀ {s t state arguments block} (blockIn : block.InBounds ctx.raw),
    related s t → s.step = .ok (state, .branch arguments block) →
    ∃ t', t.Reaches t' ∧ related ⟨block, arguments, state, blockIn⟩ t'

/-- A forward simulation preserves every finite returning source execution. -/
theorem ForwardSimulation.returns {ctx' : WfIRContext OpCode}
    {related : CFGState ctx → CFGState ctx' → Prop} {resultRelated}
    (simulation : ForwardSimulation related resultRelated)
    {s : CFGState ctx} {t : CFGState ctx'} {state values}
    (hrelated : related s t) (execution : s.Returns state values) :
    ∃ state' values', t.Returns state' values' ∧
      resultRelated (state, values) (state', values') := by
  induction execution generalizing t with
  | done h => exact simulation.onReturn hrelated h
  | branch blockIn h _ ih =>
      obtain ⟨t', path, hrelated'⟩ := simulation.onBranch blockIn hrelated h
      obtain ⟨state', values', tail, hresult⟩ := ih hrelated'
      exact ⟨state', values', path.returns tail, hresult⟩

/-- Lift a CFG simulation to the interpreter's semantic refinement relation. -/
theorem ForwardSimulation.refines {ctx' : WfIRContext OpCode}
    {related : CFGState ctx → CFGState ctx' → Prop} {resultRelated}
    (simulation : ForwardSimulation related resultRelated)
    {s : CFGState ctx} {t : CFGState ctx'} (hrelated : related s t) :
    Interp.isRefinedBy resultRelated s.interpret t.interpret := by
  cases hsource : s.interpret with
  | fail => simp only [Interp.isRefinedBy]
  | ub => simp only [Interp.isRefinedBy]
  | ok result =>
      rcases result with ⟨state, values⟩
      obtain ⟨state', values', execution, hresult⟩ :=
        simulation.returns hrelated (returns_of_interpret_eq hsource)
      simp only [execution.interpret_eq, Interp.isRefinedBy]
      exact hresult

end CFGState

end

end Veir
