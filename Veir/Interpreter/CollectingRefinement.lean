module

public import Veir.Interpreter.CollectingSemantics
public import Veir.Interpreter.Refinement.Basic
import all Veir.Interpreter.Basic
import all Veir.Interfaces.FunctionInterfaces

public section

namespace Veir.Collecting

/-!
# From collecting invariants to function refinement

`Simulation` has two local obligations: matching a successful block return and
matching one CFG edge. The source invariant restricts these obligations to states
described by the analysis. `Simulation.refines` lifts them to complete executions,
using the adequacy theorem for the existing interpreter.

The observation relation is a parameter. In particular, this infrastructure does
not silently replace Veir's current equal-memory notion of function refinement by
a weaker one. A client using poison-refining stores will need an appropriate
memory-refinement contract as well as value refinement.
-/

variable {sourceCtx targetCtx : WfIRContext OpCode}

/-- Observe the final memory and return values of a CFG execution. -/
@[expose] def Entry.evaluate (entry : Entry sourceCtx) : Interp (MemoryState × Array RuntimeValue) := do
  let (state, values) ←
    interpretBlockCFG entry.block entry.arguments entry.state entry.inBounds
  return (state.memory, values)

/-- Local obligations for relating two CFGs. The relation may rename SSA values
and relate different environments, memories, and block-argument lists. Insertions
and deletions inside a block are handled by the block execution in these obligations.
Neither obligation assumes refinement of a whole CFG or function. -/
structure Simulation
    (invariant : Entry sourceCtx → Prop)
    (related : Entry sourceCtx → Entry targetCtx → Prop)
    (observations : (MemoryState × Array RuntimeValue) → (MemoryState × Array RuntimeValue) → Prop) : Prop where
  /-- A successful source return is matched by a successful target block return. -/
  returns : ∀ source target state values,
    invariant source → related source target →
    source.run = .ok (state, .return values) →
    ∃ state' values', target.run = .ok (state', .return values') ∧
      observations (state.memory, values) (state'.memory, values')
  /-- A successful source CFG edge is matched by a target edge and related entries. -/
  branches : ∀ source target next,
    invariant source → related source target → Step source next →
    ∃ next', Step target next' ∧ related next next'

/-- Lift a local simulation along any finite returning source execution. -/
theorem Simulation.executes {invariant related observations}
    (simulation : Simulation invariant related observations)
    (preserved : ∀ source next, invariant source → Step source next → invariant next)
    {source : Entry sourceCtx} {target : Entry targetCtx} {state values}
    (covered : invariant source) (states : related source target)
    (execution : Executes source state values) :
    ∃ state' values', Executes target state' values' ∧
      observations (state.memory, values) (state'.memory, values') := by
  induction execution generalizing target with
  | returned executed =>
      obtain ⟨state', values', returned, observed⟩ :=
        simulation.returns _ _ _ _ covered states executed
      exact ⟨state', values', .returned returned, observed⟩
  | step step _ ih =>
      obtain ⟨next', step', nextRelated⟩ := simulation.branches _ _ _ covered states step
      obtain ⟨state', values', execution', observed⟩ :=
        ih (preserved _ _ covered step) nextRelated
      exact ⟨state', values', .step step' execution', observed⟩

/-- Local simulation on an inductive invariant implies refinement of complete CFG
executions. This theorem uses the existing `Interp.isRefinedBy`: source UB and
source interpreter failure impose no target obligation. -/
theorem Simulation.refines {invariant related observations}
    (simulation : Simulation invariant related observations)
    (preserved : ∀ source next, invariant source → Step source next → invariant next)
    {source : Entry sourceCtx} {target : Entry targetCtx}
    (covered : invariant source) (states : related source target) :
    Interp.isRefinedBy observations source.evaluate target.evaluate := by
  cases executed : interpretBlockCFG source.block source.arguments source.state source.inBounds with
  | fail _ => simp [Entry.evaluate, executed, Interp.isRefinedBy]
  | ub _ => simp [Entry.evaluate, executed, Interp.isRefinedBy]
  | ok result =>
      rcases result with ⟨state, values⟩
      obtain ⟨state', values', targetExecution, observed⟩ := simulation.executes preserved covered states
        ((executes_iff_interpretBlockCFG _ _ _).mpr executed)
      simp [Entry.evaluate, executed, targetExecution.interpret, Interp.isRefinedBy, observed]

/-- A function with one region and a nonempty body, as expected by the interpreter.
The stored fields are structural witnesses, not semantic assumptions. -/
structure FunctionBody {ctx : WfIRContext OpCode} {op : OperationPtr}
    (function : FunctionOp ctx.raw op) where
  opInBounds : op.InBounds ctx.raw
  oneRegion : op.getNumRegions! ctx.raw = 1
  entry : BlockPtr
  entryInBounds : entry.InBounds ctx.raw
  firstBlock : (function.getFunctionBody!.get! ctx.raw).firstBlock = some entry

variable {sourceOp targetOp : OperationPtr}

/-- A function invocation begins with a fresh SSA environment and the supplied memory. -/
@[expose] def FunctionBody.start {function : FunctionOp sourceCtx.raw sourceOp}
    (body : FunctionBody function) (arguments : Array RuntimeValue) (memory : MemoryState) : Entry sourceCtx :=
  ⟨body.entry, arguments, ⟨.empty sourceCtx, memory⟩, body.entryInBounds⟩

/-- All invocations, retaining their individual arguments and initial memories. -/
@[expose] def FunctionBody.Initial {function : FunctionOp sourceCtx.raw sourceOp}
    (body : FunctionBody function) (entry : Entry sourceCtx) : Prop :=
  ∃ arguments memory, entry = body.start arguments memory

/-- Starting the collecting semantics at a function body gives exactly the
existing function interpreter. -/
theorem FunctionBody.evaluate_start {function : FunctionOp sourceCtx.raw sourceOp}
    (body : FunctionBody function) (arguments : Array RuntimeValue) (memory : MemoryState) :
    (body.start arguments memory).evaluate = interpretFunction function arguments memory body.opInBounds := by
  have hregions : sourceOp.getNumRegions sourceCtx.raw body.opInBounds = 1 := by
    have := body.oneRegion
    grind
  unfold interpretFunction
  simp only [hregions, ne_eq, not_true_eq_false, ↓reduceDIte]
  unfold interpretRegion
  have hfirst : ((function.getFunctionBody body.opInBounds (by omega)).get sourceCtx.raw
      (by grind)).firstBlock = some body.entry := by
    have := body.firstBlock
    grind
  split
  · next hnone => grind
  · next block hsome =>
      have : block = body.entry := by grind
      subst block
      rfl

end Veir.Collecting
