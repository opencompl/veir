module

public import Veir.Interpreter.Basic
import all Veir.Interpreter.Basic
import Veir.Interpreter.Lemmas
import all Init.Internal.Order.Basic

public section

namespace Veir.Collecting

/-!
# Collecting semantics

The concrete semantics follows the CFG, carrying the interpreter's SSA environment
and memory. An `Entry` is just before binding a block's arguments. `Reachable`
collects entries reached by finite executions, and `AtOperation` exposes the
successful prefixes inside each block, including blocks that eventually encounter
UB or fail interpretation.

All execution rules use the existing interpreter. In particular, this semantics
does not use the dataflow solver, folding, or the branch-operation interface.
`executes_iff_interpretBlockCFG` connects finite returning executions to the
interpreter's partial fixed point.
-/

/-- A concrete block entry, before its incoming arguments have been bound. -/
structure Entry (ctx : WfIRContext OpCode) where
  block : BlockPtr
  arguments : Array RuntimeValue
  state : InterpreterState ctx
  inBounds : block.InBounds ctx.raw

variable {ctx : WfIRContext OpCode}

/-- Execute one block, including simultaneous binding of its incoming arguments. -/
@[expose] def Entry.run (entry : Entry ctx) : Interp (InterpreterState ctx × ControlFlowAction) :=
  interpretBlock entry.block entry.arguments entry.state entry.inBounds

/-- One actual CFG traversal. UB and interpreter failure have no outgoing edges. -/
inductive Step : Entry ctx → Entry ctx → Prop
  | branch {entry : Entry ctx} {state : InterpreterState ctx}
      {arguments : Array RuntimeValue} {destination : BlockPtr}
      (executed : entry.run = .ok (state, .branch arguments destination))
      (inBounds : destination.InBounds ctx.raw) :
      Step entry ⟨destination, arguments, state, inBounds⟩

/-- The least set containing the initial entries and closed under actual CFG steps. -/
inductive Reachable (initial : Entry ctx → Prop) : Entry ctx → Prop
  | initial {entry} : initial entry → Reachable initial entry
  | step {source target} : Reachable initial source → Step source target → Reachable initial target

/-- The collecting semantics is a fixed point of adding initial entries and
successors. `Reachable.invariant` establishes that it is the least such fixed point. -/
theorem reachable_iff {initial : Entry ctx → Prop} {entry : Entry ctx} :
    Reachable initial entry ↔
      initial entry ∨ ∃ previous, Reachable initial previous ∧ Step previous entry := by
  constructor
  · intro reachable
    cases reachable with
    | initial h => exact .inl h
    | step h step => exact .inr ⟨_, h, step⟩
  · rintro (h | ⟨previous, reachable, step⟩)
    · exact .initial h
    · exact .step reachable step

/-- Every inductive invariant contains the collecting semantics. -/
theorem Reachable.invariant {initial invariant : Entry ctx → Prop}
    (initially : ∀ entry, initial entry → invariant entry)
    (preserved : ∀ source target, invariant source → Step source target → invariant target)
    {entry} (reachable : Reachable initial entry) : invariant entry := by
  induction reachable with
  | initial h => exact initially _ h
  | step _ h ih => exact preserved _ _ ih h

/-- Finite execution of zero or more CFG edges followed by a return. -/
inductive Executes : Entry ctx → InterpreterState ctx → Array RuntimeValue → Prop
  | returned {entry state values} (executed : entry.run = .ok (state, .return values)) :
      Executes entry state values
  | step {source target state values} :
      Step source target → Executes target state values → Executes source state values

theorem Executes.interpret {entry : Entry ctx} {state values}
    (execution : Executes entry state values) :
    interpretBlockCFG entry.block entry.arguments entry.state entry.inBounds = .ok (state, values) := by
  induction execution with
  | returned h =>
      unfold interpretBlockCFG
      simp only [Entry.run] at h
      simp [h]
  | step step _ ih =>
      cases step with
      | branch h inBounds =>
          unfold interpretBlockCFG
          simp only [Entry.run] at h
          simp [h, inBounds, ih]

/-- A successful interpreter result always has a finite execution witness. -/
theorem executes_of_interpretBlockCFG (block : BlockPtr) (arguments : Array RuntimeValue)
    (state : InterpreterState ctx) (inBounds : block.InBounds ctx.raw) :
    ∀ final values,
      interpretBlockCFG block arguments state inBounds = .ok (final, values) →
      Executes ⟨block, arguments, state, inBounds⟩ final values := by
  apply interpretBlockCFG.fixpoint_induct
    (motive := fun run => ∀ block arguments state inBounds final values,
      run block arguments state inBounds = .ok (final, values) →
      Executes ⟨block, arguments, state, inBounds⟩ final values)
  · refine Lean.Order.admissible_pi_apply
      (fun (block : BlockPtr)
        (run : Array RuntimeValue → InterpreterState ctx → block.InBounds ctx.raw →
          Interp (InterpreterState ctx × Array RuntimeValue)) => ∀ arguments state inBounds final values,
        run arguments state inBounds = .ok (final, values) →
        Executes ⟨block, arguments, state, inBounds⟩ final values) ?_
    intro block
    refine Lean.Order.admissible_pi_apply
      (fun (arguments : Array RuntimeValue)
        (run : InterpreterState ctx → block.InBounds ctx.raw →
          Interp (InterpreterState ctx × Array RuntimeValue)) => ∀ state inBounds final values,
        run state inBounds = .ok (final, values) →
        Executes ⟨block, arguments, state, inBounds⟩ final values) ?_
    intro arguments
    refine Lean.Order.admissible_pi_apply
      (fun (state : InterpreterState ctx)
        (run : block.InBounds ctx.raw → Interp (InterpreterState ctx × Array RuntimeValue)) =>
        ∀ inBounds final values,
        run inBounds = .ok (final, values) →
        Executes ⟨block, arguments, state, inBounds⟩ final values) ?_
    intro state
    refine Lean.Order.admissible_pi_apply
      (fun (inBounds : block.InBounds ctx.raw)
        (result : Interp (InterpreterState ctx × Array RuntimeValue)) => ∀ final values,
        result = .ok (final, values) →
        Executes ⟨block, arguments, state, inBounds⟩ final values) ?_
    intro inBounds
    exact Interp.admissible_of_ub _ (by intros; contradiction)
  · intro run ih block arguments state inBounds final values h
    cases executed : interpretBlock block arguments state inBounds with
    | fail _ => simp [executed] at h
    | ub _ => simp [executed] at h
    | ok result =>
        rcases result with ⟨nextState, action⟩
        cases action with
        | «return» results =>
            simp only [executed, Interp.ok.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            exact .returned executed
        | branch args destination =>
            simp only [executed] at h
            split at h
            · next destinationIn =>
                exact .step (.branch (entry := ⟨block, arguments, state, inBounds⟩)
                  executed destinationIn) (ih _ _ _ _ _ _ h)
            · cases h

/-- The collecting semantics agrees with the existing interpreter on returning runs. -/
theorem executes_iff_interpretBlockCFG (entry : Entry ctx) (state values) :
    Executes entry state values ↔
      interpretBlockCFG entry.block entry.arguments entry.state entry.inBounds = .ok (state, values) :=
  ⟨Executes.interpret, executes_of_interpretBlockCFG _ _ _ _ _ _⟩

/-- A successful prefix of the operation chain, stopping before the indicated operation. -/
inductive Prefix : OperationPtr → InterpreterState ctx → OperationPtr → InterpreterState ctx → Prop
  | refl (op state) : Prefix op state op state
  | next {first initial op state next state'}
      (hprefix : Prefix first initial op state)
      (inBounds : op.InBounds ctx.raw)
      (executed : interpretOp op state inBounds = .ok (state', none))
      (successor : (op.get! ctx.raw).next = some next) :
      Prefix first initial next state'

theorem Prefix.trans {first initial middle state last final}
    (left : Prefix (ctx := ctx) first initial middle state)
    (right : Prefix middle state last final) : Prefix first initial last final := by
  induction right with
  | refl => exact left
  | next _ hOp hRun hNext ih => exact .next ih hOp hRun hNext

/-- Prefixes stay in the same block, and every visited operation is in bounds. -/
theorem Prefix.location {first initial op state block}
    (hprefix : Prefix (ctx := ctx) first initial op state)
    (firstIn : first.InBounds ctx.raw)
    (firstParent : (first.get! ctx.raw).parent = some block) :
    op.InBounds ctx.raw ∧ (op.get! ctx.raw).parent = some block := by
  induction hprefix with
  | refl => exact ⟨firstIn, firstParent⟩
  | next _ _ _ _ ih =>
      obtain ⟨operations, chain⟩ := ctx.wellFormed.opChain block (by grind)
      grind

/-- A successful chain ends at an actual operation reached by a successful prefix. -/
theorem Prefix.of_interpretOpChain (first : OperationPtr) (initial : InterpreterState ctx)
    (firstIn : first.InBounds ctx.raw) :
    ∀ final action, interpretOpChain first initial firstIn = .ok (final, action) →
      ∃ op state, ∃ opIn : op.InBounds ctx.raw,
        Prefix first initial op state ∧ interpretOp op state opIn = .ok (final, some action) := by
  induction first, initial, firstIn using interpretOpChain.induct with
  | case1 first initial firstIn ih =>
    intro final action executed
    cases hop : interpretOp first initial firstIn with
    | fail _ => simp [interpretOpChain, hop, bind] at executed
    | ub _ => simp [interpretOpChain, hop, bind] at executed
    | ok result =>
      rcases result with ⟨state, cf⟩
      cases cf with
      | some cf =>
        have h : state = final ∧ cf = action := by
          simpa [interpretOpChain, hop, bind, pure] using executed
        rcases h with ⟨rfl, rfl⟩
        exact ⟨first, initial, firstIn, .refl _ _, hop⟩
      | none =>
        cases hn : (first.get! ctx.raw).next with
        | none =>
          rw [interpretOpChain_of_next!_eq_none hn] at executed
          simp [hop] at executed
        | some next =>
          rw [interpretOpChain_of_next!_eq_some hn] at executed
          have hnext : (first.get ctx.raw firstIn).next = some next := by grind
          obtain ⟨op, state', opIn, hp, hlast⟩ :=
            ih state next hnext final action (by simpa [hop] using executed)
          exact ⟨op, state', opIn, (Prefix.next (.refl _ _) firstIn hop hn).trans hp, hlast⟩

/-- A state immediately before an operation in this concrete block invocation. -/
@[expose] def AtOperation (entry : Entry ctx) (op : OperationPtr) (state : InterpreterState ctx) : Prop :=
  ∃ variables first,
    entry.state.variables.setArgumentValues? entry.block entry.arguments entry.inBounds = some variables ∧
    (entry.block.get! ctx.raw).firstOp = some first ∧
    Prefix first ⟨variables, entry.state.memory⟩ op state

theorem AtOperation.location {entry : Entry ctx} {op state}
    (atOp : AtOperation entry op state) :
    op.InBounds ctx.raw ∧ (op.get! ctx.raw).parent = some entry.block := by
  obtain ⟨variables, first, _, hf, hp⟩ := atOp
  have := entry.inBounds
  exact hp.location (by grind) (by grind)

/-- Expose the terminal operation of a successfully executed block. -/
theorem Entry.terminal {entry : Entry ctx} {final action}
    (executed : entry.run = .ok (final, action)) :
    ∃ op state, ∃ opIn : op.InBounds ctx.raw,
      AtOperation entry op state ∧ interpretOp op state opIn = .ok (final, some action) := by
  unfold Entry.run interpretBlock at executed
  cases hb : entry.state.variables.setArgumentValues? entry.block entry.arguments entry.inBounds with
  | none => simp [hb, bind, liftM, monadLift, MonadLift.monadLift] at executed
  | some variables =>
    simp only [hb, bind, liftM, monadLift, MonadLift.monadLift] at executed
    split at executed
    · cases executed
    · next first hf =>
      obtain ⟨op, state, opIn, hp, hlast⟩ := Prefix.of_interpretOpChain _ _ _ _ _ executed
      exact ⟨op, state, opIn, ⟨variables, first, hb, by grind, hp⟩, hlast⟩

/-- An operation state reached from one of the initial entries. -/
@[expose] def ReachesOperation (initial : Entry ctx → Prop) (op : OperationPtr)
    (state : InterpreterState ctx) : Prop :=
  ∃ entry, Reachable initial entry ∧ AtOperation entry op state

/-- SSA values observable immediately before an executed operation. -/
@[expose] def Values (initial : Entry ctx → Prop) (value : ValuePtr) (runtime : RuntimeValue) : Prop :=
  ∃ op state, ReachesOperation initial op state ∧ state.variables.getVar? value = some runtime

/-- Actual block reachability, independent of the analysis's executability flags. -/
@[expose] def Blocks (initial : Entry ctx → Prop) (block : BlockPtr) : Prop :=
  ∃ entry, Reachable initial entry ∧ entry.block = block

/-- Actual CFG traversals, independent of the analysis's branch interface. -/
@[expose] def Edges (initial : Entry ctx → Prop) (source target : BlockPtr) : Prop :=
  ∃ entry next, Reachable initial entry ∧ Step entry next ∧
    entry.block = source ∧ next.block = target

end Veir.Collecting
