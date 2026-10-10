module

public import Veir.Interpreter.CollectingSemantics
public import Veir.Analysis.DataFlow.SparseFact
public import Veir.Analysis.DataFlow.DeadCodeAnalysis

public section

namespace Veir.SCCP

/-!
# Sound SCCP facts

The main theorem is `facts_sound`: local validity of the *combined* constant and
executability facts implies soundness for every concrete execution. The corollary
`constant_refines` is the interface intended for constant-substitution proofs.

`Valid` contains semantic obligations at entries, individual operations, and
branches. It does not assert that a worklist terminated, and it does not assume
monotonicity or optimality of the abstract transfer functions. `SCCPChecker`
establishes these obligations from checked output and explicit local transfer
soundness contracts; `Facts.ofDataFlow` alone only reads the solver's output.
-/

/-- The semantic part of a solved SCCP result; scheduling and materializer metadata
are deliberately absent. -/
structure Facts where
  constant : ValuePtr → AbstractConstant
  blockLive : BlockPtr → Prop
  edgeLive : BlockPtr → BlockPtr → Prop

/-- Read the facts produced by the joint constant-propagation/dead-code solver.
Missing facts retain the implementation's bottom/dead interpretation. -/
@[expose] def Facts.ofDataFlow (facts : DataFlowContext) (ctx : WfIRContext OpCode) : Facts where
  constant := fun value => SparseFact.getElement .sparseConstant value facts
  blockLive := fun block =>
    (facts.getOrMkFact .liveness (.InsertPoint (InsertPoint.atStart! block ctx.raw))).live = true
  edgeLive := fun source target =>
    (facts.getOrMkFact .liveness (.CFGEdge ⟨source, target⟩)).live = true

variable {ctx : WfIRContext OpCode}

/-- Every value already bound in the environment satisfies its constant fact.
This includes retained values from earlier iterations: each was genuinely computed
earlier, and SCCP's one fact per static definition covers all its dynamic values.
This is not the stronger, generally false claim that old defining equations still
hold for all retained bindings. -/
@[expose] def Facts.CoversState (facts : Facts) (state : InterpreterState ctx) : Prop :=
  ∀ value runtime, state.variables.getVar? value = some runtime →
    AbstractConstant.γ (facts.constant value) runtime

/-- The block is executable, and binding its pending arguments establishes the
value invariant. A failed binding produces no subsequent execution state. -/
@[expose] def Facts.CoversEntry (facts : Facts) (entry : Collecting.Entry ctx) : Prop :=
  facts.blockLive entry.block ∧
    ∀ variables,
      entry.state.variables.setArgumentValues? entry.block entry.arguments entry.inBounds = some variables →
      facts.CoversState ⟨variables, entry.state.memory⟩

/-- Local proof obligations, stated against the interpreter rather than against
the folding and branch interfaces that the analysis is meant to justify. -/
structure Facts.Valid (facts : Facts) (initial : Collecting.Entry ctx → Prop) : Prop where
  /-- Every allowed initial invocation is covered. -/
  initial : ∀ entry, initial entry → facts.CoversEntry entry
  /-- Executing an operation in an executable block preserves the value facts. -/
  operation : ∀ block op (opIn : op.InBounds ctx.raw) state next action,
    (op.get! ctx.raw).parent = some block → facts.blockLive block →
    facts.CoversState state → interpretOp op state opIn = .ok (next, action) →
    facts.CoversState next
  /-- An actual branch enables its edge and covers the destination's arguments.
This obligation covers the edge and the argument join together. -/
  branch : ∀ block op (opIn : op.InBounds ctx.raw) state next arguments destination
      (destinationIn : destination.InBounds ctx.raw),
    (op.get! ctx.raw).parent = some block → facts.blockLive block →
    facts.CoversState state →
    interpretOp op state opIn = .ok (next, some (.branch arguments destination)) →
    facts.edgeLive block destination ∧
      facts.CoversEntry ⟨destination, arguments, next, destinationIn⟩

private theorem Facts.Valid.covers_prefix {facts : Facts} {initial : Collecting.Entry ctx → Prop}
    (valid : facts.Valid initial) {block first op} {initialState state : InterpreterState ctx}
    (live : facts.blockLive block) (firstIn : first.InBounds ctx.raw)
    (parent : (first.get! ctx.raw).parent = some block)
    (covered : facts.CoversState initialState)
    (hprefix : Collecting.Prefix first initialState op state) : facts.CoversState state := by
  induction hprefix with
  | refl => exact covered
  | next hp opIn executed _ ih =>
      exact valid.operation block _ opIn _ _ _ (hp.location firstIn parent).2 live ih executed

theorem Facts.Valid.covers_operation {facts : Facts} {initial : Collecting.Entry ctx → Prop}
    (valid : facts.Valid initial) {entry : Collecting.Entry ctx} {op state}
    (covered : facts.CoversEntry entry) (atOp : Collecting.AtOperation entry op state) :
    facts.CoversState state := by
  obtain ⟨variables, first, bound, firstOp, hp⟩ := atOp
  have := entry.inBounds
  exact valid.covers_prefix covered.1 (by grind) (by grind) (covered.2 _ bound) hp

theorem Facts.Valid.covers_step {facts : Facts} {initial : Collecting.Entry ctx → Prop}
    (valid : facts.Valid initial) {source target : Collecting.Entry ctx}
    (covered : facts.CoversEntry source) (step : Collecting.Step source target) :
    facts.edgeLive source.block target.block ∧ facts.CoversEntry target := by
  cases step with
  | branch executed destinationIn =>
      obtain ⟨op, state, opIn, atOp, terminal⟩ := Collecting.Entry.terminal executed
      exact valid.branch _ _ opIn _ _ _ _ destinationIn atOp.location.2 covered.1
        (valid.covers_operation covered atOp) terminal

/-- Soundness at block entries is proved jointly for constants and executability. -/
theorem Facts.Valid.covers_reachable {facts : Facts} {initial}
    (valid : facts.Valid initial) {entry : Collecting.Entry ctx}
    (reachable : Collecting.Reachable initial entry) : facts.CoversEntry entry :=
  reachable.invariant valid.initial (fun _ _ covered step => (valid.covers_step covered step).2)

/-- What it means for SCCP's constants, blocks, and edges to describe all actual
executions. The concrete sets come exclusively from `Collecting`. -/
structure Facts.Sound (facts : Facts) (initial : Collecting.Entry ctx → Prop) : Prop where
  values : ∀ value runtime, Collecting.Values initial value runtime →
    AbstractConstant.γ (facts.constant value) runtime
  blocks : ∀ block, Collecting.Blocks initial block → facts.blockLive block
  edges : ∀ source target, Collecting.Edges initial source target → facts.edgeLive source target

/-- **SCCP soundness:** locally valid constant and executability facts cover every
runtime value, reachable block, and traversed edge in the collecting semantics. -/
theorem facts_sound {facts : Facts} {initial : Collecting.Entry ctx → Prop}
    (valid : facts.Valid initial) : facts.Sound initial where
  values := by
    rintro value runtime ⟨op, state, ⟨entry, reachable, atOp⟩, observed⟩
    exact valid.covers_operation (valid.covers_reachable reachable) atOp value runtime observed
  blocks := by
    rintro block ⟨entry, reachable, rfl⟩
    exact (valid.covers_reachable reachable).1
  edges := by
    rintro source target ⟨entry, next, reachable, step, rfl, rfl⟩
    exact (valid.covers_step (valid.covers_reachable reachable) step).1

/-- **Constant-substitution guarantee:** a constant reported by valid SCCP facts
refines every runtime value it can replace in an actual execution.

The orientation is intentional: `runtime ⊒ constant` permits replacing poison by
a defined constant. This is a value-refinement theorem, not yet a theorem about
the materializer, IR rewrites, or the entire canonicalization pass. -/
theorem constant_refines {facts : Facts} {initial : Collecting.Entry ctx → Prop}
    (valid : facts.Valid initial) {value runtime constant}
    (known : facts.constant value = .constant constant)
    (observed : Collecting.Values initial value runtime) : runtime ⊒ constant := by
  have sound := (facts_sound valid).values value runtime observed
  simpa only [known, AbstractConstant.γ] using sound

/-- A block certified dead cannot be entered in an actual execution. -/
theorem dead_block_unreachable {facts : Facts} {initial : Collecting.Entry ctx → Prop}
    (valid : facts.Valid initial) {block} (dead : ¬ facts.blockLive block) :
    ¬ Collecting.Blocks initial block := fun reached => dead ((facts_sound valid).blocks _ reached)

end Veir.SCCP
