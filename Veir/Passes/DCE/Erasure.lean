module

public import Veir.Passes.DCE.dce
public import Veir.PatternRewriter.DriverPreservation
import all Veir.PatternRewriter.DriverPreservation
import all Veir.PatternRewriter.Basic
import all Veir.Passes.DCE.dce
import all Init.Data.Array.Basic
import all Veir.Rewriter.WfRewriter.Basic
import all Veir.Rewriter.Basic

public section

namespace Veir.DCE

/-- A single syntactic deletion, recording deadness in the context where the
deletion takes place. This relation makes no semantic refinement assumption. -/
inductive EraseStep : WfIRContext OpCode → WfIRContext OpCode → Prop where
  | erase (ctx : WfIRContext OpCode) (operation : OperationPtr)
      (inBounds : operation.InBounds ctx.raw) (dead : operation.isTriviallyDead ctx.raw) :
      EraseStep ctx (WfRewriter.eraseOp ctx operation dead.1 dead.2.1 inBounds)

/-- A finite sequence of the actual deletions performed by DCE. -/
inductive Erasures : WfIRContext OpCode → WfIRContext OpCode → Prop where
  | refl (ctx) : Erasures ctx ctx
  | tail {source middle target} : Erasures source middle → EraseStep middle target →
      Erasures source target

theorem Erasures.single {source target} (step : EraseStep source target) :
    Erasures source target := .tail (.refl source) step

theorem Erasures.trans {source middle target} (first : Erasures source middle)
    (second : Erasures middle target) : Erasures source target := by
  induction second with
  | refl => exact first
  | tail _ step ih => exact .tail ih step

/-- Worklist updates affect no part of the erased context. -/
theorem eraseOp_ctx (rewriter : PatternRewriter OpCode) (operation : OperationPtr)
    (inBounds : operation.InBounds rewriter.ctx.raw)
    (dead : operation.isTriviallyDead rewriter.ctx.raw) :
    (rewriter.eraseOp operation dead.1 dead.2.1 inBounds).ctx =
      WfRewriter.eraseOp rewriter.ctx operation dead.1 dead.2.1 inBounds := by
  rfl

theorem eraseOp_erasures (rewriter : PatternRewriter OpCode) (operation : OperationPtr)
    (inBounds : operation.InBounds rewriter.ctx.raw)
    (dead : operation.isTriviallyDead rewriter.ctx.raw) :
    Erasures rewriter.ctx (rewriter.eraseOp operation dead.1 dead.2.1 inBounds).ctx := by
  rw [eraseOp_ctx rewriter operation inBounds dead]
  exact .single (.erase rewriter.ctx operation inBounds dead)

theorem eliminateDeadOp_erasures (rewriter next : PatternRewriter OpCode)
    (operation : OperationPtr) (inBounds : operation.InBounds rewriter.ctx.raw)
    (success : eliminateDeadOp rewriter operation inBounds = some next) :
    Erasures rewriter.ctx next.ctx := by
  unfold eliminateDeadOp at success
  split at success
  next dead =>
    simp [PatternRewriter.eraseOp!, inBounds, dead.1, dead.2.1] at success
    subst next
    exact eraseOp_erasures rewriter operation inBounds dead
  next notDead =>
    simp at success
    subst next
    exact .refl _

/-- The singleton DCE pattern leaves a live operation and its context alone. -/
theorem greedyPattern_live (rewriter : PatternRewriter OpCode) (operation : OperationPtr)
    (inBounds : operation.InBounds rewriter.ctx.raw)
    (live : ¬operation.isTriviallyDead rewriter.ctx.raw) :
    RewritePattern.GreedyRewritePattern #[eliminateDeadOp] rewriter operation inBounds =
      some rewriter := by
  simp [RewritePattern.GreedyRewritePattern, eliminateDeadOp, inBounds, live]

theorem greedyPattern_eq_eliminateDeadOp (rewriter : PatternRewriter OpCode)
    (operation : OperationPtr) (inBounds : operation.InBounds rewriter.ctx.raw) :
    RewritePattern.GreedyRewritePattern #[eliminateDeadOp] rewriter operation inBounds =
      eliminateDeadOp rewriter operation inBounds := by
  by_cases dead : operation.isTriviallyDead rewriter.ctx.raw
  · simp [RewritePattern.GreedyRewritePattern, eliminateDeadOp, inBounds, dead,
      PatternRewriter.eraseOp!, PatternRewriter.eraseOp]
    simp [ite_eq_left dead]
  · simp [RewritePattern.GreedyRewritePattern, eliminateDeadOp, inBounds, dead]

theorem greedyPattern_erasures (rewriter next : PatternRewriter OpCode)
    (operation : OperationPtr) (inBounds : operation.InBounds rewriter.ctx.raw)
    (success : RewritePattern.GreedyRewritePattern #[eliminateDeadOp]
      rewriter operation inBounds = some next) : Erasures rewriter.ctx next.ctx := by
  rw [greedyPattern_eq_eliminateDeadOp] at success
  exact eliminateDeadOp_erasures rewriter next operation inBounds success

private theorem popWhile_size_le {α : Type} (predicate : α → Bool) (stack : Array α) :
    (stack.popWhile predicate).size ≤ stack.size := by
  fun_induction Array.popWhile <;> simp_all <;> omega

/-- A nonempty worklist consumes at least one stack position, including any
trailing tombstones removed by `popWhile`. -/
theorem worklist_pop_decreases (worklist : PatternRewriter.Worklist)
    (nonempty : worklist.isEmpty = false) :
    worklist.pop.2.stack.size < worklist.stack.size := by
  have index_nonempty : worklist.indexInStack.isEmpty = false := by
    simpa [PatternRewriter.Worklist.isEmpty, Std.HashMap.isEmpty_eq_size_eq_zero] using nonempty
  obtain ⟨operation, member⟩ := Std.HashMap.isEmpty_eq_false_iff_exists_mem.mp index_nonempty
  have slot := worklist.wf_index operation worklist.indexInStack[operation]
    (Std.HashMap.getElem?_eq_some_getElem member)
  obtain ⟨inBounds, _⟩ := Array.getElem?_eq_some_iff.mp slot
  have positive : 0 < worklist.stack.size := by omega
  have trimmed := popWhile_size_le (fun operation : Option OperationPtr => operation = none)
    worklist.stack
  unfold PatternRewriter.Worklist.pop
  dsimp only
  split <;> simp_all
  omega

theorem eraseOp_inBounds_iff (ctx : WfIRContext OpCode) (operation other : OperationPtr)
    (inBounds : operation.InBounds ctx.raw) (dead : operation.isTriviallyDead ctx.raw) :
    other.InBounds (WfRewriter.eraseOp ctx operation dead.1 dead.2.1 inBounds).raw ↔
      other.InBounds ctx.raw ∧ other ≠ operation := by
  simp only [WfRewriter.eraseOp]
  constructor
  · intro survivor
    have different : other ≠ operation := by
      unfold Rewriter.eraseOp at survivor
      exact OperationPtr.InBounds.ne_of_inBounds_OperationPtr_dealloc survivor
    exact ⟨(Rewriter.eraseOp_inBounds (ctx := ctx.raw) (op := operation)
      (.operation other) different).mp survivor, different⟩
  · rintro ⟨survivor, different⟩
    exact (Rewriter.eraseOp_inBounds (ctx := ctx.raw) (op := operation)
      (.operation other) different).mpr survivor

/-- Erasure removes exactly one live operation, regardless of linked-list and
use-list updates performed while detaching it. -/
theorem eraseOp_operation_count (ctx : WfIRContext OpCode) (operation : OperationPtr)
    (inBounds : operation.InBounds ctx.raw) (dead : operation.isTriviallyDead ctx.raw) :
    (WfRewriter.eraseOp ctx operation dead.1 dead.2.1 inBounds).raw.operations.size + 1 =
      ctx.raw.operations.size := by
  have keys :
      (WfRewriter.eraseOp ctx operation dead.1 dead.2.1 inBounds).raw.operations.keys.Perm
        (ctx.raw.operations.erase operation).keys := by
    apply (List.perm_ext_iff_of_nodup Std.HashMap.nodup_keys Std.HashMap.nodup_keys).mpr
    intro other
    simp only [Std.HashMap.mem_keys, Std.HashMap.mem_erase]
    simpa [OperationPtr.inBounds_def, and_comm, ne_comm] using
      eraseOp_inBounds_iff ctx operation other inBounds dead
  have same_size := keys.length_eq
  simp only [Std.HashMap.length_keys, Std.HashMap.size_erase,
    ite_eq_left (OperationPtr.inBounds_def.mp inBounds)] at same_size
  have positive : 0 < ctx.raw.operations.size := by
    have not_empty : ctx.raw.operations.isEmpty = false :=
      Std.HashMap.isEmpty_eq_false_iff_exists_mem.mpr
        ⟨operation, OperationPtr.inBounds_def.mp inBounds⟩
    have nonzero : ctx.raw.operations.size ≠ 0 := by
      simpa [Std.HashMap.isEmpty_eq_size_eq_zero] using not_empty
    omega
  omega

def worklistMeasure (rewriter : PatternRewriter OpCode) : Nat × Nat :=
  (rewriter.ctx.raw.operations.size, rewriter.worklist.stack.size)

def pattern : RewritePattern OpCode := RewritePattern.GreedyRewritePattern #[eliminateDeadOp]

/-- Dead erasure decreases the first lexicographic component. A live operation
leaves the context alone and consumes a position in the popped worklist. -/
theorem worklistStep_decreases (rewriter next : PatternRewriter OpCode)
    (success : RewritePattern.worklistStep pattern () rewriter = some (.yield next)) :
    Prod.Lex Nat.lt Nat.lt (worklistMeasure next) (worklistMeasure rewriter) := by
  unfold RewritePattern.worklistStep at success
  split at success
  next nonempty =>
    cases hpop : rewriter.worklist.pop with
    | mk operation worklist =>
      simp only [hpop] at success
      split at success
      next inBounds =>
        split at success
        next dead =>
          simp at success
          subst next
          apply Prod.Lex.left
          rw [eraseOp_ctx { rewriter with worklist } _ inBounds dead]
          have count := eraseOp_operation_count rewriter.ctx operation.get! inBounds dead
          change (WfRewriter.eraseOp rewriter.ctx operation.get! dead.1 dead.2.1 inBounds).raw.operations.size <
            rewriter.ctx.raw.operations.size
          omega
        next live =>
          simp only [pattern, greedyPattern_live { rewriter with worklist } _ inBounds live] at success
          simp at success
          subst next
          apply Prod.Lex.right
          have smaller := worklist_pop_decreases rewriter.worklist (by simpa using nonempty)
          simpa [hpop] using smaller
      next outOfBounds => simp at success
  next empty => simp at success

private def SweepProgress (initialCount : Nat) (rewriter : PatternRewriter OpCode) : Prop :=
  rewriter.ctx.raw.operations.size ≤ initialCount ∧
    (rewriter.hasDoneAction = true → rewriter.ctx.raw.operations.size < initialCount)

private theorem worklistStep_progress (initialCount : Nat)
    (rewriter next : PatternRewriter OpCode) (exit : Bool)
    (progress : SweepProgress initialCount rewriter)
    (success : RewritePattern.worklistStep pattern () rewriter =
      some (if exit then .done next else .yield next)) : SweepProgress initialCount next := by
  unfold RewritePattern.worklistStep at success
  split at success
  next nonempty =>
    cases hpop : rewriter.worklist.pop with
    | mk operation worklist =>
      simp only [hpop] at success
      split at success
      next inBounds =>
        split at success
        next dead =>
          cases exit <;> simp at success
          subst next
          have count := eraseOp_operation_count rewriter.ctx operation.get! inBounds dead
          unfold SweepProgress
          rw [eraseOp_ctx { rewriter with worklist } operation.get! inBounds dead]
          change (WfRewriter.eraseOp rewriter.ctx operation.get! dead.1 dead.2.1 inBounds).raw.operations.size ≤ initialCount ∧
            (true = true → (WfRewriter.eraseOp rewriter.ctx operation.get! dead.1 dead.2.1 inBounds).raw.operations.size < initialCount)
          have bounded := progress.1
          constructor <;> omega
        next live =>
          simp only [pattern, greedyPattern_live { rewriter with worklist } _ inBounds live] at success
          cases exit <;> simp at success
          subst next
          exact progress
      next outOfBounds => simp at success
  next empty =>
    cases exit <;> simp at success
    subst next
    exact progress

private theorem sweep_progress (ctx next : WfIRContext OpCode) (changed : Bool)
    (success : RewritePattern.greedySweep pattern ctx = some (changed, next)) :
    next.raw.operations.size ≤ ctx.raw.operations.size ∧
      (changed = true → next.raw.operations.size < ctx.raw.operations.size) := by
  unfold RewritePattern.greedySweep at success
  cases hloop : Lean.Loop.forIn {}
      ({ ctx, hasDoneAction := false, worklist := .createFromContext ctx } : PatternRewriter OpCode)
      (RewritePattern.worklistStep pattern) with
  | none => simp [hloop] at success
  | some result =>
    simp [hloop] at success
    have progress := option_loop_preserves (RewritePattern.worklistStep pattern)
      (SweepProgress ctx.raw.operations.size) worklistMeasure (Prod.Lex Nat.lt Nat.lt)
      (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf
      (fun state next hs hstep => ⟨worklistStep_progress _ state next false hs hstep,
        worklistStep_decreases state next hstep⟩)
      (fun state next hs hstep => worklistStep_progress _ state next true hs hstep)
      (by constructor <;> simp) hloop
    simpa only [SweepProgress, success.1, success.2] using progress

def contextMeasure (state : Bool × WfIRContext OpCode) : Nat × Nat :=
  (state.2.raw.operations.size, if state.1 then 1 else 0)

theorem contextStep_decreases (state next : Bool × WfIRContext OpCode)
    (success : RewritePattern.contextStep pattern () state = some (.yield next)) :
    Prod.Lex Nat.lt Nat.lt (contextMeasure next) (contextMeasure state) := by
  unfold RewritePattern.contextStep at success
  split at success
  next changed =>
    cases hsweep : RewritePattern.greedySweep pattern state.2 with
    | none => simp [hsweep] at success
    | some pair =>
      simp [hsweep] at success
      subst next
      obtain ⟨bounded, strict⟩ := sweep_progress state.2 pair.2 pair.1 hsweep
      by_cases same : pair.2.raw.operations.size = state.2.raw.operations.size
      · have unchanged : pair.1 = false := by
          cases h : pair.1 <;> simp_all
        unfold contextMeasure
        rw [same]
        apply Prod.Lex.right
        simp [unchanged, changed]
      · apply Prod.Lex.left
        change pair.2.raw.operations.size < state.2.raw.operations.size
        omega
  next unchanged => simp at success

/-- The actual DCE driver produces a finite syntactic deletion sequence.
Both termination variants are proved from operation count and worklist size;
no semantic refinement relation or semantic transitivity is assumed. -/
theorem applyInContext_erasures (ctx next : WfIRContext OpCode)
    (success : RewritePattern.applyInContext pattern ctx = some next) : Erasures ctx next := by
  exact RewritePattern.applyInContext_preserves pattern Erasures Erasures.refl
    (fun _ _ _ => Erasures.trans) eraseOp_erasures greedyPattern_erasures
    worklistMeasure (Prod.Lex Nat.lt Nat.lt) (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf
    worklistStep_decreases
    contextMeasure (Prod.Lex Nat.lt Nat.lt) (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf
    contextStep_decreases ctx next success


end Veir.DCE
