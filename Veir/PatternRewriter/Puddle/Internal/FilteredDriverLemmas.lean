module
public import Veir.PatternRewriter.Puddle.Internal.ModuleEligibility
public import Veir.PatternRewriter.Puddle.Internal.ScopedWorklist
import all Veir.PatternRewriter.Basic
import all Veir.PatternRewriter.Internal.Traversal

public section
namespace Veir
variable {OpInfo : Type} [HasOpInfo OpInfo]

/-- A successful dispatch preserves both the worklist predicate and the context invariant. -/
structure RewritePattern.ScopedContextStepPreserves (pattern : RewritePattern OpInfo)
    (scope : WfIRContext OpInfo → OperationPtr → Prop)
    (invariant : WfIRContext OpInfo → Prop)
    (relation : WfIRContext OpInfo → WfIRContext OpInfo → Prop) : Prop where
  patternStep : ∀ (before : PatternRewriter OpInfo) (op : OperationPtr)
    (opIn : op.InBounds before.ctx.raw) (after : PatternRewriter OpInfo),
    invariant before.ctx → before.worklist.All (scope before.ctx) → scope before.ctx op →
    Puddle.rootEligible before.ctx op = true → pattern before op opIn = some after →
    (invariant after.ctx ∧ after.worklist.All (scope after.ctx)) ∧ relation before.ctx after.ctx
  deadStep : ∀ (before : PatternRewriter OpInfo) (op : OperationPtr)
    (opIn : op.InBounds before.ctx.raw) (dead : op.isTriviallyDead before.ctx.raw)
    (_noAllocation : (op.getEffects before.ctx.raw).allocates = false),
    invariant before.ctx → before.worklist.All (scope before.ctx) → scope before.ctx op →
    Puddle.rootEligible before.ctx op = true →
    let after := before.eraseOp op dead.1 dead.2.1 opIn
    (invariant after.ctx ∧ after.worklist.All (scope after.ctx)) ∧ relation before.ctx after.ctx

theorem RewritePattern.worklistStep_preserves_scope
    (pattern : RewritePattern OpInfo)
    (scope : WfIRContext OpInfo → OperationPtr → Prop)
    (invariant : WfIRContext OpInfo → Prop)
    (relation : WfIRContext OpInfo → WfIRContext OpInfo → Prop)
    (steps : ScopedContextStepPreserves pattern scope invariant relation)
    (refl : ∀ ctx, invariant ctx → relation ctx ctx)
    {before after : PatternRewriter OpInfo} (initial : invariant before.ctx)
    (all : before.worklist.All (scope before.ctx))
    (run : pattern.worklistStep before = some after) :
    (invariant after.ctx ∧ after.worklist.All (scope after.ctx)) ∧ relation before.ctx after.ctx := by
  unfold worklistStep at run
  dsimp only at run
  split at run
  next op popped =>
    have chosen := all.pop.2 op popped
    split at run
    next bound =>
      split at run
      next =>
        cases run
        exact ⟨⟨initial, all.pop.1⟩, refl _ initial⟩
      next leaf =>
        split at run
        next =>
          cases run
          exact ⟨⟨initial, all.pop.1⟩, refl _ initial⟩
        next ssa =>
          have accepted : Puddle.rootEligible before.ctx op = true := by
            simp_all [Puddle.rootEligible]
          split at run
          next dead =>
            cases run
            exact steps.deadStep {before with worklist := before.worklist.pop.2} op bound dead.1 dead.2
              initial all.pop.1 chosen accepted
          next => exact steps.patternStep {before with worklist := before.worklist.pop.2} op bound _
                    initial all.pop.1 chosen accepted run
    next => cases run
  · cases run

/-- Every successful execution of the unbounded driver has a finite proof by
fixpoint induction. No termination, worklist ordering, or fairness assumption is needed. -/
theorem RewritePattern.runWorklist_preserves_scope
    (pattern : RewritePattern OpInfo)
    (scope : WfIRContext OpInfo → OperationPtr → Prop)
    (invariant : WfIRContext OpInfo → Prop)
    (relation : WfIRContext OpInfo → WfIRContext OpInfo → Prop)
    (steps : ScopedContextStepPreserves pattern scope invariant relation)
    (refl : ∀ ctx, invariant ctx → relation ctx ctx)
    (trans : ∀ a b c, relation a b → relation b c → relation a c) :
    ∀ (before : PatternRewriter OpInfo), (invariant before.ctx ∧ before.worklist.All (scope before.ctx)) → ∀ (after : PatternRewriter OpInfo),
      pattern.runWorklist before = some after →
      (invariant after.ctx ∧ after.worklist.All (scope after.ctx)) ∧ relation before.ctx after.ctx := by
  apply runWorklist.fixpoint_induct pattern
    (fun candidate => ∀ (before : PatternRewriter OpInfo), (invariant before.ctx ∧ before.worklist.All (scope before.ctx)) → ∀ (after : PatternRewriter OpInfo),
      candidate before = some after → (invariant after.ctx ∧ after.worklist.All (scope after.ctx)) ∧ relation before.ctx after.ctx)
  · exact Lean.Order.admissible_pi_apply
      (fun (before : PatternRewriter OpInfo) output => (invariant before.ctx ∧ before.worklist.All (scope before.ctx)) → ∀ (after : PatternRewriter OpInfo),
        output = some after → (invariant after.ctx ∧ after.worklist.All (scope after.ctx)) ∧ relation before.ctx after.ctx)
      (fun before => Lean.Order.admissible_pi _ (fun _ =>
        Lean.Order.admissible_pi _ (fun after => Lean.Order.Option.admissible_eq_some
          ((invariant after.ctx ∧ after.worklist.All (scope after.ctx)) ∧ relation before.ctx after.ctx) after)))
  · intro candidate induction before initial after outcome
    dsimp only at outcome
    split at outcome
    · cases outcome
      exact ⟨initial, refl _ initial.1⟩
    · obtain ⟨next, stepped, returned⟩ := Option.bind_eq_some_iff.mp outcome
      have nextFacts := pattern.worklistStep_preserves_scope scope invariant relation steps refl initial.1 initial.2 stepped
      have finalFacts := induction next nextFacts.1 after returned
      exact ⟨finalFacts.1, trans _ _ _ nextFacts.2 finalFacts.2⟩


/-- The semantic contract of one actual worklist round, including its automatic dead-code steps. -/
def RewritePattern.RoundPreserves (pattern : RewritePattern OpInfo) (root : OperationPtr)
    (invariant : WfIRContext OpInfo → Prop)
    (relation : WfIRContext OpInfo → WfIRContext OpInfo → Prop) : Prop :=
  ∀ before after changed, invariant before →
    pattern.applyOnceInContext before root = some (changed, after) →
    invariant after ∧ relation before after


private theorem list_forIn_invariant {α σ : Type} (items : List α)
    (body : α → σ → Option (ForInStep σ)) (property : σ → Prop)
    (step : ∀ item ∈ items, ∀ state, property state → ∀ result, body item state = some result → property result.value)
    (initial final : σ) (start : property initial)
    (success : forIn items initial body = some final) : property final := by
  induction items generalizing initial with
  | nil => cases success; exact start
  | cons head tail ih =>
    simp only [List.forIn_cons] at success
    cases first : body head initial with
    | none => simp [first, Bind.bind] at success
    | some result =>
      have post := step head (by simp) initial start result first
      cases result with
      | done final' =>
        simp only [first, Bind.bind, Option.bind, Pure.pure] at success
        cases success
        exact post
      | yield next =>
        simp only [first, Bind.bind, Option.bind] at success
        exact ih (fun item mem => step item (by simp [mem])) next post success

private theorem range_forIn_invariant {σ : Type} (bound : Nat)
    (body : Nat → σ → Option (ForInStep σ)) (property : σ → Prop)
    (step : ∀ item state, property state → ∀ result, body item state = some result → property result.value)
    (initial final : σ) (start : property initial)
    (success : forIn (0...bound) initial body = some final) : property final := by
  rw [forIn_eq_forIn', Std.Rco.forIn'_eq_forIn'_toList] at success
  have converted : forIn (0...bound).toList initial body = some final := by
    simpa only [forIn_eq_forIn'] using success
  exact list_forIn_invariant _ body property (fun item _ => step item) initial final start converted

theorem RewritePattern.applyInContext_preserves
    (pattern : RewritePattern OpInfo) (root : OperationPtr)
    (invariant : WfIRContext OpInfo → Prop)
    (relation : WfIRContext OpInfo → WfIRContext OpInfo → Prop)
    (round : pattern.RoundPreserves root invariant relation)
    (refl : ∀ ctx, invariant ctx → relation ctx ctx)
    (trans : ∀ a b c, relation a b → relation b c → relation a c)
    {before after : WfIRContext OpInfo} (initial : invariant before) (maxRounds : Nat)
    (success : pattern.applyInContext before root maxRounds = some after) :
    invariant after ∧ relation before after := by
  unfold applyInContext at success
  simp only [_root_.bind_pure] at success
  apply range_forIn_invariant maxRounds _ (fun ctx => invariant ctx ∧ relation before ctx)
    ?_ before after ⟨initial, refl before initial⟩ success
  intro item current prior result ran
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at ran
  obtain ⟨⟨changed, next⟩, roundRun, returned⟩ := ran
  have nextProperty := round current next changed prior.1 roundRun
  have related := trans before current next prior.2 nextProperty.2
  split at returned <;> simp only [Option.pure_def] at returned <;> cases returned
  all_goals exact ⟨nextProperty.1, related⟩

/-- A root with no regions to visit seeds an empty worklist in every round. -/
theorem RewritePattern.applyInContext_eq_of_no_regions (pattern : RewritePattern OpInfo)
    {before after : WfIRContext OpInfo} {root : OperationPtr} {maxRounds : Nat}
    (empty : ¬(root.InBounds before.raw ∧ 0 < root.getNumRegions! before.raw))
    (run : pattern.applyInContext before root maxRounds = some after) : after = before := by
  have seed : PatternRewriter.seedNestedReversePostOrder before.raw .empty root = .empty := by
    unfold PatternRewriter.seedNestedReversePostOrder PatternRewriter.foldNestedOperations
    split
    next inside =>
      have zero := Nat.eq_zero_of_not_pos (fun pos => empty ⟨inside, pos⟩)
      simp only [zero, PatternRewriter.walkRegions]
      rfl
    next => rfl
  have round : pattern.RoundPreserves root (· = before) (fun _ _ => True) := by
    rintro _ next changed rfl once
    unfold applyOnceInContext at once
    rw [seed] at once
    dsimp only at once
    rw [runWorklist.eq_1] at once
    have stop : PatternRewriter.Worklist.empty.isEmpty = true := by
      simp [PatternRewriter.Worklist.isEmpty, PatternRewriter.Worklist.empty]
    simp [stop] at once
    exact ⟨once.2.symm, trivial⟩
  exact (pattern.applyInContext_preserves root _ _ round (by simp) (by simp) rfl maxRounds run).1

/-- The actual round contract follows from the mutation branches of the actual worklist
runner. Seeding and the final flag projection do not change the context. -/
theorem RewritePattern.RoundPreserves.of_scopedContextSteps
    (pattern : RewritePattern OpInfo) (root : OperationPtr)
    (invariant : WfIRContext OpInfo → Prop)
    (relation : WfIRContext OpInfo → WfIRContext OpInfo → Prop)
    (scope : WfIRContext OpInfo → OperationPtr → Prop)
    (seed : ∀ ctx, invariant ctx → ∀ op : OperationPtr, (IRNode.operation root).Ancestor op ctx → scope ctx op)
    (steps : ScopedContextStepPreserves pattern scope invariant relation)
    (refl : ∀ ctx, invariant ctx → relation ctx ctx)
    (trans : ∀ a b c, relation a b → relation b c → relation a c) :
    pattern.RoundPreserves root invariant relation := by
  intro before after changed initial success
  unfold applyOnceInContext at success
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at success
  obtain ⟨final, run, returned⟩ := success
  cases returned
  have kept := pattern.runWorklist_preserves_scope scope invariant relation steps refl trans _
    ⟨initial, (PatternRewriter.seedNestedReversePostOrder_all before root).mono (seed before initial)⟩ final run
  exact ⟨kept.1.1, kept.2⟩

/-- The actual function-wise traversal composes the bounded rewriting rounds for every
function selected by the traversal, with no assumption on the collection order. -/
theorem RewritePattern.applyToFunctions_preserves
    (pattern : RewritePattern OpInfo) (root : OperationPtr)
    (invariant : WfIRContext OpInfo → Prop)
    (relation : WfIRContext OpInfo → WfIRContext OpInfo → Prop)
    {before after : WfIRContext OpInfo}
    (round : ∀ f : {op : OperationPtr // op.InBounds before.raw ∧ 0 < op.getNumRegions! before.raw ∧
      (IRNode.operation root).Ancestor op before}, pattern.RoundPreserves f.val invariant relation)
    (refl : ∀ ctx, invariant ctx → relation ctx ctx)
    (trans : ∀ a b c, relation a b → relation b c → relation a c)
    (initial : invariant before) (maxRounds : Nat)
    (success : pattern.applyToFunctions before root maxRounds = some after) :
    invariant after ∧ relation before after := by
  unfold applyToFunctions at success
  simp only [guard, Option.bind_eq_bind] at success
  split at success <;> try contradiction
  simp only [Option.pure_def, Option.bind_some] at success
  split at success
  · cases success; exact ⟨initial, refl _ initial⟩
  simp only [Option.bind_fun_some] at success
  rw [← Array.forIn_toList] at success
  apply list_forIn_invariant _ _ (fun ctx => invariant ctx ∧ relation before ctx)
    ?_ before after ⟨initial, refl before initial⟩ success
  intro function member current prior result ran
  have facts := PatternRewriter.collectNestedFunctions_scoped before root function (Array.mem_toList_iff.mp member)
  simp only [Option.bind_eq_some_iff] at ran
  obtain ⟨next, roundRun, returned⟩ := ran
  cases returned
  have nextFacts := pattern.applyInContext_preserves function invariant relation
    (round ⟨function, facts⟩) refl trans prior.1 maxRounds roundRun
  exact ⟨nextFacts.1, trans before current next prior.2 nextFacts.2⟩

end Veir
