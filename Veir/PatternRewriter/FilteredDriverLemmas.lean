module
public import Veir.PatternRewriter.Basic
import all Veir.PatternRewriter.Basic

public section
namespace Veir
variable {OpInfo : Type} [HasOpInfo OpInfo]

/-- Context-level obligations for the two actual mutation branches of the worklist driver. -/
structure RewritePattern.ContextStepPreservesIf (pattern : RewritePattern OpInfo)
    (eligible : WfIRContext OpInfo → OperationPtr → Bool)
    (invariant : WfIRContext OpInfo → Prop)
    (relation : WfIRContext OpInfo → WfIRContext OpInfo → Prop) : Prop where
  patternStep : ∀ (before : PatternRewriter OpInfo) (op : OperationPtr)
    (opIn : op.InBounds before.ctx.raw) (after : PatternRewriter OpInfo),
    invariant before.ctx → eligible before.ctx op = true → pattern before op opIn = some after →
      invariant after.ctx ∧ relation before.ctx after.ctx
  deadStep : ∀ (before : PatternRewriter OpInfo) (op : OperationPtr)
    (opIn : op.InBounds before.ctx.raw) (dead : op.isTriviallyDead before.ctx.raw)
    (_noAllocation : (op.getEffects before.ctx.raw).allocates = false),
    invariant before.ctx → eligible before.ctx op = true →
      invariant (before.eraseOp op dead.1 dead.2.1 opIn).ctx ∧
      relation before.ctx (before.eraseOp op dead.1 dead.2.1 opIn).ctx

/-- Popping only changes the worklist; either successful dispatch branch satisfies
its corresponding concrete pattern or dead-operation obligation. -/
theorem RewritePattern.worklistStepIf_preserves
    (pattern : RewritePattern OpInfo) (eligible : WfIRContext OpInfo → OperationPtr → Bool)
    (invariant : WfIRContext OpInfo → Prop)
    (relation : WfIRContext OpInfo → WfIRContext OpInfo → Prop)
    (steps : ContextStepPreservesIf pattern eligible invariant relation)
    (refl : ∀ ctx, invariant ctx → relation ctx ctx)
    {before after : PatternRewriter OpInfo} (initial : invariant before.ctx)
    (run : pattern.worklistStepIf eligible before = some after) :
    invariant after.ctx ∧ relation before.ctx after.ctx := by
  unfold worklistStepIf at run
  dsimp only at run
  split at run
  next opIn =>
    split at run
    next accepted =>
      unfold worklistStep at run
      dsimp only at run
      split at run
      next bound =>
        split at run
        next dead =>
          cases run
          exact steps.deadStep { before with worklist := before.worklist.pop.2 } _ bound dead.1 dead.2 initial accepted
        next notDead =>
          exact steps.patternStep { before with worklist := before.worklist.pop.2 } _ bound _ initial accepted run
      next outside => contradiction
    next rejected =>
      cases run
      exact ⟨initial, refl _ initial⟩
  next outside => cases run

/-- Every successful execution of the unbounded driver has a finite proof by
fixpoint induction. No termination, worklist ordering, or fairness assumption is needed. -/
theorem RewritePattern.runWorklistIf_preserves
    (pattern : RewritePattern OpInfo) (eligible : WfIRContext OpInfo → OperationPtr → Bool)
    (invariant : WfIRContext OpInfo → Prop)
    (relation : WfIRContext OpInfo → WfIRContext OpInfo → Prop)
    (steps : ContextStepPreservesIf pattern eligible invariant relation)
    (refl : ∀ ctx, invariant ctx → relation ctx ctx)
    (trans : ∀ a b c, relation a b → relation b c → relation a c) :
    ∀ (before : PatternRewriter OpInfo), invariant before.ctx → ∀ (after : PatternRewriter OpInfo),
      pattern.runWorklistIf eligible before = some after →
      invariant after.ctx ∧ relation before.ctx after.ctx := by
  apply runWorklistIf.fixpoint_induct pattern eligible
    (fun candidate => ∀ (before : PatternRewriter OpInfo), invariant before.ctx → ∀ (after : PatternRewriter OpInfo),
      candidate before = some after → invariant after.ctx ∧ relation before.ctx after.ctx)
  · exact Lean.Order.admissible_pi_apply
      (fun (before : PatternRewriter OpInfo) output => invariant before.ctx → ∀ (after : PatternRewriter OpInfo),
        output = some after → invariant after.ctx ∧ relation before.ctx after.ctx)
      (fun before => Lean.Order.admissible_pi _ (fun _ =>
        Lean.Order.admissible_pi _ (fun after => Lean.Order.Option.admissible_eq_some
          (invariant after.ctx ∧ relation before.ctx after.ctx) after)))
  · intro candidate induction before initial after outcome
    dsimp only at outcome
    split at outcome
    · cases outcome
      exact ⟨initial, refl _ initial⟩
    · obtain ⟨next, stepped, returned⟩ := Option.bind_eq_some_iff.mp outcome
      have nextFacts := pattern.worklistStepIf_preserves eligible invariant relation steps refl initial stepped
      have finalFacts := induction next nextFacts.1 after returned
      exact ⟨finalFacts.1, trans _ _ _ nextFacts.2 finalFacts.2⟩


/-- The semantic contract of one actual worklist round, including its automatic dead-code steps. -/
def RewritePattern.RoundPreservesIf (pattern : RewritePattern OpInfo) (root : OperationPtr)
    (eligible : WfIRContext OpInfo → OperationPtr → Bool)
    (invariant : WfIRContext OpInfo → Prop)
    (relation : WfIRContext OpInfo → WfIRContext OpInfo → Prop) : Prop :=
  ∀ before after changed, invariant before →
    pattern.applyOnceInContextIf eligible before root = some (changed, after) →
    invariant after ∧ relation before after


private theorem list_forIn_invariant {α σ : Type} (items : List α)
    (body : α → σ → Option (ForInStep σ)) (property : σ → Prop)
    (step : ∀ item state, property state → ∀ result, body item state = some result → property result.value)
    (initial final : σ) (start : property initial)
    (success : forIn items initial body = some final) : property final := by
  induction items generalizing initial with
  | nil => cases success; exact start
  | cons head tail ih =>
    simp only [List.forIn_cons] at success
    cases first : body head initial with
    | none => simp [first, Bind.bind] at success
    | some result =>
      have post := step head initial start result first
      cases result with
      | done final' =>
        simp only [first, Bind.bind, Option.bind, Pure.pure] at success
        cases success
        exact post
      | yield next =>
        simp only [first, Bind.bind, Option.bind] at success
        exact ih next post success

private theorem range_forIn_invariant {σ : Type} (bound : Nat)
    (body : Nat → σ → Option (ForInStep σ)) (property : σ → Prop)
    (step : ∀ item state, property state → ∀ result, body item state = some result → property result.value)
    (initial final : σ) (start : property initial)
    (success : forIn (0...bound) initial body = some final) : property final := by
  rw [forIn_eq_forIn', Std.Rco.forIn'_eq_forIn'_toList] at success
  have converted : forIn (0...bound).toList initial body = some final := by
    simpa only [forIn_eq_forIn'] using success
  exact list_forIn_invariant _ body property step initial final start converted

theorem RewritePattern.applyInContextIf_preserves
    (pattern : RewritePattern OpInfo) (root : OperationPtr)
    (eligible : WfIRContext OpInfo → OperationPtr → Bool)
    (invariant : WfIRContext OpInfo → Prop)
    (relation : WfIRContext OpInfo → WfIRContext OpInfo → Prop)
    (round : pattern.RoundPreservesIf root eligible invariant relation)
    (refl : ∀ ctx, invariant ctx → relation ctx ctx)
    (trans : ∀ a b c, relation a b → relation b c → relation a c)
    {before after : WfIRContext OpInfo} (initial : invariant before) (maxRounds : Nat)
    (success : pattern.applyInContextIf eligible before root maxRounds = some after) :
    invariant after ∧ relation before after := by
  unfold applyInContextIf at success
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

/-- The actual round contract follows from the mutation branches of the actual worklist
runner. Seeding and the final flag projection do not change the context. -/
theorem RewritePattern.RoundPreservesIf.of_contextSteps
    (pattern : RewritePattern OpInfo) (root : OperationPtr)
    (eligible : WfIRContext OpInfo → OperationPtr → Bool)
    (invariant : WfIRContext OpInfo → Prop)
    (relation : WfIRContext OpInfo → WfIRContext OpInfo → Prop)
    (steps : ContextStepPreservesIf pattern eligible invariant relation)
    (refl : ∀ ctx, invariant ctx → relation ctx ctx)
    (trans : ∀ a b c, relation a b → relation b c → relation a c) :
    pattern.RoundPreservesIf root eligible invariant relation := by
  intro before after changed initial success
  unfold applyOnceInContextIf at success
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at success
  obtain ⟨final, run, returned⟩ := success
  cases returned
  exact pattern.runWorklistIf_preserves eligible invariant relation steps refl trans _ initial final run

/-- All bounded rounds preserve the invariant and compose the contextual relation. -/
theorem RewritePattern.applyInContextIf_preserves_of_contextSteps
    (pattern : RewritePattern OpInfo) (root : OperationPtr)
    (eligible : WfIRContext OpInfo → OperationPtr → Bool)
    (invariant : WfIRContext OpInfo → Prop)
    (relation : WfIRContext OpInfo → WfIRContext OpInfo → Prop)
    (steps : ContextStepPreservesIf pattern eligible invariant relation)
    (refl : ∀ ctx, invariant ctx → relation ctx ctx)
    (trans : ∀ a b c, relation a b → relation b c → relation a c)
    {before after : WfIRContext OpInfo} (initial : invariant before) (maxRounds : Nat)
    (success : pattern.applyInContextIf eligible before root maxRounds = some after) :
    invariant after ∧ relation before after :=
  pattern.applyInContextIf_preserves root eligible invariant relation
    (RoundPreservesIf.of_contextSteps pattern root eligible invariant relation steps refl trans)
    refl trans initial maxRounds success

/-- The actual function-wise traversal composes the bounded rewriting rounds for every
function selected by the traversal, with no assumption on the collection order. -/
theorem RewritePattern.applyToFunctionsIf_preserves_of_contextSteps
    (pattern : RewritePattern OpInfo) (root : OperationPtr)
    (eligible : WfIRContext OpInfo → OperationPtr → Bool)
    (invariant : WfIRContext OpInfo → Prop)
    (relation : WfIRContext OpInfo → WfIRContext OpInfo → Prop)
    (steps : ContextStepPreservesIf pattern eligible invariant relation)
    (refl : ∀ ctx, invariant ctx → relation ctx ctx)
    (trans : ∀ a b c, relation a b → relation b c → relation a c)
    {before after : WfIRContext OpInfo} (initial : invariant before) (maxRounds : Nat)
    (success : pattern.applyToFunctionsIf eligible before root maxRounds = some after) :
    invariant after ∧ relation before after := by
  unfold applyToFunctionsIf at success
  simp only [_root_.bind_pure] at success
  rw [← Array.forIn_toList] at success
  apply list_forIn_invariant _ _ (fun ctx => invariant ctx ∧ relation before ctx)
    ?_ before after ⟨initial, refl before initial⟩ success
  intro function current prior result ran
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at ran
  obtain ⟨next, roundRun, returned⟩ := ran
  cases returned
  have nextFacts := pattern.applyInContextIf_preserves_of_contextSteps function eligible invariant relation
    steps refl trans prior.1 maxRounds roundRun
  exact ⟨nextFacts.1, trans before current next prior.2 nextFacts.2⟩

end Veir
