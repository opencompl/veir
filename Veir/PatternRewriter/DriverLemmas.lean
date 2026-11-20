module
public import Veir.PatternRewriter.Basic
public import Veir.PatternRewriter.WorklistLemmas
import all Veir.PatternRewriter.Basic
namespace Veir
public section
variable {OpInfo : Type} [HasOpInfo OpInfo]

/-- The semantic contract of one actual worklist round, including its automatic dead-code steps. -/
def RewritePattern.RoundPreserves (pattern : RewritePattern OpInfo) (root : OperationPtr)
    (invariant : WfIRContext OpInfo → Prop)
    (relation : WfIRContext OpInfo → WfIRContext OpInfo → Prop) : Prop :=
  ∀ before after changed, invariant before →
    pattern.applyOnceInContext before root = some (changed, after) →
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

/-- The actual round contract follows from the mutation branches of the actual worklist
runner. Seeding and the final flag projection do not change the context. -/
theorem RewritePattern.RoundPreserves.of_contextSteps
    (pattern : RewritePattern OpInfo) (root : OperationPtr)
    (invariant : WfIRContext OpInfo → Prop)
    (relation : WfIRContext OpInfo → WfIRContext OpInfo → Prop)
    (steps : ContextStepPreserves pattern invariant relation)
    (refl : ∀ ctx, invariant ctx → relation ctx ctx)
    (trans : ∀ a b c, relation a b → relation b c → relation a c) :
    pattern.RoundPreserves root invariant relation := by
  intro before after changed initial success
  unfold applyOnceInContext at success
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at success
  obtain ⟨final, run, returned⟩ := success
  cases returned
  exact pattern.runWorklist_preserves invariant relation steps refl trans _ initial final run

/-- All bounded rounds preserve the invariant and compose the contextual relation. -/
theorem RewritePattern.applyInContext_preserves_of_contextSteps
    (pattern : RewritePattern OpInfo) (root : OperationPtr)
    (invariant : WfIRContext OpInfo → Prop)
    (relation : WfIRContext OpInfo → WfIRContext OpInfo → Prop)
    (steps : ContextStepPreserves pattern invariant relation)
    (refl : ∀ ctx, invariant ctx → relation ctx ctx)
    (trans : ∀ a b c, relation a b → relation b c → relation a c)
    {before after : WfIRContext OpInfo} (initial : invariant before) (maxRounds : Nat)
    (success : pattern.applyInContext before root maxRounds = some after) :
    invariant after ∧ relation before after :=
  pattern.applyInContext_preserves root invariant relation
    (RoundPreserves.of_contextSteps pattern root invariant relation steps refl trans)
    refl trans initial maxRounds success

/-- The actual function-wise traversal composes the bounded rewriting rounds for every
function selected by the traversal, with no assumption on the collection order. -/
theorem RewritePattern.applyToFunctions_preserves_of_contextSteps
    (pattern : RewritePattern OpInfo) (root : OperationPtr)
    (invariant : WfIRContext OpInfo → Prop)
    (relation : WfIRContext OpInfo → WfIRContext OpInfo → Prop)
    (steps : ContextStepPreserves pattern invariant relation)
    (refl : ∀ ctx, invariant ctx → relation ctx ctx)
    (trans : ∀ a b c, relation a b → relation b c → relation a c)
    {before after : WfIRContext OpInfo} (initial : invariant before) (maxRounds : Nat)
    (success : pattern.applyToFunctions before root maxRounds = some after) :
    invariant after ∧ relation before after := by
  unfold applyToFunctions at success
  simp only [_root_.bind_pure] at success
  rw [← Array.forIn_toList] at success
  apply list_forIn_invariant _ _ (fun ctx => invariant ctx ∧ relation before ctx)
    ?_ before after ⟨initial, refl before initial⟩ success
  intro function current prior result ran
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at ran
  obtain ⟨next, roundRun, returned⟩ := ran
  cases returned
  have nextFacts := pattern.applyInContext_preserves_of_contextSteps function invariant relation
    steps refl trans prior.1 maxRounds roundRun
  exact ⟨nextFacts.1, trans before current next prior.2 nextFacts.2⟩

end
end Veir
