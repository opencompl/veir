module
public import Veir.PatternRewriter.Basic
import all Veir.PatternRewriter.Basic
namespace Veir
public section
variable {OpInfo : Type} [HasOpInfo OpInfo]

def RewritePattern.NoActionPreservesContext (pattern : RewritePattern OpInfo) : Prop :=
  ∀ (before after : PatternRewriter OpInfo) (op : OperationPtr) (inBounds : op.InBounds before.ctx.raw),
    pattern before op inBounds = some after → after.hasDoneAction = false → after.ctx = before.ctx


private theorem list_forIn_stop_invariant {α σ : Type} (items : List α)
    (body : α → σ → Option (ForInStep σ)) (continuing stopped : σ → Prop)
    (step : ∀ item ∈ items, ∀ state, continuing state → ∀ result,
      body item state = some result →
      match result with | .yield next => continuing next | .done final => stopped final)
    (initial final : σ) (start : continuing initial)
    (success : forIn items initial body = some final) : continuing final ∨ stopped final := by
  induction items generalizing initial with
  | nil => cases success; exact Or.inl start
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
        exact Or.inr post
      | yield next =>
        simp only [first, Bind.bind, Option.bind] at success
        exact ih (fun item member => step item (by simp [member])) next post success

private theorem array_forIn_stop_invariant {α σ : Type} (items : Array α)
    (body : α → σ → Option (ForInStep σ)) (continuing stopped : σ → Prop)
    (step : ∀ item ∈ items, ∀ state, continuing state → ∀ result,
      body item state = some result →
      match result with | .yield next => continuing next | .done final => stopped final)
    (initial final : σ) (start : continuing initial)
    (success : forIn items initial body = some final) : continuing final ∨ stopped final := by
  exact list_forIn_stop_invariant items.toList body continuing stopped
    (fun item member => step item (by simpa using member)) initial final start
    (by simpa only [Array.forIn_toList] using success)

/-- Greedy application changes the context only by returning the successful result of one
member rule attempted in the original context. Earlier unsuccessful matches may change metadata. -/
theorem RewritePattern.greedy_success_origin
    (patterns : Array (RewritePattern OpInfo))
    {before after : PatternRewriter OpInfo} {op : OperationPtr} {inBounds : op.InBounds before.ctx.raw}
    (noAction : ∀ pattern ∈ patterns, ∀ (attempt result : PatternRewriter OpInfo)
      (attemptIn : op.InBounds attempt.ctx.raw), attempt.ctx = before.ctx →
      pattern attempt op attemptIn = some result → result.hasDoneAction = false → result.ctx = attempt.ctx)
    (success : GreedyRewritePattern patterns before op inBounds = some after) :
    after.ctx = before.ctx ∨
      ∃ pattern ∈ patterns, ∃ attempt : PatternRewriter OpInfo, attempt.ctx = before.ctx ∧
        ∃ attemptIn : op.InBounds attempt.ctx.raw, pattern attempt op attemptIn = some after := by
  let origin (result : PatternRewriter OpInfo) : Prop :=
    ∃ pattern ∈ patterns, ∃ attempt : PatternRewriter OpInfo, attempt.ctx = before.ctx ∧
      ∃ attemptIn : op.InBounds attempt.ctx.raw, pattern attempt op attemptIn = some result
  unfold GreedyRewritePattern at success
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at success
  obtain ⟨state, loop, returned⟩ := success
  have loopInvariant := array_forIn_stop_invariant patterns _
    (fun state : Option (PatternRewriter OpInfo) × PatternRewriter OpInfo =>
      state.1 = none ∧ state.2.ctx = before.ctx)
    (fun state => ∃ result, state.1 = some result ∧ origin result)
    ?_ _ state ⟨rfl, rfl⟩ loop
  · rcases loopInvariant with ⟨noWinner, context⟩ | ⟨winner, someWinner, fromMember⟩
    · simp only [noWinner, Option.pure_def] at returned
      cases returned
      exact Or.inl context
    · simp only [someWinner, Option.pure_def] at returned
      cases returned
      exact Or.inr fromMember
  · intro pattern member current currentInvariant result ran
    split at ran
    · rename_i currentIn
      split at ran
      · rename_i next nextRun
        split at ran
        · rename_i didAction
          simp only [Option.pure_def] at ran
          cases ran
          exact ⟨next, rfl, pattern, member, current.2, currentInvariant.2, currentIn, nextRun⟩
        · rename_i noActionFlag
          simp only [Option.pure_def] at ran
          cases ran
          have noActionEq : next.hasDoneAction = false := by simpa using noActionFlag
          exact ⟨rfl, (noAction pattern member current.2 next currentIn currentInvariant.2 nextRun noActionEq).trans currentInvariant.2⟩
      · cases ran
    · cases ran

/-- Any context relation stable under a successful member rule is stable under the actual
greedy combinator. Since greedy stops at its first action, no transitivity premise is needed. -/
theorem RewritePattern.greedy_context_relation
    (patterns : Array (RewritePattern OpInfo))
    (relation : WfIRContext OpInfo → WfIRContext OpInfo → Prop)
    {before after : PatternRewriter OpInfo} {op : OperationPtr} {inBounds : op.InBounds before.ctx.raw}
    (same : relation before.ctx before.ctx)
    (noAction : ∀ pattern ∈ patterns, ∀ (attempt result : PatternRewriter OpInfo)
      (attemptIn : op.InBounds attempt.ctx.raw), attempt.ctx = before.ctx →
      pattern attempt op attemptIn = some result → result.hasDoneAction = false → result.ctx = attempt.ctx)
    (memberStep : ∀ pattern ∈ patterns, ∀ (attempt result : PatternRewriter OpInfo)
      (attemptIn : op.InBounds attempt.ctx.raw), attempt.ctx = before.ctx →
      pattern attempt op attemptIn = some result → relation attempt.ctx result.ctx)
    (success : GreedyRewritePattern patterns before op inBounds = some after) :
    relation before.ctx after.ctx := by
  rcases greedy_success_origin patterns noAction success with unchanged | ⟨pattern, member, attempt, context, attemptIn, ran⟩
  · simpa only [unchanged] using same
  · have step := memberStep pattern member attempt after attemptIn context ran
    simpa only [context] using step

end
end Veir
