module

public import Veir.PatternRewriter.Basic
import all Veir.PatternRewriter.Basic
import Init.Internal.Order.While

public section

namespace Veir

/-- A decreasing successful iteration preserves an invariant through an Option
loop. Failure is allowed; only successful loop results are asserted. -/
theorem option_loop_preserves {α β : Type} (body : Unit → α → Option (ForInStep α))
    (invariant : α → Prop) (measure : α → β) (less : β → β → Prop)
    (wellFounded : WellFounded less)
    (yield_step : ∀ state next, invariant state → body () state = some (.yield next) →
      invariant next ∧ less (measure next) (measure state))
    (done_step : ∀ state next, invariant state → body () state = some (.done next) →
      invariant next)
    {initial final : α} (initial_invariant : invariant initial)
    (success : Lean.Loop.forIn {} initial body = some final) : invariant final := by
  generalize hm : measure initial = current
  induction wellFounded.apply current generalizing initial final with
  | intro current _ ih =>
    rw [Lean.Loop.forIn_eq_of_monadTail] at success
    cases hbody : body () initial with
    | none => simp [hbody] at success
    | some result =>
      cases result with
      | done next =>
        simp [hbody] at success
        subst final
        exact done_step initial next initial_invariant hbody
      | yield next =>
        simp [hbody] at success
        obtain ⟨next_invariant, decrease⟩ :=
          yield_step initial next initial_invariant hbody
        exact ih (measure next) (by simpa [hm] using decrease) next_invariant success rfl

namespace RewritePattern

variable {OpInfo : Type} [HasOpInfo OpInfo]

/-- One iteration of the actual greedy worklist loop, including its automatic
dead-operation erasure before the supplied pattern. -/
def worklistStep (pattern : RewritePattern OpInfo) (_ : Unit)
    (rewriter : PatternRewriter OpInfo) : Option (ForInStep (PatternRewriter OpInfo)) := do
  if !rewriter.worklist.isEmpty then
    let (operation?, worklist) := rewriter.worklist.pop
    let operation := operation?.get!
    let rewriter := { rewriter with worklist }
    if inBounds : operation.InBounds rewriter.ctx.raw then
      if dead : operation.isTriviallyDead rewriter.ctx.raw then
        return .yield (rewriter.eraseOp operation dead.1 dead.2.1 inBounds)
      else
        return .yield (← pattern rewriter operation inBounds)
    else
      failure
  else
    return .done rewriter

/-- A proof-facing view of one sweep of the actual greedy driver. -/
def greedySweep (pattern : RewritePattern OpInfo) (ctx : WfIRContext OpInfo) :
    Option (Bool × WfIRContext OpInfo) := do
  let result ← Lean.Loop.forIn {}
    ({ ctx, hasDoneAction := false, worklist := .createFromContext ctx } : PatternRewriter OpInfo)
    (worklistStep pattern)
  pure (result.hasDoneAction, result.ctx)

private theorem applyOnceInContext_eq_loop (pattern : RewritePattern OpInfo) (ctx : WfIRContext OpInfo) :
    applyOnceInContext pattern ctx = greedySweep pattern ctx := by
  rfl

/-- The worklist bookkeeping does not change the context; only automatic
erasure and successful supplied patterns need preservation proofs. -/
theorem worklistStep_preserves (pattern : RewritePattern OpInfo)
    (relation : WfIRContext OpInfo → WfIRContext OpInfo → Prop)
    (refl : ∀ ctx, relation ctx ctx)
    (erase_preserves : ∀ (rewriter : PatternRewriter OpInfo) operation
      (inBounds : operation.InBounds rewriter.ctx.raw)
      (dead : operation.isTriviallyDead rewriter.ctx.raw),
      relation rewriter.ctx (rewriter.eraseOp operation dead.1 dead.2.1 inBounds).ctx)
    (pattern_preserves : ∀ (rewriter next : PatternRewriter OpInfo) operation
      (inBounds : operation.InBounds rewriter.ctx.raw),
      pattern rewriter operation inBounds = some next → relation rewriter.ctx next.ctx)
    (rewriter next : PatternRewriter OpInfo) (exit : Bool)
    (success : worklistStep pattern () rewriter =
      some (if exit then .done next else .yield next)) :
    relation rewriter.ctx next.ctx := by
  unfold worklistStep at success
  split at success
  · cases hpop : rewriter.worklist.pop with
    | mk operation worklist =>
      simp only [hpop] at success
      split at success
      next inBounds =>
        split at success
        next dead =>
          cases exit <;> simp at success
          subst next
          exact erase_preserves { rewriter with worklist } operation.get! inBounds dead
        next notDead =>
          cases hpattern : pattern { rewriter with worklist } operation.get! inBounds with
          | none => simp [hpattern] at success
          | some result =>
            cases exit <;> simp [hpattern] at success
            subst next
            exact pattern_preserves { rewriter with worklist } result operation.get! inBounds hpattern
      next outOfBounds => simp at success
  · cases exit <;> simp at success
    subst next
    exact refl _

/-- Local context preservation composes through a complete successful worklist
sweep. The supplied variant may use a lexicographic well-founded order. -/
theorem greedySweep_preserves {Variant : Type} (pattern : RewritePattern OpInfo)
    (relation : WfIRContext OpInfo → WfIRContext OpInfo → Prop)
    (refl : ∀ ctx, relation ctx ctx)
    (trans : ∀ a b c, relation a b → relation b c → relation a c)
    (erase_preserves : ∀ (rewriter : PatternRewriter OpInfo) operation
      (inBounds : operation.InBounds rewriter.ctx.raw)
      (dead : operation.isTriviallyDead rewriter.ctx.raw),
      relation rewriter.ctx (rewriter.eraseOp operation dead.1 dead.2.1 inBounds).ctx)
    (pattern_preserves : ∀ (rewriter next : PatternRewriter OpInfo) operation
      (inBounds : operation.InBounds rewriter.ctx.raw),
      pattern rewriter operation inBounds = some next → relation rewriter.ctx next.ctx)
    (measure : PatternRewriter OpInfo → Variant) (less : Variant → Variant → Prop)
    (wellFounded : WellFounded less)
    (decreases : ∀ state next, worklistStep pattern () state = some (.yield next) →
      less (measure next) (measure state))
    (ctx next : WfIRContext OpInfo) (changed : Bool)
    (success : greedySweep pattern ctx = some (changed, next)) : relation ctx next := by
  unfold greedySweep at success
  cases hloop : Lean.Loop.forIn {}
      ({ ctx, hasDoneAction := false, worklist := .createFromContext ctx } : PatternRewriter OpInfo)
      (worklistStep pattern) with
  | none => simp [hloop] at success
  | some result =>
    simp [hloop] at success
    have preserved := option_loop_preserves (worklistStep pattern)
      (fun state => relation ctx state.ctx) measure less wellFounded
      (fun state next hs hstep => ⟨trans _ _ _ hs
        (worklistStep_preserves pattern relation refl erase_preserves pattern_preserves
          state next false hstep), decreases state next hstep⟩)
      (fun state next hs hstep => trans _ _ _ hs
        (worklistStep_preserves pattern relation refl erase_preserves pattern_preserves
          state next true hstep))
      (refl ctx) hloop
    simpa [success.2] using preserved

/-- One iteration of the driver's outer loop over complete sweeps. -/
def contextStep (pattern : RewritePattern OpInfo) (_ : Unit)
    (state : Bool × WfIRContext OpInfo) : Option (ForInStep (Bool × WfIRContext OpInfo)) := do
  if state.1 then
    return .yield (← greedySweep pattern state.2)
  else
    return .done state

/-- Both loops here are the loops of `applyInContext`, by definitional equality. -/
theorem applyInContext_eq_loop (pattern : RewritePattern OpInfo) (ctx : WfIRContext OpInfo) :
    applyInContext pattern ctx = (do
      let result ← Lean.Loop.forIn {} (true, ctx) (contextStep pattern)
      pure result.2) := by
  rfl

/-- A context relation preserved by dead erasure and supplied patterns is
preserved by the actual greedy driver. The two variants discharge termination
of successful inner and outer iterations independently of semantic preservation. -/
theorem applyInContext_preserves {InnerVariant OuterVariant : Type}
    (pattern : RewritePattern OpInfo)
    (relation : WfIRContext OpInfo → WfIRContext OpInfo → Prop)
    (refl : ∀ ctx, relation ctx ctx)
    (trans : ∀ a b c, relation a b → relation b c → relation a c)
    (erase_preserves : ∀ (rewriter : PatternRewriter OpInfo) operation
      (inBounds : operation.InBounds rewriter.ctx.raw)
      (dead : operation.isTriviallyDead rewriter.ctx.raw),
      relation rewriter.ctx (rewriter.eraseOp operation dead.1 dead.2.1 inBounds).ctx)
    (pattern_preserves : ∀ (rewriter next : PatternRewriter OpInfo) operation
      (inBounds : operation.InBounds rewriter.ctx.raw),
      pattern rewriter operation inBounds = some next → relation rewriter.ctx next.ctx)
    (innerMeasure : PatternRewriter OpInfo → InnerVariant)
    (innerLess : InnerVariant → InnerVariant → Prop) (innerWellFounded : WellFounded innerLess)
    (innerDecreases : ∀ state next, worklistStep pattern () state = some (.yield next) →
      innerLess (innerMeasure next) (innerMeasure state))
    (outerMeasure : Bool × WfIRContext OpInfo → OuterVariant)
    (outerLess : OuterVariant → OuterVariant → Prop) (outerWellFounded : WellFounded outerLess)
    (outerDecreases : ∀ state next, contextStep pattern () state = some (.yield next) →
      outerLess (outerMeasure next) (outerMeasure state))
    (ctx next : WfIRContext OpInfo) (success : applyInContext pattern ctx = some next) :
    relation ctx next := by
  have step_preserves (state result : Bool × WfIRContext OpInfo) (exit : Bool)
      (hstep : contextStep pattern () state =
        some (if exit then .done result else .yield result)) : relation state.2 result.2 := by
    unfold contextStep at hstep
    split at hstep
    · cases hsweep : greedySweep pattern state.2 with
      | none => simp [hsweep] at hstep
      | some pair =>
        cases exit <;> simp [hsweep] at hstep
        subst result
        exact greedySweep_preserves pattern relation refl trans erase_preserves pattern_preserves
          innerMeasure innerLess innerWellFounded innerDecreases _ _ _ hsweep
    · cases exit <;> simp at hstep
      subst result
      exact refl _
  rw [applyInContext_eq_loop] at success
  cases hloop : Lean.Loop.forIn {} (true, ctx) (contextStep pattern) with
  | none => simp [hloop] at success
  | some result =>
    simp [hloop] at success
    have preserved := option_loop_preserves (contextStep pattern)
      (fun state => relation ctx state.2) outerMeasure outerLess outerWellFounded
      (fun state next hs hstep => ⟨trans _ _ _ hs (step_preserves state next false hstep),
        outerDecreases state next hstep⟩)
      (fun state next hs hstep => trans _ _ _ hs (step_preserves state next true hstep))
      (refl ctx) hloop
    simpa [success] using preserved


end RewritePattern

end Veir
