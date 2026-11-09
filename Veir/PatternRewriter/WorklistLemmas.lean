module
public import Veir.PatternRewriter.Basic
import all Veir.PatternRewriter.Basic

public section
namespace Veir
variable {OpInfo : Type} [HasOpInfo OpInfo]

/-- Context-level obligations for the two actual mutation branches of the worklist driver. -/
structure RewritePattern.ContextStepPreserves (pattern : RewritePattern OpInfo)
    (invariant : WfIRContext OpInfo → Prop)
    (relation : WfIRContext OpInfo → WfIRContext OpInfo → Prop) : Prop where
  patternStep : ∀ (before : PatternRewriter OpInfo) (op : OperationPtr)
    (opIn : op.InBounds before.ctx.raw) (after : PatternRewriter OpInfo),
    invariant before.ctx → pattern before op opIn = some after →
      invariant after.ctx ∧ relation before.ctx after.ctx
  deadStep : ∀ (before : PatternRewriter OpInfo) (op : OperationPtr)
    (opIn : op.InBounds before.ctx.raw) (dead : op.isTriviallyDead before.ctx.raw)
    (_noAllocation : (op.getEffects before.ctx.raw).allocates = false),
    invariant before.ctx →
      invariant (before.eraseOp op dead.1 dead.2.1 opIn).ctx ∧
      relation before.ctx (before.eraseOp op dead.1 dead.2.1 opIn).ctx

/-- Popping only changes the worklist; either successful dispatch branch satisfies
its corresponding concrete pattern or dead-operation obligation. -/
theorem RewritePattern.worklistStep_preserves
    (pattern : RewritePattern OpInfo) (invariant : WfIRContext OpInfo → Prop)
    (relation : WfIRContext OpInfo → WfIRContext OpInfo → Prop)
    (steps : ContextStepPreserves pattern invariant relation)
    {before after : PatternRewriter OpInfo} (initial : invariant before.ctx)
    (run : pattern.worklistStep before = some after) :
    invariant after.ctx ∧ relation before.ctx after.ctx := by
  unfold worklistStep at run
  dsimp only at run
  split at run
  next opIn =>
    split at run
    next dead =>
      cases run
      exact steps.deadStep { before with worklist := before.worklist.pop.2 } _ opIn dead.1 dead.2 initial
    next notDead =>
      exact steps.patternStep { before with worklist := before.worklist.pop.2 } _ opIn _ initial run
  next outside => cases run

/-- Every successful execution of the unbounded driver has a finite proof by
fixpoint induction. No termination, worklist ordering, or fairness assumption is needed. -/
theorem RewritePattern.runWorklist_preserves
    (pattern : RewritePattern OpInfo) (invariant : WfIRContext OpInfo → Prop)
    (relation : WfIRContext OpInfo → WfIRContext OpInfo → Prop)
    (steps : ContextStepPreserves pattern invariant relation)
    (refl : ∀ ctx, invariant ctx → relation ctx ctx)
    (trans : ∀ a b c, relation a b → relation b c → relation a c) :
    ∀ (before : PatternRewriter OpInfo), invariant before.ctx → ∀ (after : PatternRewriter OpInfo),
      pattern.runWorklist before = some after →
      invariant after.ctx ∧ relation before.ctx after.ctx := by
  apply runWorklist.fixpoint_induct pattern
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
      have nextFacts := pattern.worklistStep_preserves invariant relation steps initial stepped
      have finalFacts := induction next nextFacts.1 after returned
      exact ⟨finalFacts.1, trans _ _ _ nextFacts.2 finalFacts.2⟩

/-- Worklist seeding cannot change the IR or its current action flag. -/
theorem PatternRewriter.seedNestedReversePostOrder_context
    (before : PatternRewriter OpInfo) (root : OperationPtr) :
    (before.seedNestedReversePostOrder root).ctx = before.ctx ∧
      (before.seedNestedReversePostOrder root).hasDoneAction = before.hasDoneAction := by
  exact ⟨rfl, rfl⟩

end Veir
