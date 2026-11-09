module
public import Veir.PatternRewriter.Puddle.Internal.FilteredDriverLemmas
import all Veir.PatternRewriter.Puddle.Internal.ScopedWorklist
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

theorem RewritePattern.ContextStepPreserves.toFiltered
    {pattern : RewritePattern OpInfo} {invariant relation}
    (h : ContextStepPreserves pattern invariant relation) :
    ScopedContextStepPreserves pattern (fun _ _ => True) invariant relation := by
  constructor
  · intro before op inside after inv _ _ _ run
    obtain ⟨next, rel⟩ := h.patternStep before op inside after inv run
    exact ⟨⟨next, fun _ _ => trivial⟩, rel⟩
  · intro before op inside dead alloc inv _ _ _
    obtain ⟨next, rel⟩ := h.deadStep before op inside dead alloc inv
    exact ⟨⟨next, fun _ _ => trivial⟩, rel⟩

/-- Popping only changes the worklist; either successful dispatch branch satisfies
its corresponding concrete pattern or dead-operation obligation. -/
theorem RewritePattern.worklistStep_preserves
    (pattern : RewritePattern OpInfo) (invariant : WfIRContext OpInfo → Prop)
    (relation : WfIRContext OpInfo → WfIRContext OpInfo → Prop)
    (steps : ContextStepPreserves pattern invariant relation)
    (refl : ∀ ctx, invariant ctx → relation ctx ctx)
    {before after : PatternRewriter OpInfo} (initial : invariant before.ctx)
    (run : pattern.worklistStep before = some after) :
    invariant after.ctx ∧ relation before.ctx after.ctx := by
  have h := pattern.worklistStep_preserves_scope _ _ _ steps.toFiltered refl initial (fun _ _ => trivial) run
  exact ⟨h.1.1, h.2⟩

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
  intro before initial after run
  have h := pattern.runWorklist_preserves_scope _ _ _ steps.toFiltered refl trans before
    ⟨initial, fun _ _ => trivial⟩ after run
  exact ⟨h.1.1, h.2⟩

end Veir
