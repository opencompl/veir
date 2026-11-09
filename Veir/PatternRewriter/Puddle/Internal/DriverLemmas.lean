module
public import Veir.PatternRewriter.Basic
public import Veir.PatternRewriter.Puddle.Internal.WorklistLemmas
import all Veir.PatternRewriter.Basic
namespace Veir
public section
variable {OpInfo : Type} [HasOpInfo OpInfo]

/-- The actual round contract follows from the mutation branches of the actual worklist
runner. Seeding and the final flag projection do not change the context. -/
theorem RewritePattern.RoundPreserves.of_contextSteps
    (pattern : RewritePattern OpInfo) (root : OperationPtr)
    (invariant : WfIRContext OpInfo → Prop)
    (relation : WfIRContext OpInfo → WfIRContext OpInfo → Prop)
    (steps : ContextStepPreserves pattern invariant relation)
    (refl : ∀ ctx, invariant ctx → relation ctx ctx)
    (trans : ∀ a b c, relation a b → relation b c → relation a c) :
    pattern.RoundPreserves root invariant relation :=
  RoundPreserves.of_scopedContextSteps pattern root _ _ (fun _ _ => True)
    (fun _ _ _ _ => trivial) steps.toFiltered refl trans

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
    invariant after ∧ relation before after :=
  pattern.applyToFunctions_preserves root _ _
    (fun f => RoundPreserves.of_contextSteps pattern f.val _ _ steps refl trans)
    refl trans initial maxRounds success

end
end Veir
