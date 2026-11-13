module

public import Veir.PatternRewriter.Basic
public import Veir.PatternRewriter.Puddle.Execution

/-!
# Per-operation choice of rewrite rules

A pass that picks its rewrites from a registry, by the operation it is at, is a rewrite pattern
that chooses, from the context and the operation, the rules to try in order. `ofRules` gives it
that shape; `CTreePointwiseSoundness` proves that choosing valid rules is pointwise valid.

The chosen rules are data, not a pattern: a choice returning a pattern would be compiled as one
function taking the context and the rewriter, which keeps the context shared while the rules run
and makes every rewrite copy it.
-/

public section
namespace Veir
namespace RewritePattern

/-- Try, in order, the rules chosen from the context and the operation. -/
@[expose]
def ofRules (choose : WfIRContext OpCode → OperationPtr → List (Puddle.Pattern OpCode)) :
    RewritePattern OpCode :=
  fun rewriter op opIn =>
    let rules := choose rewriter.ctx op
    GreedyRewritePattern (rules.toArray.map fun rule => rule.compile.run) rewriter op opIn

end RewritePattern
end Veir
end
