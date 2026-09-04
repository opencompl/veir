module

public import Veir.Pass
public import Veir.PatternRewriter.Basic

import all Veir.Passes.InstCombine

namespace Veir

/-!
  # Apply patterns pass

  Applies a command-line-selected set of peephole rewrite patterns. Each pattern is
  exposed as a boolean pass option and is disabled by default, so a pipeline can
  request exactly the desired rewrites, for example:

  `apply-patterns{muli-two-to-addi addi-zero-to-x}`

  Currently, only the patterns from `Veir.Passes.InstCombine` are available.
-/

/-- The peephole patterns selectable through `ApplyPatternsPass`. -/
def applyPatterns : List (String × RewritePattern OpCode) := [
  ("muli-two-to-addi", mulITwoToAddi),
  ("muli-zero-to-cst", mulIZeroToCst),
  ("muli-one-to-x", mulIOneToX),
  ("addi-zero-to-x", addiZeroToX),
  ("subi-zero-to-x", subiZeroToX),
  ("subi-self-to-zero", subiSelfToZero),
  ("andi-self-to-x", andiSelfToX),
  ("andi-zero-to-zero", andiZeroToZero),
  ("ori-zero-to-x", oriZeroToX),
  ("ori-self-to-x", oriSelfToX),
  ("xori-zero-to-x", xoriZeroToX),
  ("xori-self-to-zero", xoriSelfToZero),
  ("not-not-to-x", notNotToX),
  ("de-morgan-and-to-or", deMorganAndToOr),
  ("de-morgan-or-to-and", deMorganOrToAnd)
]

def ApplyPatternsPass.impl (options : PassOptions) (ctx : WfIRContext OpCode)
    (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  let patterns := applyPatterns.foldl (init := #[]) fun selected (name, pattern) =>
    if (options.get? name).getD false then selected.push pattern else selected
  let pattern := RewritePattern.GreedyRewritePattern patterns
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying pattern rewrites"
  | some ctx => pure ctx

public def ApplyPatternsPass : Pass OpCode :=
  { name := "apply-patterns"
    description := "Apply a selected set of peephole rewrite patterns."
    options := .ofList (applyPatterns.map fun (name, _) =>
      (name, { description := s!"Enable the '{name}' rewrite pattern." }))
    run := ApplyPatternsPass.impl }

end Veir
