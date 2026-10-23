module

import QPFTypes.Meta.QPFExpr.AddDecl
import QPFTypes.Meta.QPFExpr.OfTypeExpr

/-!
# `QPFExpr.ofTypeDef` Unit Tests

A minimal smoke test of calling `QPFExpr.ofTypeDef` directly. The pipeline is
tested extensively, through the `@[qpf]` attribute, in `Test.Meta.QPFAttr`.
-/

namespace QPFTypes.Test.OfTypeExpr
open Lean Meta Elab QPFExpr

set_option QPFTypes.debug true

/--
Derive a QPF from the existing type definition `declName` via
`QPFExpr.ofTypeDef`, and add it to the environment via `QPFExpr.addDecls`.
-/
private meta def deriveQPF (declName : Name) : TermElabM Unit :=
  QPFExpr.ofTypeDef declName (·.addDecls declName · <| ·.map Expr.fvar)

def Proj (α : liveParam (Type u)) := α
run_elab deriveQPF ``Proj

#guard_msgs (drop info) in #synth QPF (@TypeFun.ofCurried 1 Proj)

def FailsLiveDomain (α : liveParam Type) := α → Nat

/--
error: While deriving a QPF from definition:
  FailsLiveDomain

the domain of a function type may not mention live variables:
  α
a function type is not functorial in its domain.
-/
#guard_msgs in
run_elab deriveQPF ``FailsLiveDomain

end QPFTypes.Test.OfTypeExpr
