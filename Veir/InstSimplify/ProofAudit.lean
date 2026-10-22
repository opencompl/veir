module

public import Veir.PatternRewriter.Puddle.Validity
public meta import Lean.Elab.Command

/-!
Checks the declaration kinds and terminal proposition of reported proof names.
This does not unfold `Pattern.Valid`, inspect proof bodies, or add declarations.
-/

public section

namespace Veir.InstSimplify.ProofAudit

open Lean Elab Command

private meta def forallConclusion : Expr → Expr
  | .forallE _ _ body _ => forallConclusion body
  | .mdata _ body => forallConclusion body
  | type => type

/-- Every listed identifier must name a theorem. At least one must conclude
`Veir.Puddle.Pattern.Valid` after its forall parameters are removed.

Example: `audit_pattern_proofs "IS2024" [Veir.InstSimplify.IS2024.valid]`.
Auxiliary theorems with other conclusions are allowed alongside that theorem. -/
syntax (name := auditPatternProofs) "audit_pattern_proofs " str " [" ident,* "]" : command

@[command_elab auditPatternProofs]
meta def elabAuditPatternProofs : CommandElab := fun stx => do
  let ruleId := stx[1].isStrLit?.getD "<rule>"
  let proofNames := stx[3].getSepArgs
  let mut hasPatternValid := false
  for proofName in proofNames do
    let name ← resolveGlobalConstNoOverload proofName
    let info ← getConstInfo name
    match info with
    | .thmInfo theoremInfo =>
      if (forallConclusion theoremInfo.type).getAppFn.isConstOf ``Veir.Puddle.Pattern.Valid then
        hasPatternValid := true
    | _ =>
      throwErrorAt proofName "{ruleId}: reported proof {name} is not a theorem declaration"
  unless hasPatternValid do
    throwErrorAt stx "{ruleId}: no reported theorem concludes with Veir.Puddle.Pattern.Valid after forall parameters"

end Veir.InstSimplify.ProofAudit
