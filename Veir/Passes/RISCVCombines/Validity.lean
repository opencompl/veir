module

meta import Lean
import all Veir.Passes.RISCVCombines.Proofs
public import Veir.Passes.RISCVCombines.Validity.Pass

/-!
# CTree validity of the RISC-V combines

Checks the CTree validity proofs (`Puddle.CTree.Pattern.Valid`) of the `riscv-combine`
patterns, which live in `Veir.Passes.RISCVCombines.Proofs`.
-/

/- Fail the build if a validity proof of a RISC-V combine (a theorem `*_valid` in
`Veir.RISCV.CTreeProofs`) depends on `sorryAx`. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let proofs := env.constants.fold (init := #[]) fun acc name info =>
    -- The proofs are private to their modules, so their names carry a `_private` prefix.
    let userName := privateToUserName name
    if (`Veir.RISCV.CTreeProofs).isPrefixOf userName && userName.getString!.endsWith "_valid" &&
        info matches .thmInfo _ then
      acc.push name
    else
      acc
  if proofs.isEmpty then
    throwError "no validity proofs found in `Veir.RISCV.CTreeProofs`"
  let mut unproven := #[]
  for name in proofs do
    if (← collectAxioms name).contains ``sorryAx then
      unproven := unproven.push (privateToUserName name)
  unless unproven.isEmpty do
    throwError "validity proofs depending on `sorryAx`: {unproven.qsort Name.lt}"
