module

meta import Lean
import all Veir.Passes.RISCVCombines.Validity.Basic
import all Veir.Passes.RISCVCombines.Validity.Bitwise
import all Veir.Passes.RISCVCombines.Validity.SignExtending
import all Veir.Passes.RISCVCombines.Validity.LowWord
import all Veir.Passes.RISCVCombines.Validity.Store
import all Veir.Passes.RISCVCombines.Validity.Load

/-!
# CTree validity of the RISC-V combines

Collects the CTree validity proofs (`Puddle.CTree.Pattern.Valid`) of the `riscv-combine`
patterns, grouped by topic in `Veir.Passes.RISCVCombines.Validity.*`.

The proofs follow the CTree strategy of `math-fehr/puddle-ctree-wip`: `simpPuddleValid`
discharges the structural obligations and erases the handle bookkeeping,
`simp [ctree_semantics]` unfolds the operation semantics, and each remaining register equality is
closed by the combine's local correctness lemma in `Veir.Passes.RISCVCombines.Proofs`, whose
statement must therefore match the pattern exactly.
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
  logInfo m!"{proofs.size} validity proofs, none depending on `sorryAx`"
