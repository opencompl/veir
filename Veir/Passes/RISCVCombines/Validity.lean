module

import Veir.Passes.RISCVCombines.Validity.Basic
import Veir.Passes.RISCVCombines.Validity.Bitwise
import Veir.Passes.RISCVCombines.Validity.SignExtending
import Veir.Passes.RISCVCombines.Validity.LowWord
import Veir.Passes.RISCVCombines.Validity.Store
import Veir.Passes.RISCVCombines.Validity.Load

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
