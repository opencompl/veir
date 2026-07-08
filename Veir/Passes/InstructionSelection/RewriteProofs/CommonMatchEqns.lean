import Lean
import Veir.Passes.InstructionSelection.RISCV64

/-!
# Pre-generated match equations for the RISC-V lowering combinators

Tactics like `split` and `grind` realize the `match_n.eq_k` / `match_n.congr_eq_k`
lemmas of a matcher on demand, in whichever module first needs them. The matchers of
the lowering combinators live in `Veir.Passes.InstructionSelection.RISCV64`, so two
sibling proof modules that both case on the same matcher each bake a private copy of
these lemmas (and their `_sparseCasesOn_*` auxiliaries) into their own olean — and
importing both modules together then fails with
`environment already contains 'Veir.lowerUnaryWLocal.match_3.congr_eq_1._sparseCasesOn_2'`.

Generating the lemmas here once, in a module that every rewrite proof imports, gives
all of them a single shared copy.
-/

open Lean Meta in
run_meta do
  let env ← getEnv
  let some modIdx := env.getModuleIdxFor? ``Veir.lowerUnaryWLocal
    | throwError "expected `Veir.lowerUnaryWLocal` to be imported"
  for n in env.header.moduleData[modIdx.toNat]!.constNames do
    if isMatcherCore env n then
      discard <| Match.getEquationsFor n
      discard <| Match.genMatchCongrEqns n
