import Lean
import Veir.Interpreter
import Veir.Passes.RISCVCombines.MIRCombinesVeir

/-!
# Pre-generated match equations for the MIR (`llvm` → `llvm`) combines

Same problem, and same fix, as `CommonMatchEqns.lean` (see its comment): `split`/`grind`
realize a matcher's `match_n.eq_k` / `match_n.congr_eq_k` (and `_sparseCasesOn_*`) lemmas
lazily, in whichever module first needs them, so two sibling proof modules that case on the
same matcher each bake a private copy into their olean and then clash when co-imported
(`environment already contains 'Veir.RISCV.sub_minus_one.match_3.congr_eq_1._sparseCasesOn_2'`).

The MIR combines and their matchers live in `Veir.Passes.RISCVCombines.MIRCombinesVeir`, which
`CommonMatchEqns` does *not* anchor. Pre-generating them here once — in a module every MIR-combine
proof imports — gives them a single shared copy. The anchor pins that module (via
`same_val_zero_1_local`).
-/

open Lean Meta in
run_meta do
  let env ← getEnv
  for anchor in [``Veir.RISCV.same_val_zero_1_local] do
    let some modIdx := env.getModuleIdxFor? anchor
      | throwError "expected `{anchor}` to be imported"
    for n in env.header.moduleData[modIdx.toNat]!.constNames do
      if isMatcherCore env n then
        discard <| Match.getEquationsFor n
        discard <| Match.genMatchCongrEqns n
