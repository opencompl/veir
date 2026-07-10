# Handoff: Remove `axiom Array.usize_size` by threading array-size bounds

## Task

Remove `axiom Array.usize_size (ar : Array α) : ar.usize.toUInt64.toNat = ar.size`
(in `Veir/Prelude.lean:60`) and replace its uses with honest, provable reasoning
based on explicit bounds on array sizes. No code has been edited yet — this file
records the completed analysis and the agreed plan.

## Why it's an axiom

Core Lean defines `Array.usize (xs) : USize := xs.size.toUSize`
(toolchain v4.31.0, `src/lean/Init/Data/Array/Basic.lean:166`), which **truncates**
mod `USize.size` (platform-dependent: `2^32` or `2^64`). So the equality is not
provable in general; only these are:

- Unconditional: `ar.usize.toUInt64.toNat ≤ ar.size` (mod ≤ id).
- Conditional: equality holds if `ar.size < USize.size` (platform-dependent, ugly),
  or — if we switch code from `.usize.toUInt64` to `.size.toUInt64` — if
  `ar.size < UInt64.size` (= `2^64`, platform-independent). **We chose the latter.**

Note `ExArray` already solves this correctly: it bundles
`data_fits_in_memory : data.size < Int64.maxNatValue` in the structure and proves
`ExArray.usize_size_toNat` (`ExArray/lean/ExArray/Basic.lean:112`) from it. Its
`usize` is defined as `size.toUInt64` directly — precedent for the approach.

## Scope (only 2 files use the axiom)

- `Veir/Prelude.lean:60-69` — the axiom + 2 derived theorems:
  - `Array.size_le_uint64_size (ar) : ar.size < UInt64.size` — **unprovable without
    axiom, must be deleted**; used at Rewriter/Basic.lean:1000, 1140, 1488 (only to
    show `(index+1).toNat = index.toNat + 1`, which is derivable from the loop's
    exit-condition instead).
  - `Array.size_le_toNat (h : ar.usize.toUInt64 ≤ x) : ar.size ≤ x.toNat` — used
    once at Rewriter/Basic.lean:814; must become conditional on a size bound.
- `Veir/Rewriter/Basic.lean` — all remaining uses (lines ~748-771, 814, 865/871,
  987-1005, 1134-1148, 1329-1340, 1481-1488, 1583-1601).

All the many `ctx.buf.usize` hits in `Veir/IR/Buffed/*.lean` are
`ExArray.usize`/`IRBufContext.usize` — already axiom-free. Do not touch.

## Key structural facts discovered

1. **The 5 loop functions** iterate `index : UInt64` against `if h : index ≥ arr.usize.toUInt64`:
   - `Rewriter.initBlockArgumentsLoopSim` (Basic.lean:744) — NOTE: its
     `termination_by` is `types.usize.toNat - index.toNat` (others use `types.size - …`).
   - `Rewriter.initOpRegionsSim` (:978)
   - `Rewriter.initOpResultsSim` (:1128)
   - `Rewriter.initOpOperandsSim` (:1322)
   - `initBlockOperands…Sim` (~:1481, same shape)

   Their *internal* obligations (indexing `arr[index.toNat]`, `hcap`-style bounds
   passed to `push*At`, termination) only need the **inequality**
   `index < arr.size.toUInt64 → index.toNat < arr.size`, which after switching to
   `.size.toUInt64` follows from `toNat_ofNat` normalization + cutsat
   (`size % 2^64 ≤ size`) with **no hypothesis needed**.

2. **Completeness needs the equality.**
   `Rewriter.initBlockArguments_inBounds'` (Basic.lean:793-814) states
   `argPtr.index < types.size ∨ …` — i.e. the loop processed *all* elements. That
   requires `size.toUInt64.toNat = size`, hence a bound `types.size < UInt64.size`
   must be **added as a hypothesis parameter to the loop function** (so it sits in
   context during `fun_induction`). Its proof uses `→ Array.size_le_toNat` (line 814),
   which becomes the conditional version.

3. **`createOpSim`** (Basic.lean:1565-1650) already has a **runtime guard**
   `if hsz : resultTypes.size ≤ Buffed.countCard ∧ … (all four arrays)` where
   `Buffed.countCard = UInt32.size = 2^32` (Veir/IR/Buffed/Layout.lean:19).
   `size ≤ 2^32 < 2^64` discharges every needed bound platform-independently
   (this is exactly why we use `.size.toUInt64` instead of keeping `.usize`,
   which would need `size < USize.size` — not derivable from the guard on a
   32-bit platform where `USize.size = 2^32`).
   It passes `resultTypes.usize.toUInt64` etc. to `allocEmpty` (:1583) — switch to
   `resultTypes.size.toUInt64`; obligations at :1584-1585 (`… ≤ countCard`) and the
   `hcapX` facts at :1594-1601 then follow from the guard.

4. **`createBlockSim`** (Basic.lean:852-879) already passes `argTypes.size.toUInt64`
   to `BlockPtr.allocEmpty` (:858) but has **no guard/hypothesis** — the proofs at
   :865/:871 (`get! … = .empty argTypes.size`, feeding `hcap` of
   `initBlockArguments`) use the axiom for `size.toUInt64.toNat = size`.
   **Plan: add a runtime guard** `if hsz : argTypes.size ≤ Buffed.countCard then … else none`
   mirroring `createOpSim` (return type is already `Option`). The inner
   `allocEmpty` check (`Veir/IR/Buffed/Basic.lean:2784`) checks the *truncated*
   value so it does not subsume this.
   - Downstream `split at heq` proofs gain one trivial case:
     `createBlock_inBounds_mono` (:881), `createBlock_fieldsInBounds_mono` (:899),
     possibly more below and in `Veir/Rewriter/WfRewriter/{Basic,GetSet,InBounds}.lean`.
   - Callers all tolerate `none` already: `WfRewriter.createBlock`
     (WfRewriter/Basic.lean:107-112) wraps in `rlet`, parser calls with `#[]`
     (Parser/MlirParser.lean:216, 237) and matches on the result,
     `PatternRewriter.createBlock` (PatternRewriter/Basic.lean:218). Verify the
     parser doesn't rely on an `isSome` theorem for `createBlock ctx #[] …`.

5. **`buffed` macro** (`Veir/IR/Buffed/Meta.lean:1725`): `buffed def fooSim …`
   generates `fooImpl`, `fooSpec`, base wrapper `foo`, and a `foo_def` lemma.
   Hypothesis args (with `:= by grind` defaults) ride along into the wrapper, so
   adding one more hypothesis param follows the existing pattern. Downstream
   theorems name the wrapper's hypothesis args positionally
   (`initOpResults opPtr ctx resultTypes index h₁ h₂ h₃`) — each gains an `h₄`.

## The plan

### `Veir/Prelude.lean`

Delete the axiom and `Array.size_le_uint64_size`. Add (proof style mirrors
`ExArray.usize_size_toNat`, using `Nat.toUInt64_eq`, `UInt64.toNat_ofNat'`,
`Nat.mod_eq_of_lt`):

```lean
theorem Array.size_toUInt64_toNat (ar : Array α) (h : ar.size < UInt64.size) :
    ar.size.toUInt64.toNat = ar.size

theorem Array.size_le_toNat {ar : Array α} {x : UInt64}
    (hsz : ar.size < UInt64.size) (h : ar.size.toUInt64 ≤ x) : ar.size ≤ x.toNat
```

(An unconditional `ar.size.toUInt64.toNat ≤ ar.size` may be handy but grind's
`toNat_ofNat` normalization + cutsat probably makes it unnecessary.)

### `Veir/Rewriter/Basic.lean`

1. Replace every `«arr».usize.toUInt64` with `«arr».size.toUInt64` (loop guards at
   :748, :987, :1134, :1329, :1481; allocEmpty args at :1583).
2. `initBlockArgumentsLoopSim`: change `termination_by` to
   `types.size - index.toNat`; rewrite its `decreasing_by` (currently invokes the
   axiom at :769) as `grind only [UInt64.le_iff_toNat_le, UInt64.toNat_add,
   UInt64.toNat_mod_size]`-style, same as the other loops.
3. Add `(hsz : «arr».size < UInt64.size := by grind)` as final hypothesis param to
   the 5 loop `Sim` defs; pass it through the recursive call (same array — trivial).
   Strictly it's only *needed* where completeness theorems exist
   (initBlockArguments), but adding it uniformly keeps `grind [Array.size_toUInt64_toNat]`
   working at every former `grind [Array.usize_size, …]` site with minimal thought.
   Alternative if churn on downstream theorem signatures gets bad: skip `hsz` on
   loops whose obligations turn out to go through with the inequality alone
   (initOpResults/initOpOperands/initOpRegions/initBlockOperands may all qualify),
   and only add it to `initBlockArgumentsLoopSim`.
4. Swap proof hints: `grind [Array.usize_size, …]` → `grind [Array.size_toUInt64_toNat, …]`
   (conditional rewrite; the `hsz`/guard fact must be in context).
   `grind [Array.size_le_uint64_size]` at :1000/:1140/:1488 → derive
   `(index+1).toNat = index.toNat + 1` from `index.toNat < size.toUInt64.toNat < UInt64.size` instead.
   `grind [=_ Array.usize_size]` at :865/:871 → `grind [Array.size_toUInt64_toNat]`
   with the new createBlock guard in context.
5. `createOpSim`: obligations at :1584-1585 and `hcapX` at :1594-1601 re-proved from
   the existing guard (`hsz`) + `Array.size_toUInt64_toNat`; the `initOp*` calls gain
   `(by grind)` for their new `hsz` params.
6. `createBlockSim`: wrap body in `if hsz : argTypes.size ≤ Buffed.countCard then … else none`
   with a comment mirroring createOpSim's (:1577-1579). Fix the follow-on
   `split at heq` proofs (one extra trivial case each).
7. Update downstream theorem signatures that enumerate the loops' hypothesis args
   (`{… h₁ h₂ h₃}` → add `h₄`): the ~6 theorems after each loop def, e.g.
   :780, :793, :831, :843 (initBlockArguments), :1007+, :1150-1190+ (initOpResults),
   :1342-1379+ (initOpOperands), etc. All mechanical; `fun_induction …Sim <;> grind`
   proofs should survive.

### Build / iterate

- `lake build Veir.Rewriter.Basic` (project root `/Users/ineol/Code/veir-prs`,
  toolchain `leanprover/lean4:v4.31.0`). Expect slow elaboration —
  `createOpSim` already needs `set_option maxHeartbeats 4000000`.
- Then full `lake build` to catch WfRewriter/PatternRewriter/Parser fallout
  (files known to reference these defs: `Veir/Rewriter/WfRewriter/{Basic,GetSet,InBounds}.lean`,
  `Veir/PatternRewriter/Basic.lean`, `Veir/Parser/MlirParser.lean`,
  `Veir/Passes/InstCombine.lean`, `Veir/Passes/InstructionSelection/RISCV64.lean`,
  `Veir/Benchmarks.lean` (uses `sorry` for createOp proofs already),
  `Veir/Experiments/NoProofApi.lean`).
- Final check: `grep -rn "Array.usize_size\|axiom" Veir/` — no axiom left, and
  ideally `#print axioms` on a top-level def only shows the standard ones.

## Gotchas

- `grind` hint syntaxes in use: `[=_ Foo]` (right-to-left rewrite), `[→ Foo]`
  (forward implication), `[= Foo]`. Preserve the direction markers when swapping lemmas.
- The `rlet` macro (Prelude.lean:71+) desugars to `match _ : e with` — proofs
  reference the equation via `rename_i heq`; inserting an `if` above changes which
  hypothesis `rename_i` grabs. Watch `createBlockSim`'s `(by rename_i heq; …)` args.
- `buffed (inline := false)` on `createOpSim` — keep flags as-is.
- Do not touch the `≤ Buffed.countCard` guard in createOpSim (non-strict is fine
  for the `2^64` bound; strictness was only needed for the abandoned USize approach).
- `initOpOperandsSim` returns `Sim.IRContext` directly (not `Option`) and has
  primed mono lemmas (`initOpOperands_inBounds_mono'` :1362) — signatures there too.
- The repo has an unrelated dirty status (whole `veir-prs/` untracked from parent
  dir listing); work on branch `main`, no commits requested yet.
