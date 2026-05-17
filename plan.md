# VEIR ↔ LLZK port: master roadmap

Living document. Updated after every port, every verified pass, every infra
investigation. Cross-references the `harness/` directory for protocols and
the per-component working state.

The original Felt-port-specific plan that lived here through 2026-05-02 is
preserved in `LLZK_PORT_RETRO.md`. The reusable lessons from it are folded
into `harness/porting-notes.md`.

## Mission

1. **Port LLZK dialects** into VEIR so that LLZK MLIR can round-trip
   through `veir-opt` as typed VEIR IR (not `UnregisteredAttr` blobs).
2. **Produce verified examples** of LLZK passes in VEIR, leveraging
   VEIR's `WellFormed`-preservation and data-refinement scaffolding.
3. **Maintain a coverage review** (`harness/coverage.md`) so caveats and
   limitations are surfaced for any downstream consumer of this fork.

The harness is itself a deliverable: every doc under `harness/` is meant
to be maintained as work progresses, not written once.

## Status snapshot

| Component | State | Pointer |
|---|---|---|
| Felt dialect (18 ops, `!felt.type`) | ✅ ported (round-trip, generic format) | `LLZK_PORT_RETRO.md`, `Test/LLZK/Felt/identity.mlir` |
| String dialect (`string.new`, `!string.type`) | ✅ ported (round-trip, generic format) | `Test/LLZK/String/identity.mlir` |
| Include dialect (`include.from`) | ✅ ported (typed, with typed-path negative test) | `Test/LLZK/Include/{identity,invalid}.mlir` |
| RAM dialect (`ram.load`, `ram.store`) | ✅ ported (typed) | `Test/LLZK/RAM/{identity,invalid}.mlir` |
| Cast dialect (`cast.tofelt`, `cast.toindex`) | ✅ ported (typed) | `Test/LLZK/Cast/{identity,invalid}.mlir` |
| Bool dialect (and/or/xor/not/assert/cmp) | ✅ ported (cmp via IntegerAttr enum workaround) | `Test/LLZK/Bool/{identity,invalid,cmp,cmp_invalid}.mlir` |
| Constrain dialect (eq only) | ⚠️ partial (constrain.in deferred) | `Test/LLZK/Constrain/{identity,invalid}.mlir` |
| Global dialect (def, read, write) | ✅ ported (typed; uses FlatSymbolRefAttr) | `Test/LLZK/Global/{identity,invalid}.mlir` |
| Structured `#felt<const N>` attribute | ✅ landed 2026-05-17 — first per-dialect structured attribute; un-XFAILed Felt differential | `Veir/IR/Attribute.lean` (FeltConstAttr) + `Veir/Parser/AttrParser.lean` |
| Phase F design note (F.1) | ✅ landed 2026-05-17 — revealed regions are structurally ready in VEIR's verified IR; revised estimate down to 2-4 weeks | `harness/regions-design.md` |
| First verified LLZK pass | ✅ Phase E.1 — `felt-combine` proves `felt.add x (felt.const 0) → x` | `Veir/Passes/Felt/{Combine,Proofs}.lean` |
| Second verified LLZK pass (constant-fold) | ✅ Phase E.2 — `felt-combine` proves `felt.add (felt.const c1) (felt.const c2) → felt.const (c1+c2)` | `Veir/Passes/Felt/{Combine,Proofs}.lean` |
| Third verified LLZK pass (self-subtraction) | ✅ Phase E.3 — `felt-combine` proves `felt.sub x x → felt.const 0` | `Veir/Passes/Felt/{Combine,Proofs}.lean` |
| Fourth verified LLZK pass (assoc-const-fold) | ✅ Phase E.4 — `felt-combine` proves `felt.add (felt.add x c1) c2 → felt.add x (c1+c2)` | `Veir/Passes/Felt/{Combine,Proofs}.lean` |
| `index` type | ✅ added inline as infra during A.4 | `Veir/IR/Attribute.lean` |
| Per-dialect attribute parser | ❌ none in VEIR (workaround: `IntegerAttr`) | `harness/coverage.md` §Attributes |
| Symbol references (`@name`) | ❌ no `SymbolRefAttr` case in `Attribute` | `harness/coverage.md` §Symbols |
| `AffineMapAttr` | ❌ unrepresented | `harness/coverage.md` §AffineMap |
| Variadic-of-variadic operands | ❌ unrepresented | `harness/coverage.md` §Ops |
| Regions (multi-block, terminators) | ❌ no `Region` in verified IR | `harness/coverage.md` §Structural |
| Dominance | ⚠️ axiomatized only (`Veir/Dominance.lean`) | `harness/coverage.md` §Verification |
| WellFormed preservation across rewrites | ✅ proven | `Veir/Rewriter/WellFormed/` |
| Data refinement framework | ⚠️ exists, only RISCV instruction-selection uses it | `Veir/Data/Refinement.lean` |
| `interpret ; pass = interpret` | ❌ no framework | `harness/verification-plan.md` |
| LLZK pass verification examples | ❌ none yet | `harness/verification-plan.md` |

## Phased roadmap

Phases are sized by **risk and infrastructure**, not by dialect count.
Each phase has a build gate (`lake build` clean, full lit suite green) and
ends with `harness/coverage.md` updated.

### Phase A — Tier 1 dialect batch (≈2–3 weeks)

Goal: prove the dialect-port recipe (`harness/dialect-port-checklist.md`)
generalizes. No new VEIR infrastructure beyond what Felt established.

In dependency order:

- [x] **A.1 Include** — symbol *producer*; uses upstream `FlatSymbolRefAttr` (PR #533). Includes a typed-path negative test (defense against Gotcha 2, made worse by upstream PR #569).
- [x] **A.2 String** — single op, single param-less type.
- [x] **A.3 Cast** — Felt + index types (both in place).
- [x] **A.4 RAM** — Felt-dependent, plus `index` type infra.
- [x] **A.5 Bool (basic)** — 5 of 6 ops ported; `bool.cmp` deferred to Phase D.4.
- [x] **A.6 Constrain (eq only)** — `constrain.eq` ported; `constrain.in` deferred to Phase D.3 (Array types).

*Build/lit counts at each phase: see git log / `baseline.txt` §tier-1-complete.*

Acceptance: each dialect has a `Test/<Dialect>/identity.mlir`, full lit
suite green, build clean, `harness/coverage.md` row updated.

### Phase B — Symbol-table architecture spike  **[RETIRED 2026-05-15]**

Originally a 1-week design phase for symbol-table semantics. Assessed
and retired after Tier 1 + the upstream merge revealed:

1. **Flat `@name` parsing landed upstream** (PR #533, `FlatSymbolRefAttr`).
   Include consumes it directly; no spike needed.
2. **Tier 2 (Global, POD, Array) needs nothing beyond flat refs** — the
   one symbol-using site, `!array.type<5,@N x !felt.type>`, takes a single
   flat ref inside a parametric type.
3. **Tier 3 (Function, Polymorphic, Struct) does need nested `@A::@B`
   plus SymbolTable semantics**, but those are *gated on Phase F (regions)*.
   The two design decisions should be made together, not in isolation.

The original framing is preserved in `harness/symbol-table-spike.md`
(marked deferred) and the remaining open questions are folded into
Phase F's design scope.

### Phase C — Attribute & operand infrastructure (≈2 weeks)

Lands the per-dialect attribute and operand machinery needed by
Tier 2. (Originally included a `SymbolRefAttr` parser; that's now
delivered by upstream.)

- [x] **C.0** Per-dialect structured-attribute parser pattern (done 2026-05-17 with `FeltConstAttr`; recipe in `harness/porting-notes.md`). Establishes the template for any future structured attribute.
- [ ] **C.1** `AffineMapAttr` in `Attribute.lean` + parser (black-box: store the textual form, no semantic interpretation yet)
- [ ] **C.2** Variadic-of-variadic operand handling in `OpCode`/`Verifier`
- [x] **C.3** Enum-attribute story finalized: `IntegerAttr` workaround stays the recommended pattern (used for `bool.cmp` predicate); a per-dialect enum parser is only worth adding if a verified pass needs symbolic case matching. Pattern documented in `harness/porting-notes.md` 2026-05-15 enum-attr entry.

Acceptance: one consumer dialect for each piece of infra lands as a
follow-on commit on the same branch.

### Phase D — Tier 2 dialects (≈1–2 weeks)

- [x] **D.1 Global** — uses upstream `FlatSymbolRefAttr`. Done 2026-05-15. Validated that retiring Phase B was correct: no symbol-table machinery needed for round-trip.
- [ ] **D.2 POD** — uses C.2 + C.3
- [ ] **D.3 Array** (types + non-symbol ops) — uses C.2 + C.3
- [x] **D.4 Bool full** — `bool.cmp` ported via the IntegerAttr-as-enum workaround (Phase C.3 enum-parser deferred indefinitely; the workaround suffices). Done 2026-05-15.

### Phase E — Verification pilot 1: Felt local rewrite (≈2 weeks)

First verified LLZK-touching pass, deliberately scoped small.

- [x] **E.1** Pattern: `felt.add x (felt.const 0) → x`. Mirror
      `Veir/Passes/Combines/Combine.lean`. Done 2026-05-15.
- [x] **E.2** Proof: `Veir/Passes/Felt/Proofs.lean` proves `add x (const 0) = x`
      against `Veir/Data/Felt/` model. Done 2026-05-15.
- [x] **E.3** `Veir/Data/Felt/Basic.lean` ships: provisional `Felt := Int`
      abbrev; documented that the identity lifts to any `ZMod p` model.
      Done 2026-05-15.
- [x] **E.4** Lit test `Test/LLZK/Felt/passes/right_identity.mlir`
      exercises the pass and asserts only one of two `felt.add` ops
      survives. Done 2026-05-15.

Acceptance: build green (267/267), lit green (322/322, +1 for the
new pass test), zero `sorry` in new files (proof side; rewriter
precondition `sorry`s in `Combine.lean` are consistent with current
VEIR practice). Proof is imported from `Combine.lean` so default
`lake build` checks it — defends against silent bitrot.

### Phase F — Region infrastructure + symbol-table design (≈3–6 weeks)

Major architectural addition to VEIR's verified IR. Gates Function,
Polymorphic, Struct, Array (with symbol-bearing dims used inside
regions), and almost all LLZK transform passes.

Includes the design questions that were originally Phase B (now
retired) because they're tightly coupled to region semantics:

- [x] **F.1** Design note `harness/regions-design.md` — landed 2026-05-17.
      Big finding: structural regions are already in VEIR's verified IR
      (Operation.regions field, Region/Block types, FieldsInBounds +
      WellFormed proofs); only semantic invariants and consumer dialects
      remain. Revised estimate down from 3-6 weeks to 2-4 weeks. Phased
      implementation specified as F.2-F.5 below.
- [ ] **F.2** `Veir/IR/` extensions — `BlockArgument` as `ValuePtr`
      variant + `valueDefUseChains` extension + block-level rewriter
      primitives (`createBlock`, `insertBlock`, `eraseBlock`, `moveBlock`,
      `moveRegion`) with WellFormed-preservation proofs.
- [ ] **F.3** Verify-time semantic invariants — terminator presence
      + `IsolatedFromAbove` SSA closure. Per-OpCode `isTerminator`
      classification.
- [ ] **F.4** Symbol-table machinery (unverified per the recommended
      Hybrid path) — `SymbolRefAttr` for nested paths,
      `Veir/IR/SymbolTable.lean` walker `resolveSymbol`.
- [ ] **F.5** Prototype `Function.def` port as the first concrete
      consumer; lift the 5 XFAIL differential tests (Bool, Cast,
      Constrain, RAM, Global write) by wrapping their ops in
      `function.def`.

See `harness/regions-design.md` for full specification.

### Phase G — Tier 3 dialects (gated by F)

- [ ] **G.1 Function** — `function.def`, `function.return`, `function.call`
- [ ] **G.2 Polymorphic** — `poly.template`, type variables, `LLZKSymbolTable` trait
- [ ] **G.3 Struct** — `struct.def`, parametric `!struct.type<@A<[...]>>`, member symbols, nested functions

### Phase H — Verification pilot 2 onward

Pilots in increasing difficulty (sourced from LLZK transforms by
verifiability score; see `harness/verification-plan.md`):

- [ ] **H.1 EnforceNoOverwrite checker** (LLZK trivial-1, but needs G.3
      to run on real Struct ops — Felt-only variant could land earlier)
- [ ] **H.2 UnusedDeclarationElimination** (DCE, needs G.1 + G.3)
- [ ] **H.3 RedundantOperationElimination** (CSE-style, needs dominance
      properly implemented — `Veir/Dominance.lean` is axiomatized today)

### Out-of-band: SMT dialect

Orthogonal to the rest. Port only when there's a concrete use case;
treat as a separate project.

## Living-document protocol

Three rules:

1. **Coverage updates are non-optional.** Any commit that adds support
   for an LLZK feature, or that discovers a new gap, updates
   `harness/coverage.md` in the same commit.
2. **Phase boundaries are commit boundaries.** Each phase ends with a
   green build, a green test suite, a coverage update, and a
   checkpointing tag per `harness/checkpoint-protocol.md`.
3. **Porting notes accumulate.** Anything surprising encountered during
   a port goes into `harness/porting-notes.md` in the same commit, so
   the next porter benefits. Don't wait for a retro.

## Cross-references

| Topic | Doc |
|---|---|
| Per-dialect work | `harness/dialect-port-checklist.md` |
| "Is this port/pass done?" | `harness/evaluation-criteria.md` |
| Commit/branch/tag conventions | `harness/checkpoint-protocol.md` |
| Durable porting gotchas (the two from Felt + new ones) | `harness/porting-notes.md` |
| Verification pilot designs | `harness/verification-plan.md` |
| LLZK feature ↔ VEIR support | `harness/coverage.md` |
| Felt port history | `LLZK_PORT_RETRO.md` |

## Iteration commands (unchanged from Felt)

```bash
lake build                       # 267/267 as of 2026-05-17
lake test                        # UnitTest target — 110 jobs, clean
uv run lit Test/ -v              # 327 total
                                 #   without LLZK_OPT: 319 PASS + 8 UNSUPPORTED
                                 #   with    LLZK_OPT: 322 PASS + 5 XFAIL + 0 FAIL
uv run lit Test/LLZK/<Dialect>/identity.mlir -v
export LLZK_OPT=<path>           # activates the 5 XFAIL'd differentials + 4 PASS diffs
bash scripts/check-llzk-quality-gates.sh   # static quality gates (sorry/axiom, coverage, tags)
```
