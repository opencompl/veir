# Felt-port parity assessment (2026-05-28)

Companion to `LLZK_PORT_RETRO.md`, `SESSION_RETRO_2026-05-17.md`, and
`REVIEW_2026-05-20.md`. Answers two scoping questions:

1. **How much more work is left before "LLZK's Felt dialect has been
   ported to Lean"?**
2. **What would it take to replace the C++ implementation with the
   Lean one?**

Driven by a structured comparison of `llzk-lib/include/llzk/Dialect/Felt/`
+ `llzk-lib/lib/Dialect/Felt/` against `Veir/Dialects/LLZK/Felt/`,
`Veir/IR/Attribute.lean`, `Veir/OpCode.lean`,
`Veir/Parser/AttrParser.lean`, `Veir/Verifier.lean`,
`Veir/Passes/Felt/`, `Veir/Data/Felt/`, `Test/LLZK/Felt/`.

## 1. TL;DR

**Q1**: "Ported" is a word with multiple bars. The minimum honest answer:

- **Round-trip parity**: ✅ already there (Phase D.4 + E.5 + post-merge
  refresh land it).
- **Verifier parity** (type unification, field-name verification,
  `NotFieldNative` context-gating): **~3 engineer-days**.
- **Folder parity** (11 of 18 ops still lack folders, all 4 existing
  folders skip modular reduction): **~5-7 engineer-days** once a Field
  registry exists.
- **Attribute parity** (`#felt.field<name, prime>` + module-level
  `llzk.fields` registry): **~2 engineer-days**.
- **Assembly-format parity** (LLZK's `%c = felt.add %a, %b`): **~3
  engineer-days** for the 18 ops; not strictly required if generic
  form is acceptable, but it blocks ingesting any real LLZK source
  file.
- **Trait dispatch parity** (`Pure`, `Commutative`, `ConstantLike`,
  `FeltBinaryOpInterface`): **only needed when downstream passes
  consume them**; nominally `~1 week` if/when a downstream port lands.

Total for **"Felt is ported"** in the sense of *Lean port behaves
indistinguishably from the C++ dialect on the test corpus*: **~12-15
engineer-days** of focused work.

**Q2**: A drop-in replacement of LLZK's C++ Felt with the Lean
implementation, such that downstream tools (R1CS, SMT, ZKLean, PCL
backends; C API; Python bindings) defer to Lean, is **30-60+
engineer-months**. Not realistic on any near-term horizon.

The realistic alternative is **Strategy A — verified-output oracle**:
keep `llzk-opt` as the production tool, use `veir-opt` as a continuous
certification harness. We already have 80% of it (the differential
suite, the 15 verified rewrites, the `ZMod p` model). Hardening to
"every Felt-affecting LLZK transform is mirrored by a Lean rewrite
with a paired theorem" is **2-4 engineer-months**.

The middle ground — **Strategy E, proof-certificate generator** —
adds `llzk-opt --verify-rewrites`: Lean emits per-rewrite certificates
that an LLZK-side checker validates. 6-10 engineer-months, leaves the
C++ dialect in place, makes it certifiably equivalent to a Lean spec.

## 2. Q1 details — what's left for Felt parity

### 2.1 Done

- 18/18 opcodes enumerated in `Veir/OpCode.lean:230-249` matching
  LLZK's `Ops.td:88-246`.
- `FeltType { fieldName : Option ByteArray }` and `FeltConstAttr
  { value : Int, fieldType : FeltType }` in
  `Veir/IR/Attribute.lean:167,194`; parser at
  `Veir/Parser/AttrParser.lean:386,411`.
- Generic-MLIR round-trip green across `Test/LLZK/Felt/identity.mlir`,
  `Test/LLZK/Felt/differential/arith.mlir`, and now under
  `VEIR_ROUNDTRIP` (double round-trip) as of 2026-05-20.
- 15 verified peephole rewrites in `Veir/Passes/Felt/Combine.lean:46-306`
  with paired soundness theorems in `Veir/Passes/Felt/Proofs.lean`,
  axiom footprint `[propext, Quot.sound]` only.
- Pipeline composition validated by
  `Test/LLZK/Felt/pipelines/{combine_then_dce,telescoping_then_dce}.mlir`.

### 2.2 The honest list of gaps

The detail behind each row lives in `harness/coverage.md` and (now)
in this doc. Severity: **critical** = unsound or wrong; **major** =
missing semantic feature; **minor** = cosmetic/textual.

| # | Gap | Severity | Effort | File anchor |
|---|---|---|---|---|
| 1 | Constant-folds don't apply modular reduction (sound over `ZMod p` since the IR represents the equivalence class, but VEIR emits a different *representative* than LLZK — every named-field wrap-around test in `llzk-lib/test/Dialect/Felt/felt_const_fold.llzk` differs textually) | critical for differential alignment; **soundness OK** | 2-3d (needs §3 field registry first) | `Veir/Passes/Felt/Combine.lean:62` |
| 2 | No `FieldSpecAttr` (`#felt.field<name, prime>`) and no `llzk.fields` module-attribute registry | major (programs with custom fields fail to parse) | 2d | `Veir/IR/Attribute.lean` |
| 3 | No verification that `!felt.type<"name">`'s `name` is in the known-fields set (`bn128 / bn254 / babybear / goldilocks / mersenne31 / koalabear` per LLZK's `Field.cpp:99-119`, plus any `llzk.fields`-registered) | major | 1d (after §3.2) | `Veir/Parser/AttrParser.lean:386` |
| 4 | No `TypesUnify<"lhs","rhs">` check on binary ops; VEIR accepts `"felt.add"(%i32, %i32) : (i32, i32) -> i32` | major | 0.5d | `Veir/Verifier.lean:764-787` |
| 5 | No operand-is-felt check (LLZK gates on `LLZK_FeltType` per `Ops.td:33,60`) | major | 0.5d | same |
| 6 | 11 of 18 ops have no folder at all: `pow, div, inv, uintdiv, sintdiv, umod, smod, bit_and, bit_or, bit_xor, bit_not, shl, shr` | major (folds we accept will keep growing the diff against LLZK's canonicalizer) | 3-4d after §3.2 (some folds need `modInversePrime`) | `Veir/Passes/Felt/Combine.lean` |
| 7 | `NotFieldNative` context-gating absent: LLZK rejects `felt.bit_and` outside a `function.def` with `function.allow_non_native_field_ops`; VEIR accepts module-level use | major | 1d | `Veir/Verifier.lean` |
| 8 | `Commutative` trait absent (we hand-roll one canonicalization for `felt.add` via `add_const_swap`; `mul`, `bit_and/or/xor` have nothing) | minor (sound; just doesn't canonicalize) | 1d (add 4 patterns + 4 theorems) | `Veir/Passes/Felt/Combine.lean:247` |
| 9 | `FeltConstAttr.value : Int` rather than `APInt` — bit-width info lost. Round-trip survives because decimal print is width-agnostic; matters only when we add bit-width-sensitive folds (e.g., `bit_not` needs bitWidth to mask) | minor (today) | included with §6 | `Veir/IR/Attribute.lean:194` |
| 10 | No custom assembly format: LLZK emits `%c = felt.add %a, %b : !felt.type<"bn254">, !felt.type<"bn254">`; VEIR only generic | minor (blocks ingesting any LLZK source file) | 2-3d for the 18 ops | `Veir/Parser/MlirParser.lean`, `Veir/Printer.lean` |
| 11 | Test coverage at LLZK parity: `llzk-lib/test/Dialect/Felt/` has 7 files / 1121 lines; we have ~5-10× less | minor (closes naturally once §6, §10 land) | 1-2d | `Test/LLZK/Felt/` |
| 12 | No bindings (C API / Python) | n/a for the port; major for downstream replacement (see §3) | excluded from port budget | — |

### 2.3 Suggested ordering

1. **Field registry** (§3.2 / §2): single biggest unlock. Lets §3.3,
   §3.6, §3.7 follow naturally and **makes our folds emit
   LLZK-canonical values**.
2. **Verifier checks** (§3.4, §3.5, §3.7): cheap, immediately
   surfaces existing test regressions.
3. **Folder completion** (§3.6 — 11 ops).
4. **Custom assembly format** (§3.10): real engineering, but matters
   only if we want to ingest stock LLZK source.

Total: ~12-15 engineer-days. Most of it is in §1 and §6, both gated
on a Field registry that doesn't exist today.

## 3. Q2 details — replacing the C++ implementation

### 3.1 What depends on LLZK Felt today

Spawning a survey of `llzk-lib/` returns the following consumers:

- **CLI**: `llzk-opt` (`llzk-lib/tools/llzk-opt/llzk-opt.cpp`).
- **C API**: 15 exported `llzkFelt_*` constructors in
  `llzk-lib/lib/CAPI/Dialect/Felt.cpp` (123 LOC).
- **Python bindings**: `llzk-lib/lib/Bindings/Python/LLZKRegistration.cpp`
  registers Felt into an `mlir.ir.Context`.
- **Sibling LLZK dialects**: Bool's `bool.cmp` folder dispatches over
  `FeltConstAttr` (`Bool/IR/Ops.cpp:136-137`); Cast's `cast.tofelt`
  type-checks against `FeltType` (`Cast/IR/Ops.cpp:28-40`); Function,
  Global, Struct, Polymorphic all reference `felt::*`.
- **Transforms**: `LLZKPolyLoweringPass` (the polynomial-degree
  pass), `LLZKLoweringUtils`, `LLZKInliningExtensions`,
  `LLZKInlineStructsPass`, `LLZKRedundantReadAndWriteEliminationPass`.
- **Analyses**: `IntervalAnalysis`, `Intervals`, `SourceRef`,
  `SourceRefLattice`. (`CHANGELOG.md:3` notes interval analysis was
  just extended to `felt.uintdiv`, `felt.sintdiv`, `felt.bit_or`.)
- **Backends**: All four — `R1CSLoweringPass`, `SMTLoweringPass`,
  `ZKLeanToLLZK`/`LLZKToZKLean`, `PCLLoweringPass` — consume Felt
  ops via `dyn_cast<AddFeltOp>`-style C++ pattern matching.

Felt is the canonical algebraic substrate for everything downstream
of LLZK. Replacing the dialect implementation is not a local change
to a single header.

### 3.2 Strategy comparison (full table in source agent output)

| Strategy | Effort | What it buys | What it doesn't |
|---|---|---|---|
| **A. Verified-output oracle** (LLZK primary, VEIR certifies via differential) | **2-4 mo** | Continuous proof of LLZK ↔ VEIR equivalence; publishable discrepancies; certification product | No binary replacement |
| **E. Proof-certificate generator** (Lean emits certs, LLZK checks) | 6-10 mo | LLZK passes become *certifiably* equivalent to a Lean spec; small TCB | Doesn't replace the binary |
| **D. MLIR plugin via FFI** | 8-14 mo | Verified rewrites hosted without dispatch reimpl | Brittle to MLIR ABI churn; speculative |
| **B. Lean → C++ extraction** | 12-18 mo | A verified canonicalizer drop-in inside LLZK with small TCB | Requires building a Lean → C++ extractor that handles a Mathlib-using codebase |
| **C. Drop-in `veir-opt` replaces `llzk-opt`** | **30-60+ mo** | Self-contained verified compiler | Diverges from upstream the moment Veridise touches `llzk-lib`; reimplements MLIR core + C API + Python + 4 backends |

### 3.3 Why Strategy C is unrealistic

Each line is independently order-of-magnitude weeks-to-months:

- VEIR has no MLIR pass manager — passes are Lean structures, not
  `mlir::Pass` instances.
- VEIR has no `OpInterface` registry; downstream LLZK passes
  dispatch through `dyn_cast<FeltBinaryOpInterface>` (`OpInterfaces.td:19`).
- VEIR has no C API and Lean's FFI is one-directional (Lean calls C,
  not the reverse through opaque vtables).
- VEIR's `ZMod p` model imports Mathlib (`Veir/Data/Felt/Basic.lean:3`);
  no realistic path to a C-API-compatible runtime without dragging
  Mathlib in or rewriting the model.
- All four backends consume LLZK's C++ Op types directly. Either
  reimplement each backend in Lean, or define an IR-exchange format
  that round-trips through both — neither is funded.

### 3.4 Recommended next steps for the *port* track

Per Q1, the Felt port is **~12-15 days** from "indistinguishable from
LLZK on the test corpus". Order the next session as:

1. Land a Field registry (`Veir/Data/Felt/Field.lean`?) with the
   6 LLZK-built-in fields (`bn128, bn254, babybear, goldilocks,
   mersenne31, koalabear`) and a registration hook for
   `#felt.field<name, prime>`. Drives §1, §3, §6 of §2.2.
2. Extend `Veir/Verifier.lean:764-787` with `TypesUnify` and
   operand-is-felt checks.
3. Thread modular reduction through the four existing constant
   folds (`constant_fold_{add,sub,mul,neg}`); update the soundness
   theorems to (still) hold over `ZMod p`.
4. Add folders for the 11 currently-unfolded ops, in priority order
   driven by LLZK's `felt_const_fold.llzk` coverage.
5. Add `NotFieldNative` context-gating in the verifier (requires
   region-aware traversal; aligns with Phase F.2.4 work).
6. Add `#felt.field<>` parser + `llzk.fields` module-attribute
   handling.
7. Expand `Test/LLZK/Felt/` to mirror `llzk-lib/test/Dialect/Felt/`.

Custom assembly format (§10) is **optional** for the port narrative
— round-trip works in generic form already; it only matters when
ingesting LLZK source. Defer.

### 3.5 Recommended next steps for the *replacement* track

Reframe `harness/verification-plan.md` to explicitly include three
new sections:

1. **§Replacement strategies and goals** — declare that *dialect-as-
   replacement* (Strategy C) is out of scope; **Strategy A is v1**.
   Reference the ranking in this document.
2. **§Integration debt inventory** — per §3.1 above: every consumer
   of LLZK Felt, its current VEIR coverage, and the work needed for
   replacement. Cross-link `harness/coverage.md`.
3. **§Certification milestones** — concrete acceptance criteria for
   Strategy A. Suggested v1 bar: "every `llzk-lib/test/Dialect/Felt/`
   input differential-passes via `scripts/llzk-diff.sh`, and every
   LLZK Felt folder is mirrored by a VEIR `Combine.lean` pattern
   with a paired theorem". Today's coverage: 1 of 4 LLZK Felt test
   files; 4 of LLZK's 18 op-folders.

### 3.6 Highest-risk unknowns for the replacement track

1. **Sibling-dialect coupling.** `bool.cmp` folds over `FeltConstAttr`
   (`llzk-lib/lib/Dialect/Bool/IR/Ops.cpp:136-137`); `polymorphic`
   flattening promotes `IntegerAttr → FeltConstAttr`
   (`llzk-lib/lib/Transforms/.../FlatteningPass.cpp:389-393`). Any
   Felt replacement must preserve these contracts; they're not
   documented anywhere except the C++ source.
2. **TableGen drift.** LLZK's TableGen regenerates op classes, C API
   headers, and trait dispatch on every upstream version bump. A
   replacement must either pin LLZK or build a parallel
   TableGen-equivalent in Lean.
3. **Backend dependence on C++ Op types.** No backend can be
   retargeted at Lean without either reimplementing the backend or a
   generic IR exchange. "What's the cheapest backend port?" is
   unanswered.
4. **Mathlib ABI.** `Veir/Data/Felt/Basic.lean:3` depends on
   `Mathlib.Data.ZMod.Basic`. Any extraction / FFI path inherits
   Mathlib, which is incompatible with a small TCB.

## 4. Bet-against scenarios

If someone bets $1000 that a Felt program behaves identically under
our Lean port and LLZK's C++ implementation, they will *lose* against
any of:

1. A program inside `!felt.type<"bn254">` (or any named field)
   containing constant arithmetic whose un-reduced result exceeds
   the modulus. Soundness OK; output differs textually.
2. A program declaring `llzk.fields = #felt.field<...>` on the root
   module. Parser failure in VEIR.
3. A program using LLZK's custom assembly form
   (`%c = felt.add %a, %b`). Parser failure in VEIR.
4. A program with `felt.bit_and`/`shl`/etc. outside a `function.def`
   with `function.allow_non_native_field_ops`. LLZK rejects, VEIR
   accepts.
5. A program with `"felt.add"(%i32, %i32) : (i32,i32) -> i32`. LLZK
   rejects (TypesUnify violation), VEIR accepts.

Programs that (a) use unspecified-field `!felt.type` and (b) never
trigger overflow in their constants and (c) route through VEIR's
generic-form printer round-trip cleanly today. That's the regime
where the current port is honest.

## 5. Open questions

- Is "Felt port" v1 the same bar as "Felt parity"? If yes, the next
  ~12-15 days of work are clearly scoped above. If no (e.g., parity
  is the eventual goal but v1 is a smaller story), we should write
  down the v1 bar explicitly.
- Where does the Strategy A → Strategy E ramp live in the
  `verification-plan.md` hierarchy? Today the plan only covers
  pass-verification pilots, not certification harness work.
- Is sibling-dialect coupling (§3.6 #1) discoverable from C++ alone,
  or do we need Veridise to surface contracts?
- Field registry design: shared between VEIR's IR and the verified
  proof layer, or two parallel structures with a coherence lemma?
  The latter is honest but doubles the surface.

## 6. Pointers

- LLZK ground truth: `llzk-lib/include/llzk/Dialect/Felt/IR/`,
  `llzk-lib/lib/Dialect/Felt/IR/`,
  `llzk-lib/test/Dialect/Felt/`,
  `llzk-lib/lib/Util/Field.cpp`.
- VEIR port: `Veir/Dialects/LLZK/Felt/`, `Veir/IR/Attribute.lean`,
  `Veir/OpCode.lean`, `Veir/Parser/AttrParser.lean`,
  `Veir/Verifier.lean`, `Veir/Passes/Felt/`, `Veir/Data/Felt/`,
  `Test/LLZK/Felt/`.
- Companion docs: `LLZK_PORT_RETRO.md`, `SESSION_RETRO_2026-05-17.md`,
  `REVIEW_2026-05-20.md`, `harness/coverage.md`,
  `harness/verification-plan.md`, `harness/differential.md`,
  `harness/porting-notes.md`.
