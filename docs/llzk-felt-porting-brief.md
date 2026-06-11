# LLZK Felt Porting Brief For VEIR Maintainers

Last reviewed: 2026-06-11

Audience: VEIR maintainers and contributors.

Status: meeting brief. This document summarizes the experience of porting a
production-like C++ MLIR dialect into VEIR, using the LLZK Felt dialect as the
concrete case study. It is not acceptance evidence by itself.

Companion slides live under
`docs/slides/llzk-felt-porting/LlzkFeltPortingSlides/Slides.lean`.

## Purpose

The LLZK Felt port is a useful stress test for VEIR because it is not a toy
dialect. The source of truth is an existing C++/TableGen MLIR dialect with
custom syntax, custom attributes, verifier and folder behavior, field-registry
semantics, tests, and downstream users.

The long-term project goal is a high-assurance drop-in replacement for the C++
LLZK Felt dialect path. That means:

- existing Felt workloads can use a VEIR-backed path without source changes;
- the selected VEIR profile produces output accepted by the same downstream
  consumers as the C++ path;
- intentional differences from C++ LLZK are explicit, reviewed, and gated;
- the assurance claim says exactly what was checked, what was proved, and what
  remains trusted.

This is not the same as replacing all of `llzk-opt`. The near-term target is
the Felt dialect and Felt-affecting canonicalization/folding path.

## Executive Takeaways

- Porting an existing C++ MLIR dialect to VEIR is feasible today, but it is not
  yet a straightforward engineering workflow.
- The LLZK Felt port needed a companion harness in `llzk-lean` to supply source
  truth, differential evidence, pin checks, expected-divergence polarity, and
  caveat documentation.
- VEIR gives a strong foundation for machine-checked rewrite implementation,
  but the current assurance story is narrower than "compiler equivalence".
- The biggest upstream wins would be porting documentation, ODS/TableGen-driven
  scaffolding, total operation metadata gates, reusable MLIR differential
  harnesses, profile-selectable pass pipelines, and proof-statement templates.
- For drop-in replacement work, VEIR should distinguish two profiles:
  - a C++-parity profile used for adoption, regression testing, and fallback;
  - an enhanced VEIR profile used for verified improvements over the C++ path.

## Current Concrete Status

Source and integration facts:

| Item | Current state |
|---|---|
| Working VEIR fork | `project-llzk/veir` |
| Integrated Felt milestone | `project-llzk/veir#1`, merged at `45d31a20b4ff10498f7caba3c8b635553cc93dea` |
| Upstream opencompl PR | `opencompl/veir#829`, closed unmerged |
| llzk-lean accepted VEIR pin | `d899d95004d4bd988c8456d686c33b11a7a5eb4a` |
| Accepted LLZK source basis | `project-llzk/llzk-lib` commit `db922857bc5a88a9107627ef6b36a8b5e57bc5c2` |
| Current LLZK Felt op count | 18 accepted mnemonics |
| Current VEIR Felt rewrite surface | 15 patterns over 5 ops: `const`, `add`, `sub`, `mul`, `neg` |
| Clean-pin differential corpus | `21 pass (incl. expected-diverge), 0 fail` |
| Current expected divergences | 10 canonical VEIR-only algebraic rewrites |
| Strategy E cert coverage | 2 of 15 patterns; no real runtime MLIR matcher yet |

Current implementation capabilities in VEIR:

- LLZK Felt IR representation.
- Parser/printer support sufficient for the current corpus.
- Verifier shape checks for the currently modeled surface.
- `felt-combine` pass with 15 rewrite patterns.
- Arithmetic proofs over `Felt p := ZMod p`.
- Structural rewrite precondition proofs for the 15 current patterns.
- A standalone value-level interpreter proof-of-concept in
  `Veir/Passes/Felt/InterpModel.lean`.
- Differential driver in `scripts/llzk-diff.sh`.

Current gaps:

- 13 accepted LLZK Felt operations still lack VEIR semantic models and
  interpreter cases: `pow`, `div`, `uintdiv`, `sintdiv`, `umod`, `smod`,
  `inv`, `bit_and`, `bit_or`, `bit_xor`, `bit_not`, `shl`, and `shr`.
- The current `felt-combine` profile is stronger than C++ LLZK for some
  nonconstant algebraic rewrites. That is valuable, but it is not the same
  thing as a C++-parity profile.
- There is no whole-program rewrite semantic theorem.
- There is no direct `llzk-opt` replacement integration point.
- The proof-certificate route is only a prototype: the checker can load and
  dispatch certificate metadata, but it does not yet validate real MLIR rewrite
  events.

## What Porting Required

The LLZK Felt port required work in several layers.

1. **Source truth.** We had to freeze the C++ source basis by exact commit and
   record which LLZK files define the dialect, folders, field registry, tests,
   and observed behavior.

2. **Operation modeling.** Felt operation names had to be represented in
   VEIR's opcode universe, with properties for `felt.const` and `Unit`
   properties for other currently modeled operations.

3. **Type and attribute modeling.** LLZK Felt uses a typed field-element
   constant attribute, with named fields such as `babybear`. VEIR had to model
   the `!felt.type` and `#felt<const N> : !felt.type<"...">` surface rather
   than using an integer-attribute workaround.

4. **Parser/printer interop.** The harness compares generic MLIR output from
   `llzk-opt` and `veir-opt`, which required normalization for cosmetic
   differences and explicit handling of LLZK custom assembly through a
   `--lower-first` path.

5. **Folder/canonicalization behavior.** C++ LLZK folder behavior had to be
   understood case by case: registered field names, field mismatch, bare or
   unknown fields, modular reduction, divide-by-zero no-fold cases, signed
   representative behavior, bitwidth, and `NotFieldNative` scope.

6. **Rewrite proofs.** VEIR rewrites needed both algebraic facts and IR
   well-formedness preservation facts. Those are separate from proving that
   the executable compiler pass preserves runtime semantics.

7. **Differential harnessing.** The companion `llzk-lean` repo became the
   place where we track accepted pins, exact source commits, corpus polarity,
   clean dependency evidence, known divergences, and proof/certificate caveats.

8. **Review gates.** Because the port is intended as a replacement path, every
   phase had to be explicit about what was newly proved, what was only tested,
   and what remained trusted.

## Pain Points And Upstream Opportunities

This table is the most actionable part for upstream VEIR.

| Area | Pain point from the Felt port | Upstream improvement |
|---|---|---|
| Porting guide | There is no single workflow for "take an existing MLIR dialect and port it into VEIR". We had to discover the needed layers by doing the port. | Add a dialect-porting guide with an end-to-end checklist: source snapshot, ODS inventory, opcodes, properties, parser/printer, verifier, traits, side effects, folders, tests, proofs, and differential evidence. |
| ODS/TableGen ingestion | C++ LLZK's dialect truth lives in TableGen plus C++. VEIR currently requires manual reconstruction of much of that shape. | Provide an ODS/TableGen-to-VEIR scaffolding tool, even if partial. It should generate opcode skeletons, property records, parser hooks, printer hooks, verifier placeholders, trait metadata, and a coverage checklist. |
| Total operation metadata | New operations can silently fall into conservative defaults. Phase 10 found this concretely: after an upstream DCE side-effect API change, Felt ops defaulted to side-effecting and DCE stopped removing dead Felt constants. | Make important op metadata total and auditable. Add a gate that requires every registered op to declare side effects, speculatability/UB behavior, terminator status, traits, and interfaces explicitly or through an intentional default with a warning. |
| Side effects and DCE | The DCE behavior depends on `OperationPtr.hasSideEffects`. A missing dialect entry changed observable output in the replacement smoke. | Add dialect-local side-effect declarations and tests. A new dialect should get generated tests for dead pure constants/arithmetic and retained side-effecting operations. |
| Pass profiles | `felt-combine` contains useful enhanced rewrites, but drop-in adoption also needs a C++-parity profile. Today the distinction is mostly social/documentary. | Add first-class pass profiles or pass parameters so downstreams can select "parity", "enhanced", or "experimental" behavior and record that selection in evidence. |
| Custom attributes and types | Felt constants needed structured field-element attributes with field names and modular semantics. This was not just a generic integer constant. | Provide a documented recipe and templates for custom MLIR attribute/type parser-printer implementations, round-trip tests, and semantic value extraction. |
| External semantic tables | LLZK field behavior depends on a C++ field registry. VEIR had to mirror the registry and treat unknown fields as no-fold cases. | Add a pattern for external semantic tables: exact source commit, generated mirror, drift checker, and runtime lookup API. |
| Folder behavior | C++ folders are not just algebraic identities. They include field-registration guards, matching field-name checks, no-fold cases, and representational details. | Add a folder-porting template that separates matcher, side conditions, result construction, value semantics, and no-fire cases. |
| Traits and interfaces | C++ MLIR dialects use traits/interfaces such as native-field restrictions and operation properties that are easy to omit in a manual port. | Generate a trait/interface ledger from ODS and make missing trait decisions visible in CI. |
| Differential harnessing | The project needed a custom harness to compare `llzk-opt` and `veir-opt`, normalize output, classify expected divergences, and reject tool skips. | Upstream VEIR should provide a reusable differential harness template for MLIR tool comparisons, including lower-first mode, expected-divergence polarity, skip handling, output normalization hooks, and corpus dashboards. |
| Custom assembly | LLZK workloads use custom assembly, but VEIR comparison is easiest over generic MLIR. | Standardize a lower-first bridge: C++ frontend lowers custom assembly to generic MLIR, then VEIR runs the replacement pass. Document exactly what remains trusted in that bridge. |
| Proof boundaries | It is easy for readers to overread "verified rewrite" as semantic preservation of the compiler pass. For Felt, current proofs are arithmetic identities plus structural rewrite well-formedness, not whole-program semantics. | Provide proof-statement templates that name theorem layers: arithmetic/value lemma, matcher-side-condition lemma, rewrite well-formedness lemma, runtime semantic lemma, whole-program theorem. |
| Certificate metadata | Strategy E currently hand-maintains a small certificate catalog in the companion repo. That can drift from executable patterns. | Attach auditable metadata to executable rewrite patterns so certificates, docs, and differential ledgers can be generated or checked against the same source. |
| Clean executable evidence | The harness had to guard against stale `veir-opt` binaries. | Add a standard "build before evidence" wrapper or binary freshness marker for `veir-opt`-based evidence. |
| Corpus coverage | The current corpus tracks cases manually. It is easy to miss operations, no-fire cases, or C++ tests. | Provide a coverage dashboard format keyed by op, folder case, rewrite pattern, proof status, certificate status, and differential status. |
| Upstream examples | There is no canonical production-like dialect port example for maintainers and users to study. | Keep an upstream case-study document based on LLZK Felt, plus a small toy dialect example that shows the same workflow with fewer details. |

## Assurance: What VEIR Provides Here

VEIR is useful because it can make the implementation and proof surface more
explicit than a conventional C++ pass. In this port, VEIR currently provides:

- executable Felt rewrite patterns;
- Lean-checked arithmetic identities for those patterns;
- Lean-checked structural preconditions for the rewrite operations;
- a typed IR representation that makes many malformed states explicit;
- a path toward value-level semantic statements for Felt runtime values;
- a single place where rewrite metadata could eventually drive certificates,
  docs, and tests.

That is meaningful assurance. It is not the same as proving that the whole C++
LLZK dialect implementation and the VEIR implementation are equivalent.

## Assurance: What VEIR Does Not Yet Provide

The current LLZK Felt work does not yet provide:

- full semantic coverage of all 18 LLZK Felt operations;
- full parity with every C++ folder case;
- proof that the current `felt-combine` pass preserves whole-program semantics;
- proof that the parser/printer bridge is semantics-preserving;
- proof that the differential normalizer is complete or harmless;
- runtime verification of actual LLZK MLIR rewrite events;
- a complete replacement path for `llzk-opt`;
- automatic protection against source drift in C++ LLZK unless the companion
  source-truth gates are run.

The important communication point is that VEIR can improve assurance, but only
when the claim is scoped to the implemented theorem and harness layer.

## Trusted Base In The Current Approach

The current assurance story trusts:

- the accepted LLZK source commit and source ledger;
- LLZK's `llzk-opt` binary used as the C++ comparison oracle;
- the C++/MLIR frontend path used to lower custom LLZK assembly to generic
  MLIR;
- VEIR's parser, printer, IR model, pass manager, and pattern rewriter;
- Lean kernel and imported Mathlib facts;
- the mirrored field registry and any generated or hand-maintained semantic
  tables;
- the differential normalizer and expected-divergence classification;
- for Strategy E, the JSON schema, C++ checker, matcher/listener wiring, and
  MLIR APIs.

Making this trusted base small and auditable should be an upstream design goal.

## Drop-In Replacement Roadmap

The practical roadmap is:

1. **Phase 9: roadmap and claim reset.** Completed locally. The docs now
   separate C++ parity from enhanced VEIR behavior and list non-claims.

2. **Phase 10: toolchain replacement spike.** Bootstrapped. The first path is
   an external driver:
   - LLZK lowers custom assembly with `llzk-opt --mlir-print-op-generic`;
   - VEIR runs `veir-opt -p=felt-combine,dce`;
   - LLZK runs `llzk-opt --canonicalize --mlir-print-op-generic`;
   - the harness compares normalized generic MLIR.

3. **Phase 11: full coverage ledger.** Replace the current operation gap
   ledger with a matrix covering syntax, verifier, traits, folders,
   parser/printer, differential tests, proofs, certificates, and assumptions.

4. **Phase 12: C++-parity profile.** Add/configure a VEIR profile that matches
   C++ LLZK behavior, while preserving an enhanced profile for verified
   improvements.

5. **Phase 13: corpus expansion.** Mirror `llzk-lib/test/Dialect/Felt/` and
   representative workloads.

6. **Phase 14: proof-certificate prototype.** Try one real aligned fold,
   initially `constant_fold_add`, through a real MLIR matcher and listener.

7. **Phase 15: proof statement hardening.** Tie runtime proofs to executable
   matchers, side conditions, result constructors, field registry behavior,
   and runtime values.

8. **Phase 16: drop-in readiness review.** Run the selected toolchain path on
   the full corpus and selected workloads, then publish final caveats and TCB.

## Specific Upstream Asks

The highest-value upstream work items are:

1. **Create a dialect-porting guide.**
   The guide should tell a user exactly how to port a C++ MLIR dialect into
   VEIR, what evidence to collect, and what claims are valid at each stage.

2. **Add ODS/TableGen scaffolding.**
   Even a partial generator would reduce manual drift and make missing pieces
   obvious.

3. **Make op metadata explicit and checked.**
   Side effects, terminator status, traits, interfaces, and speculatability
   should not silently default in ways that change pass behavior.

4. **Add pass-profile support.**
   A downstream should be able to say "run the C++ parity profile" or "run the
   enhanced verified profile" and have that profile show up in logs/evidence.

5. **Ship a reusable MLIR differential harness.**
   The LLZK harness should not remain bespoke. Upstream should provide the
   skeleton for lower-first comparisons, expected-divergence polarity, skip
   handling, normalizers, and coverage reports.

6. **Define proof-layer templates.**
   Upstream docs should distinguish arithmetic lemmas, runtime value lemmas,
   executable matcher lemmas, rewrite well-formedness, and whole-program
   semantic preservation.

7. **Colocate rewrite metadata with executable patterns.**
   Certificates, dashboards, and docs should be generated or checked from the
   same rewrite definitions that `veir-opt` runs.

8. **Adopt a production-like case study.**
   LLZK Felt can serve as a realistic example for porting a C++ MLIR dialect:
   custom attributes, source drift, field registry semantics, folder no-fire
   behavior, enhanced rewrites, and downstream replacement goals.

## Questions For The Maintainer Meeting

- Does VEIR want to support "port an existing MLIR dialect" as a first-class
  workflow, or is that expected to remain downstream project work?
- Should VEIR grow an ODS/TableGen import path, or should downstreams maintain
  dialect definitions by hand?
- What is the intended upstream story for operation traits, side effects,
  memory effects, and speculatability?
- How should VEIR represent pass profiles such as parity, enhanced, and
  experimental?
- Which differential harness pieces belong in upstream VEIR versus companion
  downstream repos?
- What theorem layer should upstream VEIR encourage users to claim first for a
  rewrite: arithmetic identity, value-level semantics, executable matcher
  semantics, or whole-program preservation?
- Should rewrite metadata be a first-class API so certificate generation and
  coverage dashboards can share the executable source of truth?
- Would maintainers accept LLZK Felt as an upstream case study or example
  document even if the full dialect remains in the `project-llzk` fork?

## Checklist For Future C++ MLIR Dialect Ports

A future dialect port should have a checklist like this before claiming
drop-in status:

- Exact upstream source commit selected.
- ODS files, C++ implementation files, tests, and semantic side tables listed.
- Every operation mapped to a VEIR opcode.
- Every operation has explicit properties or an explicit `Unit` decision.
- Every operation has side-effect, terminator, trait, and interface status.
- Custom types and attributes round-trip in generic MLIR.
- Custom assembly path is either implemented in VEIR or explicitly lowered
  through the C++ frontend.
- Every folder/canonicalization case has positive and no-fire tests.
- Expected divergences have exact polarity and rationale.
- C++-parity and enhanced profiles are separated.
- Differential corpus covers source tests and representative workloads.
- Proof statements identify their layer and assumptions.
- Trusted base and caveats are published.
- A clean checkout can reproduce the evidence.

## Bottom Line

The LLZK Felt port shows that VEIR can be a credible foundation for high
assurance dialect replacement work. It also shows that the hard part is not
just writing rewrites in Lean. The hard part is turning an existing C++ MLIR
dialect into an auditable replacement package: source truth, operation
metadata, custom attributes, folder side conditions, pass profiles,
differential evidence, proof boundaries, and trusted-base documentation.

If upstream VEIR makes those steps ergonomic, then "port an existing C++ MLIR
dialect to VEIR" becomes a repeatable workflow rather than a bespoke research
project.
