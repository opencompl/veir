import VersoSlides
import Verso.Doc.Concrete

open VersoSlides

set_option verso.code.warnLineLength 120

#doc (Slides) "LLZK Felt in VEIR" =>

# LLZK Felt in VEIR

Porting a production-like C++ MLIR dialect into VEIR

2026-06-11

:::notes
Goal for the meeting: show the Felt port as a concrete case study, not as a
final replacement claim. Emphasize what worked, what remains missing, and what
upstream VEIR could provide to make this workflow repeatable.
:::

# Talk Shape

* Background: LLZK and `llzk-lib`
* Why the Felt dialect matters
* What "drop-in replacement" should mean
* C++ LLZK Felt vs VEIR Felt today
* Current assurance, gaps, blockers, pain points
* What `llzk-lean` contributes
* Upstream VEIR asks

# LLZK / `llzk-lib`

* LLZK is an MLIR-based compiler stack for zero-knowledge workloads.
* `llzk-lib` contains the production C++ MLIR dialect implementation.
* The Felt dialect models field-element values and operations used by proof
  systems and arithmetic circuits.
* For this effort, C++ LLZK remains the source of behavioral truth until a
  reviewed replacement path exists.

:::notes
Keep this high-level. The audience knows compilers; they may not know LLZK's
domain-specific arithmetic constraints.
:::

# What The Felt Dialect Does

* Represents field-element types: `!felt.type` and named fields like
  `!felt.type<"babybear">`.
* Represents field constants:

```code text
#felt<const 42> : !felt.type<"babybear">
```

* Provides arithmetic, division/modulo, inverse, bitwise, and shift operations.
* Implements folder/canonicalization behavior in C++.
* Depends on field-registry semantics: field names, primes, reduction, and
  no-fold cases.

# Accepted Felt Operation Surface

Current LLZK Felt operation ledger has 18 accepted mnemonics:

```code text
const add sub mul pow div uintdiv sintdiv umod smod
neg inv bit_and bit_or bit_xor bit_not shl shr
```

Current VEIR coverage:

* Semantic models and rewrite work for `const`, `add`, `sub`, `mul`, `neg`.
* 13 operations still need semantic models, interpreter cases, folders, and
  tests.

# Why Port Felt To VEIR?

* Make Felt rewrites and side conditions explicit.
* Move from trusted C++ peepholes toward machine-checked rewrite structure.
* Give LLZK a path to higher-assurance canonicalization/folding.
* Use the port as a production-like case study for VEIR dialect replacement.

Not the claim:

* "VEIR already replaces all of `llzk-opt`."
* "All Felt semantics are proved."
* "The current differential corpus proves compiler equivalence."

# Drop-In Replacement: Working Definition

A Felt drop-in replacement should mean:

* existing Felt workloads need no source changes;
* the selected VEIR profile produces output accepted by the same downstream
  consumers as the C++ path;
* intentional differences from C++ LLZK are reviewed and gated;
* the assurance claim says exactly what was tested, proved, and trusted;
* rollback to the C++ path remains available.

# Two Profiles, Two Claims

*C++-parity profile*

* Adoption and debugging baseline.
* Match accepted C++ LLZK behavior closely.
* Divergences block adoption unless disabled or fixed.

*Enhanced VEIR profile*

* Value case.
* Allows verified rewrites beyond C++ LLZK.
* Divergences become features only with semantic evidence and downstream
  compatibility.

# Current Toolchain Spike

Phase 10 starts with an external-driver path:

```code text
LLZK custom assembly
  -> llzk-opt --mlir-print-op-generic
  -> generic MLIR

C++ path:
  llzk-opt --canonicalize --mlir-print-op-generic

VEIR path:
  veir-opt -p=felt-combine,dce

Harness:
  normalize and compare generic MLIR
```

This is not yet a direct `llzk-opt` replacement.

# Side-By-Side: C++ LLZK Felt

Strengths:

* Production source of truth today.
* Full accepted Felt operation surface.
* Existing parser, printer, verifier, folders, and tests.
* Integrated into `llzk-opt` and downstream workflows.

Costs:

* Rewrite/folder correctness is trusted C++.
* Side conditions are spread across ODS, C++, registry code, and tests.
* No machine-checked proof layer.

# Side-By-Side: VEIR Felt

Strengths:

* Executable Lean implementation of current Felt rewrite surface.
* 15 rewrite patterns over 5 operations.
* Arithmetic identity proofs for patterns.
* Structural rewrite precondition proofs.
* Differential driver against `llzk-opt`.

Costs:

* Only partial Felt operation coverage.
* Current `felt-combine` is enhanced, not parity-only.
* No whole-program semantic theorem.
* No direct `llzk-opt` integration point yet.

# What Worked

* Typed Felt constants replaced earlier integer-attribute workarounds.
* Registered-field add/sub/mul/neg constant folds now align on selected cases.
* Bare or unknown-field fold preconditions now align for the first target.
* The clean-pin corpus currently records:

```code text
21 pass (incl. expected-diverge), 0 fail
```

* The harness makes expected divergences explicit and exact.

# Current Known Divergences

The corpus records 10 canonical expected divergences.

These are mostly VEIR-only nonconstant algebraic rewrites, for example:

* `x + 0 -> x`
* `x * 1 -> x`
* `x - x -> 0`
* `x + (-x) -> 0`
* reassociation with constants

These are not automatically bad. They are parity blockers and enhanced-profile
candidates.

# Work Remaining

* Implement missing 13 operation semantics and folders.
* Build an explicit C++-parity VEIR profile.
* Expand corpus to mirror `llzk-lib/test/Dialect/Felt/`.
* Cover positive, no-fire, verifier-reject, and expected-failure cases.
* Tie runtime proofs to executable matchers, side conditions, result
  constructors, and field registry behavior.
* Decide whether proof certificates add enough assurance to expand.

# Pain Points From The Port

* No standard "port C++ MLIR dialect to VEIR" workflow.
* ODS/TableGen facts had to be reconstructed manually.
* Operation metadata was easy to omit.
* Field registry semantics had to be mirrored and guarded.
* C++ folders encode no-fire side conditions, not just algebra.
* Custom assembly needed a lower-first bridge through `llzk-opt`.
* Proof claims needed careful documentation to avoid overclaiming.

# Concrete Phase 10 Lesson

After an upstream DCE side-effect API change, Felt ops defaulted to
side-effecting.

Consequence:

* `felt-combine` folded an add;
* DCE did not erase dead Felt constants;
* the workspace VEIR smoke diverged from the accepted clean pin.

Fix:

```code lean
| .arith _ | .comb _ | .mod_arith _ | .datapath _ | .felt _ => false
```

Takeaway: operation metadata should be total and audited.

# Assurance VEIR Provides Today

For the current Felt surface:

* executable rewrite definitions;
* Lean-checked arithmetic identities;
* Lean-checked structural rewrite preconditions;
* a typed IR model;
* a path toward value-level runtime semantics;
* a place to colocate rewrite metadata, certificates, tests, and docs.

This is meaningful. It is not yet compiler-equivalence.

# Assurance VEIR Does Not Yet Provide

Not currently provided:

* full 18-operation Felt semantic coverage;
* full C++ folder parity;
* whole-program `interpret(after) = interpret(before)` theorem;
* parser/printer bridge proof;
* runtime verification of real LLZK MLIR rewrite events;
* direct `llzk-opt` replacement;
* automatic source-drift protection without the companion harness.

# What `llzk-lean` Adds

`llzk-lean` is the assurance and integration harness:

* exact LLZK source-truth ledger;
* accepted VEIR dependency pin checks;
* differential corpus and expected-divergence polarity;
* clean-pin evidence path;
* certificate schema and current C++ checker prototype;
* review artifacts and non-claim documentation.

It does not implement the Felt dialect itself.

# Bridge From VEIR To LLZK

Current bridge:

* VEIR implements rewrites and proof-side artifacts.
* `llzk-lean` consumes a clean VEIR pin.
* Differential harness compares `llzk-opt` and `veir-opt`.
* Certificate prototype explores runtime checking of LLZK rewrite events.

Future bridge:

* external wrapper,
* MLIR pass plugin,
* upstreamed `llzk-opt` integration,
* or a narrower folders-only replacement.

# Proof Certificates: Narrow POC First

Candidate:

* `constant_fold_add`

Prototype requirement:

* real MLIR matcher;
* rewrite listener;
* accepted good rewrite;
* rejected bad rewrite;
* explicit trusted base.

Decision point:

* Expand Strategy E only if it adds assurance beyond differential coverage
  without becoming a parallel hand-maintained compiler.

# Upstream VEIR Asks

Highest-value improvements:

* dialect-porting guide;
* ODS/TableGen scaffolding;
* total op metadata gates;
* side-effect/speculatability declarations;
* pass profiles: parity vs enhanced vs experimental;
* reusable MLIR differential harness;
* custom type/attribute templates;
* proof-layer templates;
* rewrite metadata API.

# Porting Checklist

Before a future dialect port claims drop-in status:

* exact source commit selected;
* ODS, C++ files, tests, semantic tables listed;
* every op mapped and metadata declared;
* custom attrs/types round-trip;
* custom assembly path identified;
* folder positive and no-fire cases covered;
* parity and enhanced profiles separated;
* proof layer and assumptions named;
* trusted base published;
* clean checkout can reproduce evidence.

# Discussion Questions

* Should "port an existing MLIR dialect" be a first-class VEIR workflow?
* Should VEIR grow ODS/TableGen import scaffolding?
* Where should traits, side effects, memory effects, and speculatability live?
* What is the right pass-profile API?
* Which differential harness pieces belong upstream?
* What theorem layer should VEIR recommend first for rewrites?
* Should executable rewrite metadata drive certificates and dashboards?

# Bottom Line

The LLZK Felt port shows VEIR can support high-assurance dialect replacement.

It also shows the hard part is not only writing Lean rewrites.

The repeatable workflow needs:

* source truth;
* operation metadata;
* custom attributes;
* folder side conditions;
* pass profiles;
* differential evidence;
* proof boundaries;
* trusted-base documentation.

That is the upstream ergonomics opportunity.
