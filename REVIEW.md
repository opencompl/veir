# VEIR Felt-Dialect Port — Adversarial Review: Findings

> **Status:** in progress. Last updated 2026-06-01.
> **Reviewer note:** Independent, adversarial review at the maintainer's
> request. Stance: assume each component is wrong/incomplete/unfaithful to
> LLZK until proven otherwise. Companion to `llzk-lean/docs/REVIEW.md`.
> Every Critical/High finding below was verified against source by the
> reviewer (not only by the fan-out agents); verification status is marked
> per finding. LLZK (`/home/alh/llzk-lib`, C++) is the ground-truth semantics
> VEIR must match.

---

## 0. Remediation landed (2026-06-01; F1 close 2026-06-02)

Fixes applied to this repo during the review (verified by a full `lake build`
under the repo's `v4.30.0-rc2` toolchain + `#print axioms`; the F1 close was
additionally re-verified by fresh adversarial review agents — axiom hygiene,
guard soundness, and wiring/VC3 all confirmed):

- **VC1 (framing):** `Combine.lean` docstring reframed — "5 of 18 felt ops
  implemented (13 opcode-only stubs)" + an explicit *"what 'verified' means"*
  section.
- **VC3 (cross-field fold unsoundness): FIXED.** Field-type-equality guard added
  to all 5 fold patterns; demonstrated live (`veir-opt -p=felt-combine`: a
  `bn254 + babybear` add stays unfolded; a same-field add folds).
- **VC2 (admitted preconditions): RESOLVED — all 15 of 15 patterns are now
  fully sorry-free AND axiom-clean** (`[propext, Classical.choice, Quot.sound]`,
  no `sorryAx`, no `Dom` axiom), verified by `lake build Veir.Passes.Felt.Combine`
  + `#print axioms` on each of the 15 (2026-06-02, F1). All pattern definitions
  now live in `Veir/Passes/Felt/RewriteLemmas.lean`; `Combine.lean` defines no
  pattern itself and references them unqualified in the `felt-combine` pass list.
  The close is built on three reusable, precondition-discharging tails plus a
  per-matcher in-bounds lemma library, all in `RewriteLemmas.lean`:
  - `projectToOperand` — projection shape (`replaceValue` + `eraseOp`): used by
    `right_identity_zero_add`, `right_identity_one_mul`, `neg_neg_to_self`,
    `add_sub_const_cancel`, `sub_add_const_cancel`.
  - `replaceWithNewOp` — single-`createOp` synthesis (`createOp` + `replaceOp`):
    used by `constant_fold_{add,sub,mul,neg}`, `self_subtraction_to_zero`,
    `right_zero_mul`, `add_neg_to_zero`, `add_const_swap`.
  - `replaceWithBinOpOfConst` — two-`createOp` synthesis (const then binop):
    used by `assoc_const_fold_{add,mul}`.
  In-bounds lemmas: `matchOp_inBounds` generalized over `opType` (with per-opcode
  wrappers `matchOp_inBounds_{add,mul,sub,neg,const}`); `match{Add,Mul,Sub,Neg}_spec`
  / `_inBounds`; `match{Neg,Add,Sub,Mul}FromValue_operand0_inBounds`;
  `getResult0_inBounds`, `getOperand_inBounds`, `newOp_getNumResults!_createOp`.
  All preconditions are discharged (not admitted); the three `WfIRContext` gaps
  (region count, result≠operand, op-has-parent) are supplied by sound defensive
  runtime guards as before. **The cross-field fold guard (VC3) is preserved** in
  the new `constant_fold_{sub,mul}` and `assoc_const_fold_{add,mul}` definitions.
- **VM1 (doc rot):** the two load-bearing dangling `harness/coverage.md`
  citations (`Combine.lean`, `Proofs.lean`) re-pointed to `REVIEW.md`.

**Key technique + finding from the structural close.** Discharging a pattern's
rewriter preconditions needs three facts that `WfIRContext` does **not** carry:
(a) the matched op's region count (`getNumRegions! = 0`), (b) SSA acyclicity
(`op.getResult 0 ≠ operand`), and (c) the op having a parent block. VEIR provides
(b) only via the **`axiom WfIRContext.Dom`**. We avoid that axiom entirely with
sound **defensive runtime guards** (each only skips the rewrite in degenerate
states impossible in well-formed IR). This makes the patterns self-contained and
axiom-clean. The deeper point stands (and is why every VEIR pass `sorry`s these):
`WfIRContext` encodes structural well-formedness but neither per-opcode shape
constraints nor SSA dominance — a substrate property, not a Felt defect. See
`FOLLOWUP.md` §1 (axiom inventory).

---

## 1. Scope & method

Reviewed: the VEIR Felt-dialect *port* — opcode set & op-info wiring
(`OpCode.lean`, `Dialects/LLZK/Felt/*`, `GlobalOpInfo.lean`), the
attribute/type representation and parser/printer (`IR/Attribute.lean`,
`Parser/AttrParser.lean`), the rewrite patterns and their proofs
(`Passes/Felt/{Combine,Matching,Proofs}.lean`), the semantic model
(`Data/Felt/Basic.lean`), the pass registration (`VeirOpt.lean`), the
FileCheck/differential tests (`Test/LLZK/Felt/*`), and the differential
normalizer (`scripts/llzk-diff.sh`).

Method: six parallel adversarial read sweeps, each tasked to *break* the
code; the reviewer then re-verified each sharp finding directly against
source (and against LLZK's C++). The Felt source is byte-identical between
the built dependency pin (`09d5f00f0`) and local `HEAD` (`7040fadcd`), so
no separate VEIR build was needed. The design docs deleted in the
"polish fork" commit (`5ed914831`) were recovered from git history and used
as the authors' own claims to test.

**Verification legend:** ✅ verified by reviewer against source · 🟡
agent-reported, high-confidence, not independently re-derived · ⚠️ requires
empirical check (build `llzk-opt`) to fully settle.

---

## 2. Faithfulness & coverage at a glance

**Op coverage** (LLZK defines 18 felt ops, all with `fold()`):

| VEIR status | ops | count |
|---|---|---|
| Fully wired (propertiesOf / matcher / pattern / proof) | `const`, `add`, `sub`, `mul`, `neg` | 5 |
| **Declared opcode only — no properties, no matcher, no proof, not in interpreter** | `pow`, `div`, `uintdiv`, `sintdiv`, `umod`, `smod`, `inv`, `bit_and`, `bit_or`, `bit_xor`, `bit_not`, `shl`, `shr` | **13** |

The semantic model (`Data/Felt/Basic.lean`) defines only `add/sub/mul/neg/
const` over `ZMod p`. The 13 missing ops **cannot even be stated** in the
model (no `inv`/`div`/`pow`/`mod`/bit/shift functions; no primality, no
bit-width). The ops where field/prime semantics are load-bearing are
exactly the unported ones.

**Faithfulness vs LLZK** (the 5 wired ops):

| Aspect | LLZK | VEIR | Divergence |
|---|---|---|---|
| Constant value rep | `APInt`, raw (round-trips `-1` as `-1`; **not** reduced on parse/print — verified via `llzk-opt`) | `Int`, raw | both keep raw values; VEIR's internal `DecidableEq`/`Hashable` still distinguish `0`/`p` (VH3) |
| Binary fold guard | both consts must share a **registered** field name | **no field-name guard**; folds unconditionally | VEIR folds where LLZK no-ops (VC3) |
| Cross-field operands | rejected (types must unify) | **accepted**; one operand's field silently chosen | ill-typed-vs-LLZK result (VC3) |
| Modular reduction | applied in **folds** (`field->reduce`), not on raw consts | **not** applied in folds | fold-result divergence (VH3) — *unreached today; see VH2* |
| `NotFieldNative` gating | enforced (`allow_non_native_field_ops`) | **not modeled at all** | — (only affects the unported ops) |

---

## 3. Findings catalog

### Critical

**VC1 — 13 of 18 felt ops are semantics-free `Unit` stubs.** ✅
`Dialects/LLZK/Felt/OpInfo.lean:13-16` (`Felt.propertiesOf | .const => FeltConstProperties | _ => Unit`)
and `GlobalOpInfo.lean` route every non-`const` felt op to trivial
properties. No matcher, pattern, proof, or interpreter case exists for the
13. `Data/Felt/Basic.lean` defines no `div/inv/pow/mod/bit/shift`. A "Felt
dialect port" that omits all field-specific operations should say so
plainly; today the 18-constructor enum reads as full coverage.

**VC2 — the 15 rewrite preconditions are all `sorry`'d, with
`warn.sorry false` suppressing the signal.** ✅ (axiom-audited)
Every pattern in `Combine.lean` passes `sorry` for the rewriter
well-formedness obligations; `Veir.FeltPass.Combine` (the executable pass)
transitively depends on `sorryAx`, while the paired theorems in
`Proofs.lean` are axiom-clean. The theorems prove ring identities in
isolation; they are **not mechanically linked** to the IR mutation. This is
the *origin* of the assurance gap documented downstream in
`llzk-lean/docs/REVIEW.md` §3. (The structural half is dischargeable — see
that doc's spike — but is not done here.)

**VC3 — cross-field constant folds are unsound vs LLZK and unmodelled by
the proofs.** ✅ (`Combine.lean:57-72,167-178,182-193,104-125,288-306`)
`constant_fold_{add,sub,mul}` and `assoc_const_fold_{add,mul}` build the
result const's `fieldType` from **one** operand (`cstL.value.fieldType`, or
the *inner* const for the assoc variants) and never check both consts share
a field. VEIR's verifier (`Verifier.lean`) checks only operand/result
*counts*, not type unification, so VEIR accepts `felt.add (const c1 :
fieldA) (const c2 : fieldB)` and folds it — silently discarding one field.
LLZK folds only when both consts share a registered field name. The
soundness theorems quantify over a **single** `p`, so they do not witness
the mismatched-field case at all. The correct idiom already exists in the
same file (`self_subtraction_to_zero` derives the field from the result
*type*); the const-fold patterns should additionally require
`cstL.fieldType == cstR.fieldType`.

### High

**VH1 — named-field parser parity: RESOLVED on empirical verification — the
fix works; only cosmetic/edge residue remains.** ✅ (verified against the
prebuilt `llzk-opt` in the nix store + a freshly-built `veir-opt`)
This finding was **downgraded after empirical test**, correcting two
over-claims from the fan-out sweeps (which misread LLZK's behavior). Ground
truth from real `llzk-opt --mlir-print-op-generic` (the form the differential
compares):
- unnamed: `#felt<const 42> : !felt.type`
- named:   `#felt<const 5 : <"bn254">> : !felt.type<"bn254">` (inner annotation
  printed in **stripped** form `: <"bn254">`, plus an outer `: !felt.type<…>`)

Feeding LLZK's *exact* output to `veir-opt`: VEIR **parses both** without
error. So commit `ab77c1c57` genuinely closes the gap for the generic forms
the differential uses. Residual issues, all minor:
- VEIR's *printer* omits the redundant inner annotation
  (`#felt<const 5> : !felt.type<"bn254">`), so VEIR-print ≠ LLZK-print
  textually — but **no information is lost** (the field survives in the outer
  `!felt.type<"bn254">` on both sides); the normalizer reconciles it.
  *(Low — printer could echo the inner form to reduce reliance on the
  normalizer.)*
- VEIR rejects LLZK's **v1-compat** input form `#felt<const 5 <"bn254">>`
  (no colon). But `llzk-opt` never *emits* v1 — it's a legacy hand-input
  syntax — so this is off the differential path. *(Low.)*

**Consequence for the docs:** the "parser incompatibility" caveat in
`llzk-lean/docs/strategy-a-oracle.md` §"Known alignment caveats" #3 and the
`expected-divergence/named_field_const.mlir` corpus entry are now **stale/
overstated** — named-field consts are *not* mutually unparseable. Recommend
re-testing that corpus entry; it likely now agrees (modulo the cosmetic
inner-annotation normalization).

**VH2 — the differential oracle is shallow for Felt: it never runs
`felt-combine` or any felt arithmetic.** 🟡 (script-read)
`scripts/llzk-diff.sh` runs `veir-opt` with **no `-p` flag** (parse/print
only); the sole felt differential input is two module-level `felt.const`s
(its own comment: "we only exercise felt.const at module level"). So no felt
*rewrite* and no felt *arithmetic* (add/mul/fold) is ever cross-checked
against `llzk-opt` — "parity" rests on VEIR self-consistency plus the narrow
const round-trip. This is the real coverage gap: the 15 rewrites and the
unreduced-fold divergence (VH3) are never differentially exercised.

> **Correction (verified):** an earlier sweep claimed the normalizer
> (`llzk-diff.sh:209`) *masks a field divergence* by stripping the
> FeltConstAttr inner field name on both sides. Empirically this is **not**
> so: `llzk-opt` prints `#felt<const 5 : <"bn254">> : !felt.type<"bn254">`,
> the normalizer strips only the *redundant inner* `: <"bn254">`, and the
> **outer** `!felt.type<"bn254">` survives on both sides and carries the
> field. So `babybear` vs `bn254` do **not** collapse; the normalizer's
> "outer annotation carries the field" comment is correct. The
> normalizer-masking concern is **retracted.** (The only thing normalized
> away is a cosmetic VEIR↔LLZK printer-style difference — see VH1.)

**VH3 — VEIR's folds don't reduce mod p; internal `DecidableEq` distinguishes
equal field elements.** ✅ (refined after `llzk-opt` test)
`FeltConstAttr.value : Int` (`Attribute.lean:194`), never reduced. Two
distinct effects, separated after empirical check:
- **Raw const round-trip does NOT diverge:** `llzk-opt` itself round-trips an
  unreduced/negative const verbatim (verified: `-1` prints as `-1`, not
  `p-1`). So for *non-folded* constants VEIR and LLZK agree — no print
  divergence here.
- **Fold results DO diverge:** LLZK's `fold()` applies `field->reduce`;
  VEIR's constant-fold patterns compute on raw `Int` with no reduction. So a
  fold that overflows the field (e.g. `babybear` `const (p-1) + const 1`)
  yields `#felt<const p>` in VEIR vs `#felt<const 0>` in LLZK. Sound under
  eventual mod-p interpretation (the `Int→ZMod p` coercion is a ring hom),
  but a textual divergence — and one the differential never reaches today
  (VH2).
- **Internal representation:** derived `DecidableEq`/`Hashable` distinguish
  `0`/`p` and `-1`/`p-1`, so attributes denoting the same field element are
  unequal — would defeat CSE/dedup keyed on the attribute. (Independent of
  the print question.)

### Medium

**VM1 — ~15 dangling references to deleted design docs.** ✅
The "polish fork" commit deleted `harness/coverage.md`, `porting-notes.md`,
`FELT_PARITY_ASSESSMENT_2026-05-28.md`, `quality-gates.md`, etc., but live
source still cites them — including `Combine.lean:38` and `Proofs.lean:9`,
which point at the deleted `harness/coverage.md` as the *justification* for
the `sorry`-discharge policy (now unverifiable), plus `Attribute.lean:187-188`,
the `Bool/Function/Global` properties files, and the diff/quality-gate
scripts. Comprehension-erosion risk; recoverable only from git history.

**VM2 — CI "quality gate" is partly vacuous.** 🟡
`scripts/check-llzk-quality-gates.sh` (run on every push/PR) has gates that
`grep` deleted files (`harness/coverage.md`, `plan.md`); those gates
silently no-op (errors suppressed) yet the step prints PASS. Green CI for
checks that verify nothing.

**VM3 — `add_const_swap` theorem ignores its termination guard; no `mul`
counterpart.** 🟡
The pattern fires only when lhs is const and rhs is not (a guard that
exists to prevent fixpoint oscillation), but its theorem proves
*unconditional* commutativity — so the proof doesn't justify the guard, and
termination/confluence is unmodelled. There is no analogous swap for `mul`,
so `mul (const) x` identities never fire (missed, not unsound).

**VM4 — `FeltConstProperties.fromAttrDict` does no value/field validation.** 🟡
Accepts any `FeltConstAttr` including unreduced/negative/huge values and
never checks the const's field against a surrounding result type
(`Felt/Properties.lean:24-32`). Compounds VC3/VH3 for programmatically-built
IR.

**VM5 — degenerate model cases; primality never threaded.** 🟡
`Felt p := ZMod p` for arbitrary `Nat p` includes `p=0` (≅ ℤ) and `p=1`
(trivial ring); theorems quantify over all `p` with no `Fact p.Prime`,
though docstrings invoke "field". Sound but the generality is partly
vacuous, and at `p=1` the patterns' raw-`Int` guards (`value ≠ 1`) diverge
from field semantics.

### Low

- **VL1** duplicate pass registration (`VeirOpt.lean:30-31`, `CastReconcilePass`
  inserted twice; benign). 🟡
- **VL2** field-name escape: printer/parser escape tables not provably
  inverse for arbitrary control-byte field names (low real exposure). 🟡
- **VL3** telescoping guards use raw `Int` equality instead of field
  equality — fails *safe* (incompleteness, not unsoundness) but is the wrong
  predicate. ✅

---

## 4. Checked and found genuinely OK

- The 15 ring identities in `Proofs.lean` are **mathematically correct** and
  axiom-clean; each models the *arithmetic* its pattern computes (no theorem
  proves a different identity). ✅
- `right_identity_zero_add` is correctly one-sided (pattern *and* theorem) —
  no commutativity drift on the VEIR side (the drift is in the llzk-lean
  cert, not here). ✅
- `matchOp` arity is precise (exact operand count **and** `getNumResults!=1`),
  so patterns can't over-match. ✅
- The greedy rewriter **terminates** on these 15 patterns (a lexicographic
  measure strictly decreases; no oscillation constructible). ✅
- `felt-combine` **is** genuinely registered and runnable via
  `veir-opt -p felt-combine`; `Felt/Proofs.lean` **is** on the default build
  path (not an orphan, unlike `Combines/Proofs.lean` and
  `InstructionSelection/Proofs.lean`). 🟡
- 12 of 16 felt FileCheck pass/pipeline tests assert **real** rewrite
  results (`CHECK-NOT`/`CHECK-NEXT` guards), incl. a named-field
  self-subtraction and `felt-combine,dce` composition; the 4 non-rewrite
  tests are honestly labelled. 🟡
- `const` is fully wired (non-trivial properties, attr-dict round-trip,
  matcher); the zero-synthesizing patterns correctly derive the synthesized
  const's field from the result *type*. ✅

---

## 5. Verdict & recommended sequencing

The VEIR Felt port is a **correct-but-narrow proof core wrapped in
dialect plumbing of uneven fidelity.** The algebra is sound; the breadth and
the LLZK-faithfulness are overstated. Priorities:

1. **Re-frame coverage honestly** (VC1): state that 5 of 18 ops are
   implemented and the field-specific ops are out of scope.
2. **Fix the cross-field fold unsoundness** (VC3) — add the
   `fieldType` equality guard; adopt the result-type-derived idiom.
3. **Make the differential mean something** (VH2) — run `-p felt-combine`,
   add felt-arithmetic inputs; this is what would actually catch VC3/VH3.
   (Parser parity VH1 is already empirically resolved; just (a) optionally
   have VEIR's printer echo the inner annotation to avoid relying on the
   normalizer, and (b) correct the now-stale parser-incompatibility caveat in
   `llzk-lean/docs/strategy-a-oracle.md` and re-test the `named_field_const`
   corpus entry.)
4. **Discharge the preconditions** (VC2) via `WfRewriter` (tractable — see
   the llzk-lean spike) and link theorem ↔ transformation.
5. **Repair comprehension rot** (VM1/VM2): restore or re-point the deleted
   design docs the live source and CI depend on.

Items 1, 2, 5 are cheap and high-value; 3–4 are the substantive faithfulness
work. None require restarting the port.

> **Methodology note.** Findings were produced by adversarial fan-out then
> re-verified by the reviewer. Two High claims (VH1 "parser rejects LLZK
> output"; the VH2 "normalizer masks field divergence" sub-claim) were
> **over-claims corrected on empirical test** against the prebuilt `llzk-opt`
> (nix store) and a freshly-built `veir-opt`. Net: the parser fix works; the
> live High/Critical findings are VC1 (op coverage), VC2 (sorry'd
> preconditions), VC3 (cross-field fold unsoundness), VH2 (shallow
> differential), VH3 (unreduced folds).
