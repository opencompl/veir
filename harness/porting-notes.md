# Durable porting notes

Append-only log of lessons that apply across dialect ports. Seeded
from `LLZK_PORT_RETRO.md` (the Felt-specific retrospective); add to it
in the same commit that discovers a new gotcha.

Format: each note has a date, a short title, the discovery, and a
"how to apply" paragraph. Notes are sorted by date, newest at the top.

---

## 2026-05-20 — Pattern: `show <ZMod-equality>` then `simp` / `push_cast; ring`

**Discovery (E.5 Tier 1+2 — 11 new Felt rewrites)**: Once the Felt
semantic model is `abbrev Felt (p : Nat) := ZMod p`, every Felt-rewrite
soundness proof has the same three-line shape:

```lean
theorem name (p : Nat) (x : Felt p) (c : Int) :
    <lhs in Felt-API> = <rhs in Felt-API> := by
  show <same equation expanded to ZMod p with Int casts on constants>
  simp        -- when no constant arithmetic is involved
  -- OR
  push_cast   -- pull Int casts to the outside
  ring        -- normalize over the commutative ring ZMod p
```

The `show` line is load-bearing: `Felt p` is an `abbrev` for `ZMod p`,
but the proof obligations use the wrapped Felt API (`add`, `mul`,
`const p c`). `show` strips the API layer back to `+`, `*`, and
`((c : Int) : ZMod p)` so Mathlib's `simp`-set or `ring` can apply.
Without it, both tactics get stuck trying to unfold `add`/`const`.

When the identity involves no integer constants (`x + (-x) = 0`,
`x * 0 = 0`), `simp` alone closes it. When constants are involved
and Mathlib's coercion lemmas need to commute past arithmetic,
`push_cast; ring` is the two-tactic close.

**How to apply**: For every new Felt rewrite added to `Combine.lean`,
the soundness proof in `Proofs.lean` is mechanical — the `show` line
is the only piece that requires thought. Don't try to be clever
with `change` or manual `unfold`; the `show` form is more concise
and more readable.

**Re-evaluate when**: passes start needing `[Fact (p.Prime)]`
(multiplicative inverses, Tier 3). At that point the proof shape
extends with `haveI : Fact (p.Prime) := ⟨...⟩` and the closing
tactic may need a different cast lemma.

---

## 2026-05-20 — Pattern: greedy rewriter composes small canonicalizers

**Discovery (E.5 Tier 1)**: `add_const_swap` rewrites
`add (const c) x → add x (const c)` — a no-op semantically, useful
only as a *canonicalizer* that puts constants on the right. The
payoff is composition: every other right-form rewrite
(`right_identity_zero_add`, `add_sub_const_cancel`,
`assoc_const_fold_add`, …) now fires regardless of whether the
input had the constant on the left or the right. We don't have to
write left-and-right variants of every rewrite.

The greedy rewriter (`RewritePattern.applyInContext`) iterates to
fixpoint, walking the IR and applying any matching pattern. After
`add_const_swap` produces a swapped op, the next iteration sees
`add x (const c)` and fires the right-form rewrites — without
needing an explicit pipeline order. Two guards keep this from
oscillating:

1. `add_const_swap` requires the *left* operand to be a constant
   AND the right not to be (otherwise `constant_fold_add` handles
   the const-const case).
2. After swapping, the new op has a non-constant on the left, so
   `add_const_swap` no longer matches.

The lit test `add_const_canonicalize.mlir` exercises the
composition directly: input has `add (const 0) x`, expected output
is `x` (canonicalize then right-identity in one greedy fixpoint).

**How to apply**: For commutative binary ops with right-form
patterns, add a single `_const_swap` canonicalizer and skip the
left-form variants of every other pattern. Always guard the swap
against the const-const case (let the dedicated constant-folder
catch it) and confirm the swap rewrites toward a strictly-less
matchable form so the rewriter doesn't loop.

**Re-evaluate when**: porting a non-commutative dialect (e.g., a
matrix op where left/right multiplication differ), or when
introducing a rewrite that *could* re-produce the canonicalizer's
input shape — at that point the no-oscillation argument needs to
be checked explicitly.

---

## 2026-05-19 — Pattern: adopting Mathlib means pinning to Mathlib's Lean

**Discovery (E.5 — Felt := ZMod p upgrade)**: Adding Mathlib as a
`require` in `lakefile.toml` worked, and `lake exe cache get`
fetched ~8.4k precompiled oleans in a minute. But the oleans are
ABI-tied to the *exact* Lean version Mathlib was built against — in
our case `v4.30.0-rc2`. We were on `nightly-2026-05-14`, ~1 month
ahead, and trying to `import Mathlib.Data.ZMod.Basic` produced an
`incompatible header` error on every olean.

Mathlib doesn't track Lean nightlies — only stable releases and
release candidates. There's no Mathlib branch that pairs with any
given Lean nightly, so the practical choice is: **align the
project's `lean-toolchain` to whatever Mathlib master uses** and
rebuild everything. We downgraded to `v4.30.0-rc2`. One file
(`Veir/Rewriter/GetSet/Operands.lean`) hit a `grind` heartbeat
timeout under the older compiler and needed `set_option
maxHeartbeats 400000 in`; nothing else regressed.

A second pitfall: Mathlib defines theorems that VEIR also defined
in `Veir/ForLean.lean` (e.g. `List.getElem?_idxOf`). When both end
up in scope, Lean refuses to import: `environment already contains
'List.getElem?_idxOf'`. The fix is to rename VEIR's local copies
out of the way (e.g. `List.Veir.getElem?_idxOf`) — anything Mathlib
duplicates is by definition standard and can be relied on
elsewhere.

**How to apply**: Before any future Mathlib-dependent work,
re-check that the project's `lean-toolchain` still matches Mathlib
master's `lean-toolchain`. If they've drifted, do the toolchain
bump as a *separate* commit (with a build-only verification) before
landing new proof content — that way regressions from the
toolchain swap are isolated from regressions in the new code.

**Upstream-fix candidate**: a script in `scripts/` that diffs our
`lean-toolchain` against `.lake/packages/mathlib/lean-toolchain` and
warns when they diverge.

---

## 2026-05-19 — Pattern: modulus-in-proof vs modulus-in-type for finite fields

**Discovery (E.5)**: VEIR has two LLZK-adjacent dialects that
represent finite-field values: HEIR's `mod_arith` and LLZK's `felt`.
They make opposite design choices:

- `mod_arith` bakes the modulus into the *type*:
  `ModArithType { modulus : Int; modulusType : Option IntegerType }`.
  Each value is statically tagged. No semantic model exists in
  `Veir/Data/`; no verified rewrites run on it.
- `felt` leaves the modulus *implicit* at the type level
  (`!felt.type` with optional field-name annotation). Verified
  rewrites must therefore quantify universally over the modulus to
  be sound across `bn254`, `bls12-377`, etc.

The Felt semantic model upgraded to `abbrev Felt (p : Nat) := ZMod p`,
and the 4 existing verified rewrites take `(p : Nat)` as an extra
parameter. Mathlib's `CommRing (ZMod p)` discharges the identities
without needing `[Fact p.Prime]` — primality only becomes
load-bearing once division enters the picture.

**How to apply**: When porting another field-flavored dialect to
VEIR, ask first: does the dialect pin the modulus statically (like
`mod_arith`) or leave it implicit (like `felt`)? The answer
determines whether the semantic model takes a `Nat` parameter or
hard-codes a specific field. If implicit, the proofs must
universally quantify; if pinned, they can specialize. Don't try to
build one model that does both.

---

## 2026-05-18 — Gotcha 7: LLZK `function.def` requires `function_type` even when empty

**Discovery (F.5)**: A naïve port of `function.def` that stored only
`sym_name` round-tripped through `veir-opt` but `llzk-opt` rejected
it with a parser error. LLZK's TableGen declares
`TypeAttrOf<FunctionType>:$function_type` as a *required* property
(not `OptionalAttr`), and the C++ verifier asserts it. Even for an
empty body with `() -> ()` signature the attribute must appear in
the `<{...}>` properties dictionary — LLZK won't synthesize a
default. VEIR's `FunctionDefProperties.fromAttrDict` now mirrors
that requirement: missing `function_type` is a hard error at parse
time.

**How to apply**: When porting any `FunctionOpInterface`-like op
from LLZK, copy the full TableGen property list — including ones
that look "obvious" or "internal" (the function signature lives in
the type-signature line in custom assembly but is a separate
property in generic form). Test against `llzk-opt` early; relying
solely on the VEIR round-trip will let a parsable-but-LLZK-rejected
form slip through.

**Upstream-fix candidate**: a coverage-row sweep that lists *all*
required properties for each ported op (not just the ones VEIR
encodes) would catch this class of gap earlier.

---

## 2026-05-18 — Pattern: LLZK `function.allow_*` markers are discardable attrs

**Discovery (F.5)**: LLZK gates non-native-field ops, constraint
ops, and witness ops by requiring the surrounding `function.def` to
carry one of `function.allow_non_native_field_ops`,
`function.allow_constraint`, `function.allow_witness`. These are
*discardable* dialect attributes — they live in the trailing `{...}`
attribute dictionary after the op's regions, not inside its
properties `<{...}>`. Example:

```
"function.def"() <{sym_name = "f", function_type = () -> ()}> ({
  ...
}) {function.allow_non_native_field_ops} : () -> ()
```

VEIR's generic parser already accepts them as `UnregisteredAttr`
entries on the op's discardable-attr dict and round-trips them
unmodified. No structured port needed for the differential to lift —
the C++ verifier only checks presence by name. (A future structured
port would let VEIR verify the gate too; today we trust LLZK.)

**How to apply**: When lifting an XFAIL differential that requires a
`function.def` wrapper, just add the right `function.allow_*`
discardable attr to the function. No new property field, no new
attribute case — the round-trip works as-is. Record the gate in the
coverage row for the dialect (Bool ↔ non-native-field, Constrain ↔
constraint, Global write ↔ witness).

---

## 2026-05-02 — VEIR dialect surface is closed-world

**Discovery (Felt port)**: VEIR's dialect surface is centralized through
a single closed `Attribute` inductive plus a per-dialect property
record system. Each new dialect type is a new case on the inductive;
each property-bearing op gets a record in `Veir/Properties.lean` and an
entry in a `Veir/Dialects/<X>/OpInfo.lean` file.

**How to apply**: When porting a dialect, expect to touch exactly seven
files (the recipe is in `harness/dialect-port-checklist.md`). The
verified IR data structure (`Veir/IR/Fields.lean`, `GetSet.lean`,
`WellFormed.lean`) is **untouched** by a dialect addition — attributes
are truly opaque payloads to the verified core. This is excellent news
for porting: those 9.4K LoC of proofs never need re-doing for a
dialect addition.

`Veir/Printer.lean` is also untouched. Printing goes through generic
MLIR format and relies on `Attribute.toString`; as long as a `ToString`
instance for new types exists, printing is automatic.

---

## 2026-05-17 — Lesson: empirical survey before architectural assumptions

**Discovery (Phase F design note, F.1)**: The original Phase F
estimate ("3-6 weeks, major architectural addition") assumed VEIR
had *no* region support and Phase F would add the structural
foundation from scratch. The F.1 research survey
(`tasks/a862be48f77f98bb9.output`) revealed:

- `Operation.regions : Array RegionPtr` is already a field of every
  Operation.
- `Region` and `Block` structures are defined in `Veir/IR/Basic.lean`.
- FieldsInBounds + WellFormed proofs cover all three for structural
  invariants (`region_parent` bijection, blocks-belong-to-regions,
  etc.).
- 8 files under `Veir/Rewriter/WellFormed/` already include
  `Region.lean`, `OpRegion.lean`, `Block.lean`, `BlockArguments.lean`,
  `BlockOperands.lean` — meaning even some rewriter primitives
  (`Rewriter.initOpRegions`, `Rewriter.pushRegion`) are already
  WellFormed-preserving.

Revised estimate: 2-4 weeks. The remaining work is semantic
invariants (terminator presence, IsolatedFromAbove), block-args-as-
SSA-values, symbol-table machinery, and one prototype dialect
(Function), not the full structural addition.

**How to apply**: before estimating any architectural addition, run a
focused survey of the existing codebase. The survey can spawn a
read-only Agent in parallel with drafting the design framing — both
finish faster than sequential. The Agent's specific job:

1. Read the relevant module headers + grep for hints of pre-existing
   support.
2. Count LoC under the target subtrees as a proxy for the surface
   that would need to change.
3. Identify "structurally there but semantically empty" patterns —
   features whose data structures exist but lack consumer dialects
   or invariants.

VEIR's pattern specifically: many features are structurally
prepared but semantically incomplete. Don't assume "VEIR can't do X"
without empirical confirmation; check whether the data structures
for X are already in `Veir/IR/Basic.lean`.

The F.1 design note (`harness/regions-design.md`) is the worked
example.

---

## 2026-05-17 — Pattern: round-trip is a port-quality bar

**Discovery (FeltConstAttr post-audit, Real Issue #2)**: When adding a
new structured attribute (or any new IR element with both parser and
printer), the *parse ∘ print = id* invariant is a non-negotiable
correctness bar. My `parseOptionalFeltConstAttr` originally passed
`allowNegative := false` to `parseOptionalInteger`, but the printer
emitted negative integers verbatim. Result: any value < 0 round-tripped
through `print` then `parse` failed with "expected an integer value".

**How to apply**: every new parser/printer pair gets at least one
explicit round-trip lit test exercising the corner cases of the value
space:
- For numeric payloads: negative, zero, large (bigger than `i64`).
- For optional fields: present and absent.
- For string payloads: empty, with embedded quotes, with escape chars.
- For nested structures: each variant of the inner type.

A one-line regression test (`Test/LLZK/<dialect>/passes/<edge>_roundtrip.mlir`)
catches the bug class. See
`Test/LLZK/Felt/passes/negative_const_roundtrip.mlir` for the
prototype.

---

## 2026-05-17 — Pattern: result-type / attribute-type consistency in synthesized ops

**Discovery (FeltConstAttr post-audit, Real Issue #3)**:
`self_subtraction_to_zero` originally hard-coded
`fieldType := { fieldName := none }` for the synthesized `felt.const`,
producing this kind of mismatch on bn254-typed input:
```mlir
"felt.const"() <{value = #felt<const 0> : !felt.type}> : () -> !felt.type<"bn254">
                                       ^^^^^^^^^^^^               ^^^^^^^^^^^^^^^^^^^
                                       attribute fieldType        result type
```
LLZK's verifier rejects this. The test corpus didn't include a
bn254-typed `felt.sub`, so the bug wasn't caught locally — it would
have shipped silently until somebody fed bn254 LLZK IR through VEIR.

**How to apply**: when a pattern synthesizes an op whose result type
is taken from an operand's existing type (e.g.
`resultType := lhs.getType! ctx`), and the new op's properties carry
a *structured* type-bearing attribute (`FeltConstAttr.fieldType`,
future `BoolCmpAttr`-with-typed-predicate, struct member attrs):

1. **Extract the structured type's components from the actual
   resultType**, not from defaults. Pattern:
   ```lean
   let resultType := lhs.getType! rewriter.ctx.raw
   let Attribute.feltType ft := resultType.val | return rewriter
   let cstProp : FeltConstProperties :=
     { value := { value := 0, fieldType := ft } }
   ```
2. **Add a regression test on a named-field variant** of the type
   (`!felt.type<"bn254">`, `!struct.type<@Foo<[...]>>`, etc.) for any
   pattern that synthesizes a typed structured attribute.

This is a generalization of the "preserve fieldType" thinking already
in `constant_fold_add` and `assoc_const_fold_add` (which preserve via
`cstL.value.fieldType` from a matched const), now extended to
synthesizing-from-defaults cases.

---

## 2026-05-17 — Procedure: differential XFAIL → PASS transitions

**Discovery (FeltConstAttr post-audit, Real Issue #4)**: When the
Felt differential test was un-XFAIL'd, the directive in the test file
was updated but `harness/coverage.md`'s summary count
(`322 PASS + 5 XFAIL`) and the explanation clause ("or the structured
`#felt.const<v>` attribute") stayed at the pre-fix state. Both went
stale in the same commit that fixed the underlying issue.

**How to apply**: when moving a differential test from `// XFAIL` to
`// REQUIRES`, update all three sites *in the same commit*:

1. The directive: `// XFAIL: llzk-opt` → `// REQUIRES: llzk-opt`.
2. The header comment explaining why the test exists.
3. The summary in `harness/coverage.md`'s §Tests row: the
   `N PASS + M XFAIL` count *and* any prose listing the gating
   reasons (e.g. "5 XFAIL gated on Phase G.1" — the count and the
   prose must agree).

The `harness/quality-gates.md` §3 lit-count consistency gate would
ideally catch this; the current script only catches numeric drift,
not prose drift. Manual discipline required.

---

## 2026-05-17 — Pattern: per-dialect structured attributes

**Discovery (post-Felt-differential triage)**: VEIR's first per-dialect
structured attribute, `FeltConstAttr` (printed as `#felt<const N> :
!felt.type`). The parser pattern generalizes to any LLZK structured
attribute of the form `#dialect<body> [: type-annotation]`.

Recipe (mirror `Veir/IR/Attribute.lean` for `FeltConstAttr` and
`Veir/Parser/AttrParser.lean` for `parseOptionalFeltConstAttr`):

1. **Add the structure**:
   ```lean
   structure XxxAttr where
     value : <T>      -- whatever the body parses to
     -- optional fields for any colon-suffix type annotation
     -- (e.g. fieldType : SomeType)
   deriving Inhabited, Repr, DecidableEq, Hashable
   ```

2. **Add the `Attribute` case** + `decEq` arm + `ToString` instance +
   `Coe` instance + `isType` arm (usually `false` for attributes).

3. **Add the parser**, **placed AFTER any type parsers it depends on**:
   ```lean
   def parseOptionalXxxAttr : AttrParserM (Option XxxAttr) := do
     let token ← peekToken
     let .hashIdent := token.kind | return none
     let input := (← getThe ParserState).input
     let name := { token.slice with start := token.slice.start + 1 }.of input
     if name ≠ "<dialect-mnemonic>".toByteArray then return none
     let _ ← consumeToken
     parsePunctuation "<"
     -- parse body — typically a keyword + values
     if !(← parseOptionalKeyword "<body-keyword>".toByteArray) then
       throw "#<dialect>: body must begin with `<body-keyword>`"
     let some val ← parseOptionalInteger false false
       | throw "expected integer"
     parsePunctuation ">"
     -- optional colon-type-annotation
     parsePunctuation ":"
     let some ftAttr ← parseOptionalXxxType
       | throw "expected `: !<dialect>.type` annotation"
     let Attribute.xxxType ft := ftAttr.val
       | throw "annotation must be !<dialect>.type"
     return some (XxxAttr.mk val ft)
   ```

4. **Slot into `parseOptionalAttribute`** **before** `parseOptionalDialectAttr`
   (which is the fallthrough to `UnregisteredAttr`).

**Two gotchas** discovered while building `FeltConstAttr`:

a) **Dialect mnemonic vs body keyword**. LLZK's printed form is
   `#felt<const 42>`, not `#felt.const<42>`. The dialect mnemonic in
   attribute syntax is just `felt`; `const` is a *keyword in the body*.
   This means one `#felt` parser can dispatch to multiple attribute
   variants by body keyword (`#felt<const N>`, `#felt<spec name>`,
   etc.). Don't assume the attribute name is `#<dialect>.<attr>`;
   look at LLZK's actual generic-form output via
   `llzk-opt --mlir-print-op-generic`.

b) **Type-annotation suffix is often required**. `#felt<const 42>` is
   incomplete in LLZK; the full form is `#felt<const 42> : !felt.type`.
   The type annotation parametrizes the attribute (e.g., which finite
   field the constant lives in). Store it in the `XxxAttr` structure
   alongside the value.

**Use this pattern**: Phase D.4's Bool.cmp predicate stays on
IntegerAttr for now (simpler), but if the next maintainer wants
LLZK-exact textual round-trip for Bool, the recipe applies. Same
for any future Polymorphic/Struct attribute that's structured.

---

## 2026-05-17 — Gotcha 5: `SymbolNameAttr` is `StringAttr`, not `SymbolRefAttr`

**Discovery (Include + Global differential tests, post-llzk-opt-build)**:
I had ported `include.from`'s `sym_name` and `global.def`'s `sym_name`
as `FlatSymbolRefAttr` (`@name`). LLZK rejects these — it expects
`StringAttr` (`"name"`).

In MLIR ODS, `SymbolNameAttr` is **defined as a `StringAttr` constraint**
on the *producer* side of a symbol. The `@`-prefixed `FlatSymbolRefAttr`
is for *users* of a symbol (`global.read`'s `name_ref`, `function.call`'s
`callee`, etc.). The visual similarity in some printers' output led me
astray — Gotcha 3 (2026-05-15) made the wrong assumption.

**How to apply**: when porting any op with the `Symbol` trait:
- The op's `sym_name` (or equivalent) is a `StringAttr`, parsed as `"name"`.
- Other ops that *reference* the symbol use `FlatSymbolRefAttr`, parsed as `@name`.
- Generic-form printing follows the underlying ODS type, not the trait.

**Affected ports retroactively fixed**: Include's `sym_name`, Global's
`sym_name`. Global's `name_ref` (on read/write) was correct as
`FlatSymbolRefAttr`. This re-narrows Gotcha 3 — `Symbol`-trait ops
need `@name` parsing for their *uses* elsewhere, not for their own
`sym_name` field.

**Cost of the discovery**: the differential test against `llzk-opt` was
the forcing function. Without it, I'd have shipped both Include and
Global with subtly wrong attribute encoding. Score one for the
differential harness — exactly what it was designed to catch.

---

## 2026-05-17 — Gotcha 6: most LLZK ops require a `function.def` wrapper

**Discovery (Bool/Cast/Constrain/RAM/Global differential tests)**:
At module level, most LLZK ops are not legal. LLZK enforces this via
op verifiers that check `getParentOfType<FunctionDefOp>()` and reject
otherwise, sometimes additionally requiring the parent function to
carry a specific attribute:

| Op | Required parent attribute |
|---|---|
| `bool.and`/`or`/`xor`/`not`/`cmp` | `function.allow_non_native_field_ops` |
| `cast.toindex` | `function.allow_non_native_field_ops` |
| `constrain.eq`/`constrain.in` | `function.allow_constraint` |
| `global.write` | `function.allow_witness` |
| Most RAM/Felt arith ops in constraint contexts | varies |

VEIR doesn't enforce any of this — our verifier checks only
operand/result/region/successor counts, not parent-op kind. So
identity-test inputs that work in VEIR may fail to parse in LLZK,
and vice-versa.

**How to apply**:
- Until Function dialect ports (Phase G.1), differential testing of
  most LLZK ops is **structurally impossible** — they need a
  `function.def` wrapper that VEIR can't express.
- For ops that work at module level (`include.from`, `string.new`,
  `global.def`/`global.read` without write, top-level `arith.constant`),
  differential testing works today.
- Mark fully-Function-gated tests with `// XFAIL: llzk-opt` so lit
  reports them as expected-fail rather than failure. When Phase G.1
  lands and tests are rewritten to use `function.def`, flip back to
  plain `// REQUIRES: llzk-opt`.

**Catalog of differential-testable ops today**: `include.from`,
`string.new`, `global.def`+`global.read` (without `global.write`),
plus anything else exclusively at module level. Catalog grows when
Function lands.

---

## 2026-05-15 — Pattern: enum attributes via the IntegerAttr workaround

**Discovery (Phase D.4 — bool.cmp)**: LLZK uses `I32EnumAttr` for
enum-valued op attributes (`FeltCmpPredicate` with cases
`eq=0, ne=1, lt=2, le=3, gt=4, ge=5`). The custom assembly form is
`#bool<eq>`; the generic-form is `<{predicate = 0 : i32}>` (an
i32 `IntegerAttr` carrying the enum's underlying integer value).

VEIR has no per-dialect attribute parser for `#dialect<case>`, but
the generic form is already `IntegerAttr`. So the workaround:

```lean
-- In Veir/Dialects/LLZK/<Dialect>/Properties.lean:
structure XxxCmpProperties where
  predicate : IntegerAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def XxxCmpProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String XxxCmpProperties := do
  if attrDict.size > 1 then
    throw s!"xxx.cmp: expected only 'predicate' property"
  let some attr := attrDict["predicate".toUTF8]?
    | throw "xxx.cmp: missing 'predicate' property"
  let .integerAttr intAttr := attr
    | throw s!"xxx.cmp: predicate must be an integer attribute (enum workaround)"
  -- Range-check against the enum's case count.
  if intAttr.value < 0 ∨ intAttr.value > 5 then
    throw s!"xxx.cmp: 'predicate' out of range 0..5"
  return { predicate := intAttr }
```

**Two caveats to record in `harness/coverage.md`**:

1. **The printed form differs from LLZK** (`= 0 : i32` vs `= #bool<eq>`).
   IR-level value preserved; textual form is VEIR-flavored.
2. **No symbolic name in the IR.** Pattern matches against the
   predicate use the integer constant (e.g., `if pred.value = 0` for
   `eq`), not a symbolic case name.

**When to upgrade to a real per-dialect enum parser**: when a verified
pass needs to pattern-match symbolically (`match predicate with | .eq => ...`)
*and* the `Int.value`-based dispatch becomes awkward. For now, the
IntegerAttr workaround suffices for round-trip and verifier shape
checks.

**Use this pattern**: Bool.cmp ✓ (Phase D.4). Future candidates:
Comb predicates, any LLZK dialect with a fixed-set enum. Always
pair the workaround with a range check at `fromAttrDict` to catch
out-of-band values.

---

## 2026-05-15 — Pattern: pass namespace collides with dialect inductive name

**Discovery (Phase E.1 — first verified Felt pass)**: `inductive Felt`
lives at `Veir.Felt` (registered by `@[opcodes]` in `Veir/OpCode.lean`).
A peer pass module `namespace Veir.Felt` would shadow it, so every
`OpCode.felt _` dot-notation reference becomes ambiguous and elaboration
fails (`Unknown constant Veir.Felt.felt`).

Resolution: name pass namespaces with a distinct suffix —
`Veir.FeltPass`, `Veir.BoolPass`, `Veir.ConstrainPass`, etc. — and use
fully-qualified `OpCode.felt Felt.add` / `OpCode.felt Felt.const`
inside the matcher helpers, not the `.felt .add` shorthand. See
`Veir/Passes/Felt/{Matching,Combine}.lean` for the established pattern.

**Applies to**: any future pass on Bool, Constrain, Include, Global,
RAM, Cast — i.e. every dialect whose inductive shares its bare name
with the dialect's mnemonic (which is *all* of them in this fork's
naming scheme).

**Why not just use the dialect inductive's namespace** (e.g. add the
pass to `Veir.Felt`)? It works at the cost of fully-qualifying every
opcode reference. `Veir.<Dialect>Pass` keeps the dot-notation idiom
working without sacrificing clarity.

---

## 2026-05-15 — Pattern: provisional `Felt := Int` semantic model

**Discovery (Phase E.1)**: Building a verified peephole rewrite needs
*some* semantic model for the data. Felt's true semantics is `ZMod p`
for various `p`, but threading the modulus through proofs is
unnecessary for identities like `x + 0 = x` that hold under *any*
ring homomorphism.

Recipe (see `Veir/Data/Felt/Basic.lean`):

```lean
abbrev Felt := Int           -- `abbrev` inherits all Int instances
def const (n : Int) : Felt := n
def add (a b : Felt) : Felt := a + b
```

Pair with `Veir/Passes/<Dialect>/Proofs.lean`:

```lean
theorem right_identity_zero_add (lhs : Felt) :
    add lhs (const 0) = lhs := by simp [add, const]
```

**Lift argument**: any identity proved over `Int` that's of the form
*p(x) = q(x)* where both `p` and `q` are polynomial expressions in
the inputs and ring constants 0/1 lifts to any `ZMod p` model via the
canonical ring homomorphism `ℤ → ZMod p`. This covers `x + 0 = x`,
`x + (-x) = 0`, `x * 1 = x`, `x - x = 0`, etc. — exactly the kind of
peephole each pilot in `harness/verification-plan.md` targets.

**Doesn't lift**: anything that uses field-specific structure (inverse
of nonzero elements, ordering, divisibility, characteristic). Upgrade
to a real `ZMod p` model when a pass needs those.

**Use this pattern**: `Veir/Data/<Dialect>/Basic.lean` for any
dialect whose ops form a commutative ring or group. The `abbrev`
form (not `def`) is required so Lean's instance resolution finds
`Add`/`Mul`/etc. without explicit instances.

---

## 2026-05-15 — Gotcha: differential allowlist is fixed-string and unscoped

**Discovery (Phase A differential harness)**: `scripts/llzk-diff.sh`'s
allowlist applies fixed-string substitutions globally to each line of
both files before diffing. **Rules are not scoped to specific ops or
contexts.**

Concretely: a Felt rule
```
"<{value = 42 : i256}>" -> "<{value = #felt.const<42>}>"
```
would *also* rewrite any unrelated op with the same attribute
fragment (e.g. an `arith.constant` of value 42). Today's tests are
single-dialect so this is harmless; mixed-dialect tests would need
scoping.

**How to apply**: when writing an allowlist entry, **include enough
surrounding context to make the from-pattern unique to the op the
divergence applies to**. For Felt:
```
'%{{[^ ]+}} = "felt.const"() <{value = 42 : i256}>' -> '...'
```
(Note: the script does fixed-string match, not regex, so use the
literal `%5 = ...` form from a captured output, or use the normalizer
to stabilize the SSA names first — see the script's stage-3
normalization.)

Also: the allowlist grammar is `"from" -> "to"` (line-literal). Quote
characters inside `from`/`to` aren't escaped — the regex stops at the
first inner `"`. Document the limitation per rule, or avoid embedded
quotes by widening context.

---

## 2026-05-15 — Pattern: optional-attr property fields (`Option StringAttr`)

**Discovery (Phase A.5 — Bool.assert)**: The first ported op with an
*optional* attribute. The shape of `fromAttrDict`:

```lean
let msg ← match attrDict["msg".toUTF8]? with
  | some (.stringAttr m) => .ok (some m)
  | some attr => .error s!"... expected 'msg' to be a string attribute, got {attr}"
  | none => .ok none
-- If size = 1 but msg is none, the key isn't 'msg'. Reject.
if attrDict.size = 1 ∧ msg.isNone then
  throw "...: only 'msg' is a recognized property"
return { msg := msg }
```

**Why the `size = 1 ∧ isNone` check matters**: without it, an input like
`<{foo = "x"}>` (one entry, unknown key) silently coerces to `{ msg := none }`
instead of failing. The check makes the optional-field path as strict as the
required-field paths in other dialects. Discovered during Tier-1 review.

---

## 2026-05-15 — Pattern: property-less dialects skip the per-dialect OpInfo file

**Discovery (Phase A.3 Cast, A.4 RAM, A.6 Constrain)**: Three Tier-1 ports
where no op carries attributes. The empirical pattern that emerged:

1. **Do NOT** create `Veir/Dialects/LLZK/<Dialect>/{Properties,OpInfo}.lean`.
2. **Do NOT** add a `propertiesOf` arm in `GlobalOpInfo.lean` — the central
   wildcard `_ => Unit` handles it.
3. **Do** add a single arm in `Properties.fromAttrDict`:
   ```lean
   case <dialect> =>
     all_goals exact (Except.ok ())
   ```
4. **Do NOT** add an arm in `Properties.toAttrDict` — the central
   `| _ => Std.HashMap.emptyWithCapacity 0` wildcard handles it.

That's a 3-file shortcut. Saves clutter; doesn't impair anything.

This is the right behavior for Cast (no attrs), RAM (no attrs),
Constrain.eq (no attrs), and Datapath (an existing dialect that already
uses this pattern). Captured in `harness/dialect-port-checklist.md`
Phase 3.A.

---

## 2026-05-15 — Pattern: `«keyword»` escaping for Lean-keyword constructor names

**Discovery (Phase A.1 Include)**: Op constructor names that collide
with Lean keywords (`from`, `in`, ...) are accepted in the inductive
declaration but need escaping at *use* sites:

| Position | Escape required? | Example |
|---|---|---|
| Inductive ctor declaration | No | `inductive Include_ where \| from` |
| Term-mode `match` pattern (`\| .x.y`) | No | `\| .include .from => do` |
| Tactic-mode `case` arm | **Yes** | `case «from» => exact ...` |
| Tactic-mode `match \| .x.y =>` pattern | **Yes** | `\| .include .«from» => do` |

The rule: anywhere the dot-notation parser would consume `from` as a
keyword token instead of as an identifier, escape with `«from»`.
Term-mode positions are robust because the dotted path already
disambiguates. Tactic-mode `case`/`match` positions aren't always.

---

## 2026-05-15 — Gotcha 4: Lean keywords as inductive / constructor names

**Discovery (Phase A.1, A.5)**: LLZK dialects use names that collide
with Lean's reserved keywords or built-in types:

| Where | Conflict | Resolution |
|---|---|---|
| Dialect inductive name | `String`, `Bool`, `Array`, `Function` shadow Lean built-ins | Trailing underscore (`String_`, `Bool_`, ...) — the opcodes macro strips it for the dialect mnemonic |
| Op constructor name | `from`, `include` are Lean keywords | Use as-is in the inductive (Lean accepts), but at *use* sites in `case` and `match` arms, wrap with `«...»` (French quotes): `case «include» op => ... | case «from» => ...` |

The trailing-underscore strip is implemented in `Veir/Meta/OpCode.lean`
(`Dialect.getName`); the keyword-escape is just Lean syntax. Both are
mechanical once you know the pattern.

**How to apply**: when porting a dialect, scan its TD constructor names
for Lean keywords and the inductive name for Lean built-ins. Common
hits: `from`, `to`, `if`, `let`, `do`, `in`, `match`, `with`, plus the
type names listed above.

**Future ports**: this will hit Function (constructor `function.return`
uses keyword-safe `return`, but the dialect inductive `Function`
collides — use `Function_`). Polymorphic, Array, Struct all need the
trailing-underscore treatment for the dialect inductive.

---

## 2026-05-15 — Gotcha 3: `Symbol`-trait ops still need `@name` parsing

**Discovery (Phase A.1 attempt)**: The retro / dialect-catalog
classified `Include` as "Tier 1, no infra needed" because
`include.from` is a *symbol producer*, not a user — so no
`SymbolRefAttr` (and no symbol-table lookup) is required.

In practice this is wrong. MLIR's generic format for an op with the
`Symbol` trait still emits the `sym_name` attribute as `@aliasName`,
not `"aliasName"` — i.e. the printer specializes for Symbol-trait ops.
VEIR's `AttrParser` doesn't handle the `@` lexeme as an attribute
form at all, so parsing fails before we get to anything semantic.

**Status update 2026-05-15 (later same day)**: VEIR upstream merged
PR #533 (`Add FlatSymbolRefAttr`) which adds exactly the minimal
flat-`@name` parser the gotcha described — `parseOptionalFlatSymbolRefAttr`
in `Veir/Parser/AttrParser.lean` and a `FlatSymbolRefAttr` case in
`Attribute`. **Phase A.1 (Include) is therefore unblocked** after the
upstream merge lands in this branch. The "Re-ordering implication"
below is partially reverted: Include is back in scope for Phase A.

**How to apply going forward**: any LLZK op declaring the `Symbol`
trait (Include, Function.def, Struct.def, Poly.template, Global.def)
can now store its `sym_name` as a `FlatSymbolRefAttr` in its property
dict. **Caveat**: there is still no `SymbolTable` trait, no symbol
resolution (`SymbolUserOpInterface`), and no invariant that the name
is unique within a scope. Those remain Phase F work (the standalone
Phase B was retired 2026-05-15; see plan.md).

---

## 2026-05-02 — Gotcha 1: exhaustive-match coupling across files

**Discovery (Felt port)**: `Veir/Verifier.lean`'s
`verifyLocalInvariants` is a fully-exhaustive `match opCode`.
`Veir/GlobalOpInfo.lean`'s `Properties.fromAttrDict` is a
fully-exhaustive `cases opCode` (Lean tactic). Adding a new
`OpCode.felt` constructor causes **both** to fail at build time:

```
error: Veir/Verifier.lean: Missing cases:
(OpCode.felt Felt.const) ... (18 missing arms)

error: Veir/GlobalOpInfo.lean: unsolved goals
case felt
attrDict : Std.HashMap ByteArray Attribute
op : Felt
⊢ Except String (propertiesOf (OpCode.felt op))
```

**How to apply**: Phase 2 of any dialect port (the opcode inductive)
is **not** a standalone unit of work. It's coupled to the verifier
arms (Phase 4) and to the properties dispatch (Phase 3 placeholder) at
build-time. Land all three in one commit. The
`harness/dialect-port-checklist.md` Phase 2 step is explicit about
this.

**Upstream-fix candidate**: add `_ => pure ()` wildcards to both
exhaustive matches. Trades static exhaustiveness for dialect-extension
modularity. Open question for VEIR upstream — they may prefer the
current behavior because it forces every op to be considered.

---

## 2026-05-02 — Gotcha 2: silent textual round-trip via `UnregisteredAttr`

**Discovery (Felt port)**: `AttrParser.parseOptionalDialectType` (L213)
is a fallthrough that captures any `!dialect.name` or
`!dialect.name<body>` it doesn't recognize as `UnregisteredAttr` whose
`value` is the raw textual slice. `UnregisteredAttr.toString` echoes
`value` verbatim. So **any unknown LLZK dialect type appears to
round-trip textually with zero parser support.**

What this means in practice: after Phase 3 of the Felt port, the
forcing-function test passed at 264/264. Phase 5 (the typed parser
branch) was strictly unnecessary for that test. The IR was internally
storing every `!felt.type<"bn254">` as
`Attribute.unregisteredAttr "!felt.type<\"bn254\">"`, *not* as
`Attribute.feltType { fieldName := some "bn254".toByteArray }`. The
Phase 1 typed case was effectively dead code until Phase 5 landed.

**How to apply**: Any port that adds a new typed `Attribute` case must
add the corresponding `parseOptionalXxx` and slot it into
`parseOptionalType` before `parseOptionalDialectType`. Or, equivalently,
a Lean-level unit test that constructs the typed case programmatically
and asserts it's reached after a textual round-trip. The
`harness/evaluation-criteria.md` §A.3 makes this an explicit acceptance
criterion.

**Upstream-fix candidate**: move `parseOptionalDialectType` behind a
"strict" mode that throws on unknown dialect types.

---

## 2026-05-02 — `@[opcodes]` lowercases the dialect name

**Discovery (Felt port)**: The `#generate_op_codes` macro picks up
`@[opcodes] inductive Xxx` and synthesizes the dialect arm of `OpCode`,
plus `OpCode.fromName` and `OpCode.name`. It **lowercases the inductive
name** (`Felt → "felt"`); op constructors are taken as-is (so `bit_and`
stays `bit_and`).

**How to apply**: When naming the inductive (`inductive Bool`,
`inductive Constrain`, etc.), the corresponding MLIR dialect name will
be lowercase. If LLZK's dialect name has underscores or mixed case
(`Mod_Arith` for `mod_arith`), match that pattern.

---

## 2026-05-02 — `IntegerAttr` is the workaround for missing structured attrs

**SUPERSEDED 2026-05-17 for felt.const specifically** — see the
2026-05-17 "per-dialect structured attributes" entry above. The
recipe documented there shows how to add a real structured attribute
when the workaround isn't acceptable. The IntegerAttr workaround
remains the recommended pattern for simple enums (e.g., `bool.cmp`'s
predicate); only structured payloads where LLZK rejects the
IntegerAttr-coerced form on parse need to upgrade.

**Discovery (Felt port)**: VEIR has no per-dialect attribute parser
today. Every `#dialect.name<...>` falls through to `UnregisteredAttr`.
Adding the first one is real new infrastructure.

LLZK's `#felt<const N> : !felt.type` carries both an `APInt` and the
field type. VEIR's port originally stored `felt.const`'s value as
`IntegerAttr`, mirroring VEIR's existing `arith.constant` /
`mod_arith.constant` precedent. The cost: printed output used
`<{"value" = 42 : i256}>` instead of LLZK's structured form. LLZK
refuses to parse the IntegerAttr form on input, so differential
testing failed — which forced the structured-attribute upgrade in
2026-05-17.

**How to apply**: For any LLZK structured attribute, the first
question is "can I use `IntegerAttr` (or another built-in) instead?".
The answer is *yes if VEIR's round-trip is the only consumer* and
*no if differential testing against `llzk-opt` is in scope* (because
LLZK rejects the IntegerAttr-coerced form on parse). Re-evaluate
once Phase G.1 (Function) lifts more differential tests. Either way
the workaround must be recorded in `harness/coverage.md`
(§Attributes).

**Re-evaluate when**: the next port has parameter lists or genuine
multi-field attributes — likely Polymorphic or Struct.

---

## 2026-05-02 — First-run `lake build` flake (elan toolchain-lock)

**Discovery (Felt port)**: First `lake build` after a fresh clone
failed with exit 143 (SIGTERM) on
`Veir.Rewriter.GetSet.{DetachOp,CreateOp}`. Traced to elan
toolchain-lock race at startup — another process held
`nightly-2026-04-29.lock`. Not OOM, not a real Lean error. Retry was
clean.

**How to apply**: On a first build after a fresh clone or toolchain
bump, if exit 143 hits `Rewriter/GetSet/*`, retry once. Don't
investigate as a real failure. Recorded in `baseline.txt` and
`harness/checkpoint-protocol.md` §9.

---

## Templated note (for future entries)

```
## YYYY-MM-DD — <short title>

**Discovery (<context: which dialect port, which infra spike>)**:
<one-paragraph description of what surprised you>

**How to apply**: <one paragraph describing how a future porter
benefits from this knowledge>

**Upstream-fix candidate** (optional): <if there's a code-side fix
that would prevent the gotcha from recurring>
```
