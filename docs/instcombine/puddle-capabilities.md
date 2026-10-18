# Puddle capability boundary for the LLVM InstCombine audit

This report describes the Puddle implementation in this checkout, before adding
audit-specific proof libraries. It is based on `Veir/PatternRewriter/Puddle/*`,
`Veir/Dialects/LLVM/OpInfo.lean`, and `UnitTest/Puddle.lean`.

## What a pattern can express

- A matcher is a rooted, exact operation graph. It can bind free SSA values and
  types, match non-root operations by opcode, exact operand/result arity and
  shared handles, and predicate on opcode properties. Reusing a value handle
  expresses SSA identity, so `m_Specific(X)`-style equality is available.
- `MatchProg.type` accepts any Boolean predicate on a `TypeAttr`, and
  `MatchProg.matchNative` accepts a Boolean predicate over already-bound types
  and properties. This is enough for integer widths, scalar type restrictions,
  constants, `nsw`/`nuw`, `exact`, comparison predicates, and other properties
  represented in the dialect records.
- A creator can construct concrete types/properties, transform matched metadata
  with `CreateProg.applyNative`, and create an ordered DAG of new operations.
  A replacement can select matched non-root values or created results, including
  multiple results.
- `Pattern.Valid` checks opcode support, root/handle well-formedness, and actual
  semantic refinement. Its semantic obligation says that every behavior of the
  matched root refines the replacement behavior; the unit tests contain genuine
  arbitrary-width proofs for `x + 0 -> x` and `x * 2 -> x + x`.
- Matching and creation preserve poison semantics through the existing
  `RuntimeValue`/`LLVM.Int` interpreter. Integer `add`, `sub`, `mul`, `sdiv`,
  `udiv`, `srem`, `urem`, `shl`, `lshr`, `ashr`, `and`, `or`, `xor`, `icmp`,
  `select`, casts, `freeze`, integer constants/poison/zero, and several
  integer intrinsics have interpreter cases. Overflow and exact flags are part
  of the relevant property records. `llvm.mlir.undef` is accepted by the
  verifier but currently has no interpreter branch. Float constants have a
  direct interpreter case, while poisoned floats cannot be represented.

## Freeze uses a fixed poison replacement

`LLVM.Int.freeze` in `Veir/Data/LLVM/Int/Basic.lean:845-852` preserves a defined
integer and maps poison to zero. It does not represent the nondeterministic
choice of LLVM freeze. Consequently, opcode/interpreter support alone does not
make every LLVM freeze rewrite valid under this model. For example, the eligible
unflagged scalar case `freeze(add X,1) -> add(freeze X,1)` evaluates to zero on
the left and one on the right when X is poison. The concrete Puddle pattern has
an independently checked `¬ Pattern.Valid` theorem in
`Veir/Passes/InstCombineLLVM/FreezePushThroughAddCounterexample.lean`, with a
runtime fixture satisfying the source eligibility guards. This is not an LLVM
bug claim.

## Opcode support

Puddle does not use a fixed opcode allow-list. `SupportedOpCode` accepts exactly
an opcode that is not a terminator and whose memory effect is `.none` for every
property value. For the integer InstCombine files, this includes LLVM constants,
poison, undef, zero, `and`, `or`, `xor`, `add`, `sub`, `mul`, `sdiv`, `udiv`,
`srem`, `urem`, `shl`, `lshr`, `ashr`, `icmp`, `select`, `trunc`, `sext`, `zext`,
`freeze`, `bitcast`, `inttoptr`, `ptrtoint`, `getelementptr`, aggregate/vector
insert/extract operations, and the pure integer intrinsics listed by LLVM
`getEffects` (count-zero/popcount, bit operations, min/max, abs, and saturating
arithmetic). Whether a useful semantic proof is possible is narrower than this
structural support set: the interpreter and `RuntimeValue` representation must
also model the involved types and values.

Terminators (`br`, `cond_br`, `switch`, `return`, `unreachable`) are rejected even
when their effect is `.none`. Loads, stores, allocation, calls, atomics, memory
intrinsics, lifetime/assume/vararg operations, globals/aliases/functions and any
operation conservatively assigned `.unknown` effects are rejected. A property-
specific purity proof is not supported: effects must be `.none` for *all*
properties of the opcode.

## Pure intrinsics are not generic calls

LLVM represents intrinsics as calls in C++, but the Puddle dialect has dedicated
pure opcodes for the following scalar integer operations. A source `CallInst`
or `CreateIntrinsic` alone is therefore not an unsupported-call diagnosis.
`Llvm.interpretOp'` in `OpInfo.lean` explicitly interprets these operations:

| LLVM intrinsic | Puddle opcode(s) | Material properties |
| --- | --- | --- |
| `llvm.fshl`, `llvm.fshr` | `intr__fshl`, `intr__fshr` | Three same-width integer operands |
| `llvm.ctlz`, `llvm.cttz` | `intr__ctlz`, `intr__cttz` | `is_zero_poison` |
| `llvm.ctpop` | `intr__ctpop` | Integer bit width |
| `llvm.bswap`, `llvm.bitreverse` | `intr__bswap`, `intr__bitreverse` | The current bswap verifier restricts widths to 16, 32, 64 |
| `llvm.smin`, `llvm.smax`, `llvm.umin`, `llvm.umax` | `intr__smin`, `intr__smax`, `intr__umin`, `intr__umax` | Signed/unsigned scalar semantics |
| `llvm.abs` | `intr__abs` | `is_int_min_poison` |
| `llvm.sadd.sat`, `llvm.uadd.sat` | `intr__sadd__sat`, `intr__uadd__sat` | Signed/unsigned saturation |
| `llvm.ssub.sat`, `llvm.usub.sat` | `intr__ssub__sat`, `intr__usub__sat` | Signed/unsigned saturation |
| `llvm.sshl.sat`, `llvm.ushl.sat` | `intr__sshl__sat`, `intr__ushl__sat` | Saturating shift semantics |

Proofs for these operations may require new lemmas; that is unfinished proof
work, not missing interpreter support. Conversely, `*.with.overflow`,
`scmp`/`ucmp`, and `vscale` have no corresponding opcode/interpreter case in this
checkout. Their absence must not be confused with the supported saturation,
comparison, and count-zero operations above.

## Integer flags are modeled semantics

The LLVM property records include `or.disjoint`, `trunc.nsw/nuw`, `zext.nneg`,
`nsw/nuw` on arithmetic and left shift, and `exact` on division and right
shifts. The interpreter passes these flags to the corresponding `LLVM.Int`
operations: a violated disjoint-or, trunc no-wrap, or nneg precondition yields
poison, and arithmetic no-wrap/exact flags use LLVM's poison-aware integer
semantics. These flags do not themselves block an arithmetic proof. A source
branch may still depend on LLVM overflow, KnownBits, or value-range analysis to
establish a flag or choose a rewrite; that source-side fact remains a matcher or
proof-model constraint, separate from the availability of flag semantics.

## Comparison flag limit

`IcmpProperties` currently contains only the comparison predicate. LLVM's
`samesign` property and its poison behavior are not represented. Flag-free
scalar ICmp patterns remain expressible; proofs must not claim to preserve or
model `samesign` simply because other integer overflow flags are supported.

## Pointer semantics require case-by-case review

The modeled single-index GEP currently multiplies `idx.toNat` by the element
stride for every index width (`OpInfo.lean:1618-1628`). LLVM instead normalizes
indices to its DataLayout index width using signed extension or truncation.
Consequently a narrow negative index is not modeled faithfully: for an i8 index
with bits 255 and stride one, the model adds 255, while explicitly sign-extending
that index to i64 makes it add 2^64-1. The scalar GEP index-normalization pattern has a globally validated
`¬ Pattern.Valid` theorem in
`Veir/Passes/InstCombineLLVM/GEPIndexNormalizationCounterexample.lean`. Its
runtime fixture also checks source eligibility and replacement verification.
This is a counterexample in the current Puddle model, not an LLVM bug claim.

A further proof-model restriction applies even to 64-bit `inttoptr`:
`InterpretsTo` (`Validity.lean:511-514`) requires a fixed result for every memory
state. `inttoptr` reconstructs object identity using `MemoryState.ptrFromInt`
and `decode`, so its result depends on the memory. A fixed-result premise may
exclude all ordinary nonpoison inputs; that is not a meaningful proof of a
pointer rewrite. The general pointer roundtrip needs state-aware semantics and
pointer/object consistency premises. `ptrtoint` alone returns address bits,
and the restricted GEP computation preserves object identity without consulting
memory, so this particular limitation does not automatically block them.


`Llvm.interpretOp'` does model pointer values (object identity plus a 64-bit
address), one-dynamic-index GEP scaled by `DataLayout.getTypeAllocSize`, and
64-bit `ptrtoint`/`inttoptr`. Pointer operations are therefore not automatically
unsupported. However, the current `icmp` and `select` interpreter cases accept
only integer operands; pointer comparisons and pointer-result selects have no
semantics there. GEP interpretation also does not model LLVM's full multi-index,
address-space, or no-wrap/inbounds conditions. Integer pointer differences are
not categorically unsupported: the modeled 64-bit `ptrtoint` result can be
subtracted using scalar integer semantics, and a restricted one-dynamic-index
GEP is interpreted with the data-layout element stride. There is no `ptrtoaddr`
opcode or interpreter case in this checkout, so only a `ptrtoint`-based source
specialization can use those semantics. A source fold that
needs arbitrary nested/indexed GEP decomposition, GEP no-wrap flags, address
spaces, or non-64-bit pointer arithmetic still exceeds this model. A proof of a
restricted pointer identity must state its modeled scope and cannot stand in
for the omitted LLVM behaviors. See `Veir/Dialects/LLVM/OpInfo.lean:1530` and
`:1618`.

The generic Puddle interpreter uses the default RV64 data layout. Its layout
query models scalar integer/byte/float types, 64-bit pointers, fixed arrays, and
fixed vectors. For example, an unflagged one-index GEP can be rebuilt with an
array-of-i8 element type having the same allocation stride. This does not imply
support for arbitrary LLVM target layouts or missing GEP flag semantics.

The pointer-cast width-normalization branches need special care. The default
layout has 64-bit pointers, and the current interpreter accepts `inttoptr` only
with an i64 input and `ptrtoint` only with an i64 output. LLVM's normalization
branches specifically require a *different* integer width. Thus their nontrivial
source operations are uninterpreted, while the interpreted i64 case does not
trigger the source rewrite. These branches need broader cast semantics; the
existence of i64 pointer casts is not an implemented specialization of them.

## Byte types need both source legality and interpreter support

`LLVM.Byte` represents a bit vector with a per-bit poison mask. Puddle interprets
equal-width integer/byte bitcasts, byte freeze, and byte `shl`/`lshr` (the byte
shift amount is an integer; byte `shl` cannot carry NSW). Its `trunc` interpreter
and verifier also accept byte values, but the pinned LLVM `CastInst::castIsValid`
requires integer types for truncation, so that does not create a ByteType variant
of an LLVM trunc rewrite.

The pure Byte library defines AND/OR/XOR functions, but the LLVM opcode
interpreter cases and verifier currently accept integers for those operations.
Helper definitions alone therefore do not establish opcode support for a
ByteType rewrite. Likewise, integer-only select and comparison interpretation
can block a larger graph even when one bitcast in that graph supports bytes.

Same-width integer/byte bitcast compositions and same-address-space pointer-only
bitcast compositions are modeled candidates in the general cast-pair rule.
Pointer-to-pointer bitcasts preserve the pointer value without reconstructing
object identity from memory. These must not be hidden by a blanket pointer-cast
blocker; any intermediate byte/integer-to-pointer conversion still needs the
state-dependent interpretation review described above.

## Operation verifier obligations

`Pattern.Valid` establishes handle structure and interpreter refinement. It does
not by itself prove that every created operation passes its dialect's local
verifier. In particular, `llvm.mlir.constant` requires the integer attribute's
type to equal the result type and its value to be normalized
(`Veir/Dialects/LLVM/OpInfo.lean:810` and `Veir/Verifier/Basic.lean:500`).
A mathematically correct constant in an attribute with a hard-coded type can
therefore pass the semantic theorem while producing rejected IR. Creators must
use the matched type and `IntegerAttr.ofInt`; execution tests must verify the
resulting IR. This was found and repaired in the initial constant-creating patterns, with
execution/verifier regression tests in `UnitTest/InstCombineLLVMConstants.lean`.
It was an implementation issue, not an LLVM counterexample.

## Coverage limits and proof-engineering costs

LLVM's `m_Undef` matcher also accepts poison (and aggregates made entirely of
undef/poison). An actual `llvm.mlir.undef` operation has no interpreter semantics,
but a scalar poison alternative does. Review these alternatives separately.
Likewise, a source `isGuaranteedNotToBeUndef` guard does not mean the pattern
matches an undef operation. Puddle's deterministic scalar/poison domain may
allow an unconditional proof of that restricted case; the algebra and poison
behavior still need proof, and that proof does not cover LLVM's per-use undef
choices. A missing not-undef analysis predicate alone is not a sufficient reason
to classify the entire scalar family as unsupported.

1. **No sound use-count predicate.** There is no declarative `oneUse`, use-count,
   or dead-use constraint. `inspectOperation` can query the live IR and therefore
   could check `hasOneUse`, but its result is deliberately unconstrained in the
   semantic model. Consequently it may restrict when an already-unconditional
   identity fires, but a `Pattern.Valid` proof cannot rely on a one-use fact.
   LLVM branches whose correctness (rather than profitability) needs use count
   cannot be represented soundly.
2. **No analysis facts over SSA values.** Native match predicates receive only
   types and operation properties, not values. Puddle has no declarative
   KnownBits, demanded-bits, range, sign-bit, nonzero, power-of-two, dominance,
   poison implication, or value-comparison analysis. Context inspection has the
   same proof-model limitation above. Branches guarded by these analyses need a
   new modeled matcher predicate or a theorem that makes the rewrite valid
   without the guard.
3. **Constants are property-backed operations, not an APInt expression DSL.**
   Literal integer values and arbitrary-width metadata transformations are
   expressible, but APInt predicates/calculations must be encoded manually over
   `IntegerAttr`/`Int` and then related to fixed-width `BitVec` semantics. Vector
   splats, poison-containing constants, `ConstantExpr`, and LLVM constant-folding
   helpers do not have ready-made Puddle matchers or proof lemmas.
4. **Flags are metadata but flag inference is manual.** Matching and setting
   `nsw`, `nuw`, `exact`, and `disjoint` is possible. Every propagation condition
   and poison-refinement argument must be proved explicitly; there is no library
   corresponding to LLVM's overflow analysis or `willNotOverflow*` helpers.
5. **Scalar integer semantics are the practical proof foundation.** The LLVM
   interpreter has direct scalar `RuntimeValue.int` semantics for the core
   arithmetic operations. LLVM vector integer and scalable-vector folds do not
   currently have an equivalent elementwise proof interface, so a scalar-only
   theorem is a deliberate narrower scope even when the upstream branch also
   handles vectors. Floating-point coverage is also unsuitable for an exhaustive
   audit because poisoned floats are not represented and fast-math reasoning is
   not supplied by Puddle.
6. **Graph shape is exact and local.** There are no commutative, associative,
   optional, variadic, or alternative-pattern combinators. Commuted forms require
   separate patterns; alternatives require separate rules. These are convenience
   omissions and increase the rule count; they do not block proof of each explicit
   graph shape. Puddle does not model
   PHI/control-flow rewriting, block creation, deletion beyond the matched root,
   mutation in place, or replacement of a non-root operation. This is not
   automatically a blocker: a root-operand/flag mutation can be encoded by
   constructing an equivalent new root, and some contextual producer mutations
   can be encoded with the consuming operation as the pattern root.
7. **Effectful and terminating rewrites are outside `Pattern.Valid`.** This rules
   out broad parts of calls, memory, atomics, and control flow regardless of
   whether an individual LLVM transform is safe.

The structural checker originally hid several helper reductions across module
boundaries. The audit exposed `HandleContext.empty`, `lookupBindings`, `lookup`,
`insertFresh`, and `forbid` without changing their behavior or existing
signatures, so concrete multi-operation patterns can now discharge structural
validity by kernel reduction. This is no longer a coverage limitation.

## Recommended proof tranche

The lowest-risk source-grounded tranche is scalar integer algebra in
`InstCombineAddSub.cpp` and `InstCombineMulDivRem.cpp`: exact graph matches over
`llvm.add/sub/mul`, constants, and flag-free replacements, preferably identities
that remain valid for poison. Start with branches such as `X * -1 -> 0 - X`,
`-X * -Y -> X * Y`, and similarly small add/sub cancellations after checking
their source guards and flag behavior. Treat vector claims, one-use requirements,
and propagated flags as separate follow-up scopes rather than silently dropping
their guards.

## Source landmarks

- `Veir/PatternRewriter/Puddle/Definitions.lean:191-240`: matcher model and the
  explicit warning that soundness cannot depend on `inspectOperation`.
- `Veir/PatternRewriter/Puddle/Definitions.lean:257-320`: creation and replacement
  capabilities.
- `Veir/PatternRewriter/Puddle/Validity.lean:20-60`: opcode support criterion.
- `Veir/PatternRewriter/Puddle/Validity.lean:643-680`: refinement and validity.
- `Veir/Dialects/LLVM/OpInfo.lean:456-482`: LLVM memory-effect classification.
- `Veir/Dialects/LLVM/OpInfo.lean:515-550`: terminators and poison propagation.
- `UnitTest/Puddle.lean:16-177`: semantic lemmas and genuine example proofs.

## Validation and source-variant accounting

Each source entry has its own Lean file; multiple explicit orientations may
share that entry's file. Reusable semantics lemmas belong in helper modules.
Run the entry's build and an executable rewrite/verifier regression, then
inspect `#print axioms` for every recorded `Pattern.Valid` theorem. This audit
accepts only `propext`, `Classical.choice`, and `Quot.sound`. In the pinned Lean
4.35.0-rc4 toolchain, both `pbv_decide` and ordinary `bv_decide` can introduce
native certificate-checking axioms; a successful build alone is insufficient.
The comparison proofs use constructive Nat/BitVec order algebra instead.

The proof manifest records `scope_review_complete`,
`remaining_supported_scope`, and `unsupported_scope`. The first indicates
that the source alternatives have been reviewed, not that every alternative
is proved. Remaining supported widths, predicates, operand orientations, and
flags stay explicit unfinished work. Unsupported alternatives need concrete
model limitations, such as absent vector semantics. Missing lemmas and proof
difficulty are not missing semantic capabilities. A fixed-width specialization
is useful intermediate progress, but it does not finish a supported arbitrary-
width family. The catalog cannot report overall completion while scope reviews
or known supported variants remain open.

Parallel workers have separate helpers, tests, and proof manifests. Root runs
the global checker only during a coordinated pause in Lean edits, because its
validation fingerprint covers the shared Lean source context and toolchain.
