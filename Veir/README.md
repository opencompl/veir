# Buffered IR backend

This is the only IR implementation in this checkout. Its modules and namespaces live
under `Veir`, with the capacity-aware logical model, packed-property opcode subset
(Arith, LLVM, Builtin, Func, and Test), erased simulation specifications, and static parser
liveness proofs. There is no unbuffered backend, compiler pass pipeline, or interpreter.

## Names and entry points

- Import `Veir`, or modules under `Veir.IR`, `Veir.Rewriter`, and `Veir.Parser`.
  The temporary `Veir.Buffered` namespace used during the merge has been removed.
- Simulated pointers are `Veir.Sim.*`; the packed buffer is `Veir.Buffed.IRBufContext`.
- The source-input API is `Veir.Parser.parseSourceString`, with the theorem
  `Veir.Parser.parseSourceString_safe`. `UnitTest.ParserAPI` checks it through the library root.
- Executables: `buffed-benchmark`, `veir-parse`, `parser-tests`, `allocator-tests`, and
  `ir-allocation-tests`. The unbuffered CLI tools and their dependencies/tests are removed.
- ExArray's native `ffi_static.c` retains zero-on-extension, copy-on-write, and
  the bit-width argument required by `ExArray.read`'s ABI.
- Direnv, Nix, Make, and CI select `Tools/lean-clang` for full-LTO builds. In a plain shell,
  set `export LEAN_CC="$PWD/Tools/lean-clang"` (Clang and GMP/pkg-config are required).

```sh
lake build buffed-benchmark veir-parse parser-tests allocator-tests ir-allocation-tests
lake exe parser-tests
lake exe allocator-tests
lake exe ir-allocation-tests
```

### Historical merge validation

The earlier two-backend merge with main `1fe869b8` passed the then-current default build,
`lake test`, ExArray's native test, all three buffered test executables, and the parser's
standard-axiom audit. At that time, the native parser test exercised both backends, and the
upstream FileCheck suite reported 1,516 passes, two expected failures, and three unsupported
tests. Those unbuffered tests and coexistence checks are not part of this buffered-only
checkout; native buffered tests and `Tools/check-parser-cli` cover the retained parser.

A nine-sample alternating comparison against the frozen pre-merge `daeb068e` rewrite binary
(10,000 operations, 100% configuration, CPU 4, two warmups) puts all construction/rewrite
medians within 4% of pre-merge timings. The 100,000-operation SSA parse remains linear:
422.261 ms merged versus 515.816 ms for the previously benchmarked main `f9804b76`
(CPU 3, three warmups, nine alternating samples, parse-only timing). That parser baseline
is **not** the newer merge target. Raw results are in `/tmp/veir-merge-performance/`.

The benchmark results below are historical, predate the return to the `Veir` namespace,
and identify their baselines explicitly. No performance claim is made for this relocation.

## `buffed` compatibility command

`buffed` no longer flattens arguments or results and does not generate an `Inner`
implementation. It retains the historical source/public naming convention and the
`foo.eq_sim` and `foo.unfold` proof API, while forwarding `inline := true` (the default)
or `inline := false` to the source and public definitions. `UnitTest.BuffedAdoption` checks the full
retained inventory and `Tools/check-buffed-wrapper-codegen` verifies that no inner
implementations return in generated code.

### Historical argument/result flattening design

The remainder of this subsection describes the removed generator and is retained only
as historical context. Import `Veir.IR.Buffed.Meta` (or the narrower
`ArgumentFlattening` module) and write:

```lean
open Veir

buffed (inline := false) def addressSim (p : Sim.OperationPtr) : UInt64 := p.impl
```

This keeps `addressSim` inline and generates:

- `addressInner p_impl p_spec' := addressSim ⟨p_impl, p_spec'⟩`, with one argument
  per field of each simulated context/pointer argument. `inline := false` makes
  this nonrecursive function noinline; `inline := true` (the default) makes it inline.
  Recursive inners are always noinline, regardless of the flag, including `partial_fixpoint`.
- Inline `address p := addressInner p.impl p.spec'`, with the original signature.
- `address.eq_sim : address p = addressSim p`, the checked equivalence contract.
- `address.unfold : address p = p.impl`, rewriting to the original definition's body.

The generator threads dependencies through fields and subsequent arguments and preserves
`Erased` specifications and proof fields. Inner **results** now use raw representations:
`Sim.IRContext` becomes `IRBufContext`, and a Sim pointer becomes its raw pointer field.
Projection descends through ordinary `Option`, pairs, and proof subtypes; arrays and
unrecognized leaves retain their existing representations. Public signatures are unchanged.

`foo.inner_eq_sim` proves that the raw result equals the projection of the original source
result. `ResultView` uses this proof and an **erased** reference to that source result to
restore its exact specification and dependent proofs in the inline wrapper. The original
source is not executed a second time. In particular, a noinline inner returning a context
returns the raw buffer context, not a `Sim.IRContext` allocation or a metadata pair.

For recursive definitions, `fooInner` contains a rewritten copy of the body: input structs
are locally rebound from their fields, and recursive calls invoke `fooInner` with projected
fields. Result leaves are projected before returning, leaving tail calls raw rather than
mapping/reconstructing an `Option` after every recursive call. Projected-result recursion
currently requires recursive calls in tail/result position; non-tail recursion with an
unchanged result type remains supported. Projected `partial_fixpoint` results currently
use the `Option` order. These local input rebindings can disappear during
compilation; they are not recursive struct-valued arguments. The generator does **not**
generate separate `Impl`/`Spec` functions or require `Erased.map` to inline. Equivalence uses functional induction for terminating recursion,
and admissible least-fixed-point reindexing for `partial_fixpoint` (not an assumption
that unfolding equations have unique solutions). Unfolding equations retain the original
body; private helpers are expanded in theorem statements so rewriting works across module
boundaries. Safe definitions are supported,
including well-founded recursion and `partial_fixpoint` equations. Ordinary `partial def`
and unsafe definitions cannot supply this unfolding contract. A non-exported opaque computational helper must be made public
(or the source function kept private) rather than exposed by an unchecked rewrite.

`UnitTest.Buffed` covers the full pointer family, dependent contexts/results, polymorphism,
private definitions, recursion, attributes, and native execution. `UnitTest.BuffedImport`
checks exported equations. Run `python3 Tools/check-buffed-wrapper-codegen` to additionally
verify that generated C passes a raw scalar pointer/raw context directly to the noinline
inner function without constructing a `Sim` wrapper at the call site. It also checks
allocation-free recursive test bodies, raw result types, and absence of Sim result wrappers
in the production replacement loop and operand-removal helpers. A forwarding adapter to
the boxed source fails these checks.

All **202** declarations marked `buffed` in `yqlxtmmr` (`4e230ff25`), including five
`protected buffed` declarations, were migrated to this generator. After removing
`releaseRange`, **201** remain (168 production and 33 benchmark declarations),
including the benchmark rewrites, IR accessors/setters, allocation, linked lists, construction,
and printer helpers. Their original `inline := ...` choices control nonrecursive inner
functions. Recursive inners override these choices with `@[noinline]`: Lean skips body
specialization for inline templates but generally cannot inline recursive calls. Source
`fooSim` definitions and nonrecursive outer wrappers remain inline.
`Tools/buffed-declarations.tsv` records the retained inventory, with the fresh allocators renamed;
`UnitTest.BuffedAdoption` checks the 168 production signatures, flattened arities/results, inline
and protected attributes, actual recursive inner declarations, and generated equations' axioms. The codegen runner additionally
checks all 201 source declarations, including the 33 benchmark functions with pre-existing
proof placeholders. Proofs unfold `foo.unfold`; before induction on the original `fooSim`,
use `simp only [foo.eq_sim] at *`. Reconstructed results need not be definitionally equal
to the original function: use the proved equivalence rather than `rfl`.

Historical measurements **before recursive-body rewriting**: matched pre-/post-adoption measurements (CPU
pinned, two warmups, nine alternating samples; 5k/10k operations) show 4–14% slower
millisecond-scale rewrites and 16–30% slower construction with these historical inline
choices, while the repeated-reuse-first rewrite is about 20% faster. No result/spec
splitting or speculative inline-policy tuning was included in that comparison. Those
figures measure the old forwarding implementation, not the rewritten recursive inners.

Historical measurements with recursive-body rewriting **before disabling recursive inner
inlining**: matched 5k/10k comparisons show 1.5–11.1% faster
construction versus forwarding; ordinary millisecond-scale rewrites remain within about
3%. The repeated-reuse-first case is **13–18% slower** versus forwarding, including
2.380 → 2.688 ms at 300k. This is not direct-`Erased` parity: primary construction and
millisecond-scale rewrites remain 6.6–18.3% and 2.5–10.2% slower respectively. Results
and historical inline policies were unchanged in those measurements; argument flattening
alone was not a complete optimization fix.

Historical measurements **before raw-result projection**, with all recursive inners
noinline: the inventory audit finds 19 recursive inners:
18 changed (ten benchmark and eight production helpers); `replaceValue?Inner` was already
noinline. Nonrecursive policies, source definitions, outer wrappers, and results were
unchanged in that comparison.
Matched CPU-4 runs (two warmups, nine alternating samples) at 10k/100 show 5.8–8.6% faster
construction versus the previous recursive implementation. Fold/multiply rewrites improve
3.8–7.3%, while zero/reuse rewrites change little. At 100k, construction improves 6.4–9.9%;
repeated reuse at 300k is essentially unchanged (2.707 → 2.691 ms).
Ordinary 10k rewrites remain 0.3–7.5% slower than direct `Erased`; versus pre-`Erased`, six
are 4.8–14.3% slower while sparse constant folding is 15.4× faster. The additional eight
production changes are not uniformly beneficial versus the ten-benchmark-only experiment:
reuse-forwards rewriting is 3.7% slower in that comparison. Two noisy primary pairs were
repeated without discarding their original samples. Results, hashes, all samples, and
validation logs are in `/tmp/veir-buffed-all-recursive-noinline/`.

With **raw-result projection**, matched CPU-4 runs at 10k/100 (two warmups, nine
alternating samples) show 20.3–25.1% faster construction and 3.9–8.5% faster ordinary
rewrites versus the all-recursive-noinline version. Repeated reuse at 300k improves
from 2.682 to 1.704 ms. Ordinary 10k rewrites are roughly level with or up to 7.1% faster
than direct `Erased`; six ordinary rewrites are within −2.1% to +2.9% of pre-`Erased`.
This measures the whole representation change, including changed specialization and
constructor reuse, not an isolated allocation cost. Full samples, caveats, validation,
and C/native evidence: `/tmp/veir-buffed-raw-results/`.

## Running the benchmarks

```bash
lake exe buffed-benchmark add-fold-forwards 10000 100
```

To check performance changes, build the before/after executables with the same
Lean toolchain and compiler flags, then compare all nine supported cases:

```bash
PERF_CPU=4 PERF_CSV=/tmp/veir-performance.csv \
  Tools/compare-buffed-performance.pl /path/to/before/buffed-benchmark \
  .lake/build/bin/buffed-benchmark 10000 9 100
```

`PERF_CPU` is optional (Linux `taskset`). The comparison discards two warmups,
alternates execution order, and reports median construction/rewrite times and
variation. Run it without concurrent builds. Set `PERF_MAX_RATIO` to fail on
regressions above a chosen ratio; by default that check excludes phases shorter
than 1 ms (`PERF_MIN_MS`), but all timings are reported.

## Append-only arena allocation

Allocation appends zero-initialized bytes to the arena, as it did before the
free-list introduction (`66bbf61e5`). Deleted addresses are never reused.
There is no free list, size-class lookup, release bookkeeping, slot clearing,
or compaction. The separate attribute table is also append-only. All storage
is retained until its context and any shared snapshots are dropped.

`Rewriter.eraseOp` still detaches the operation and its operands and logically
deletes it. `Rewriter.eraseBlock` and `Rewriter.eraseRegion` logically delete
detached containers; callers must first remove their contents and uses and
supply the `FieldsInBounds` proof ruling out dangling references. These APIs
do not recursively delete a subtree. Their safety and well-formedness proofs
remain, as do static parser ownership/liveness and erased specifications.
Logical deletion itself leaves the runtime buffer unchanged.

Reservations are proved to start at the old arena end and preserve old reads.
Live pointer offsets do not change. Holding a shared snapshot can still require
copy-on-write when the arena is extended or modified. Repeated allocation and
deletion intentionally grows memory rather than reaching a reuse plateau.

Validation:

```sh
lake build Veir.Rewriter.WellFormed allocator-tests ir-allocation-tests
lake exe allocator-tests
lake exe ir-allocation-tests
```

Tests cover zeroed appended bytes, preserved old bytes and snapshots, overflow
rejection, spare capacity and back-allocated results, and 10,000 allocation/
deletion cycles for each IR object kind with the expected arena growth.

## Parsing MLIR into the buffered IR

`veir-parse` parses a file in MLIR's generic operation form directly into the buffered
context (`Veir/Parser/`). Its state and construction primitives carry `Sim.IRContext OpCode`
and simulated operation, block, region, and value pointers directly. Their specification
fields stay in `Erased`; operands, successors, and regions use ordinary pointer arrays.
`Veir/Parser/StaticIR.lean` calls the rewriter directly, without generated `*Impl` wrappers,
dummy specifications, or specialization warm-ups. Forward references use detached
`builtin.unrealized_conversion_cast` placeholders that are replaced and erased on definition,
and a forward-declared block that turns out to have arguments is replaced by a fresh block with
the right argument capacity. Construction requires erased liveness certificates: there is no
allocation registry, pointer-validation lookup, or final root-address check. The attribute
parser only covers the attributes and types of this branch's `Attribute`.

```sh
lake build veir-parse
.lake/build/bin/veir-parse input.mlir [--allow-unregistered-dialect] [--print] [--lex-only] [--repeat=N]
```

`--print` prints the parsed module back in generic form (values and blocks are named by their
buffer address), `--lex-only` only runs the lexer, `--repeat=N` parses the input N times.
The parse time is reported on stderr. Parsed contexts expose the raw buffer as `.buf`, and
`SourceInfo.opLocation?` looks up a simulated operation's source location by its address.

Run the parser regression tests with:

```sh
lake exe parser-tests
```

They cover forward SSA references, repeated forward successors (with and without block
arguments), nested scopes, properties, type aliases, unregistered operations, and diagnostics.

### Parser state verification

The production parser uses `StaticParserState`: context-independent `MlirParserData`, a
well-formed `StaticIR.Context`, and an erased `data.Live ctx.raw` proof. `State.lean` keeps
suspended block scopes explicit; `Liveness.lean` proves bounds, exclusive placeholder ownership,
and absence of published placeholder aliases. Source locations are historical metadata, not
liveness evidence. Context transactions consume the old state before mutating its buffer.

`Transitions.lean` supplies composable preservation frames for caller-held handles.
`References.lean`, `Retire.lean`, and `Blocks.lean` resolve names, publish definitions, and
logically delete exclusively owned placeholders. `Operations.lean` and `Bindings.lean` retain allocation,
result-count, and argument-count certificates through construction and registration.
`Scopes.lean` and `ConstructionParser.lean` carry these contracts through mutually recursive
region/block/operation parsing and scope restoration. Ordinary name lookup is still needed;
no second allocation-address lookup validates its result.

`parseSourceString` returns `StaticIR.Context × IR.Op × SourceInfo`. Its
`parseSourceString_safe` theorem derives structural well-formedness and root liveness directly
from the recursive parser's result certificate. The old runtime registry, checked-array
reconstruction, permissive reference adapter, and final root lookup have been removed.
`BuffedIR.lean` retains proof-taking construction aliases; arbitrary pointers no longer fit
those APIs without genuine current-context bounds proofs. Addresses remain context-local and
reusable, not generation-tagged identifiers.

All specification computations and preservation certificates erase. Allocation capacity checks,
syntax/type diagnostics, and physical deletion-condition guards (no uses/regions, detached empty
blocks) still execute; these are not pointer-provenance validation. Erasure returns `none` when
its semantic conditions fail.

There are no parser construction `sorry`s, new axioms, or unchecked casts. Tests audit all parser
declarations, including private proofs and partial functions' executable implementations, allowing
only `propext`, `Classical.choice`, and `Quot.sound`. They also reject reintroducing the allocation
registry into parser dependencies. Coverage includes grouped/large forward-result sets,
self-references, caller-local handles, nested same-name block scopes, deletion guards, and static
rejection of invalid ghost specifications. The old floating-point equality axiom is a theorem
using Lean's float model.

This establishes structural IR safety and static parser-state provenance, not MLIR semantic
validity (typing, dominance, dialect rules) or correctness of the accepted parser language.

### Parser benchmark

#### Comparison with main and allocator copy-on-write correction

Parse-only measurements compare main `f9804b76` with `e588b78a` plus the allocator correction
in `Veir/IR/Buffed/RawAccessors.lean`. Both use Lean 4.35.0, release `-O3`, full LTO, CPU 3
on a Ryzen 9 9950X, three warm-ups and nine alternating samples. Main's semantic verifier
is disabled; input reading, printing, and final IR destruction are outside the timing interval.
Main's parser sources are unchanged; its compiler version and native flags were normalized.

| Input | N | Main | Buffered before correction | Buffered corrected |
|-------|--:|-----:|---------------------------:|-------------------:|
| SSA chain | 1,000 | 4.660 ms | 6.672 ms | 4.022 ms |
| SSA chain | 10,000 | 46.734 ms | 170.420 ms | 39.732 ms |
| SSA chain | 100,000 | 506.061 ms | 12,503.340 ms | 421.974 ms |
| Forward SSA chain | 10,000 | 46.083 ms | 151.723 ms | 42.090 ms |
| Nested regions | 10,000 | 99.695 ms | 1,431.994 ms | 86.922 ms |

Times are medians; the before-correction column is from the preceding benchmark session.
N counts arithmetic steps for SSA chains (N+2 total operations), definitions for forward
chains (N+1 operations), and definition/region-owner/nested-user groups for nested inputs
(3N+1 operations).

The initial slowdown was an allocator COW bug, not specification evaluation. Profiling the
100,000-step input put 92% of sampled CPU time in memory copying under `IRBufContext.reserve`.
Its fresh-allocation branch read `bctx.usize` after extending the buffer, retaining the old
buffer and forcing a full copy at almost every allocation. Using `bctx.size.toUInt64` reuses
the scalar size already read by the capacity check; generated C no longer retains the buffer
for a later size read. COW checks and all bounds/preservation proofs remain intact.

#### Historical comparison before the allocator correction

A local comparison against the immediately preceding runtime-registry parser used CPU affinity,
three warm-ups, and nine alternating samples. Median parse times:

| Input | Operations | Runtime registry | Static provenance |
|-------|-----------:|-----------------:|------------------:|
| SSA chain | 1,000 | 7.098 ms | 6.608 ms |
| SSA chain | 10,000 | 175.245 ms | 171.311 ms |
| Forward SSA chain | 1,000 | 10.713 ms | 6.881 ms |
| Forward SSA chain | 10,000 | 280.713 ms | 151.416 ms |

Generated C was inspected for buffer ownership and metadata copy-on-write. In particular,
definition-set updates consume the old data record before hash insertion, and recursive scope
restoration reads the returned scope stack rather than retaining old SSA/location tables.
These results are not a comparison against the pre-`Erased` migration baseline; peak memory
has not been measured.

The measurements below are historical, from before the `Erased` port; they have not been
reproduced for the new implementation.

Inputs are `add-tree-N.mlir` files as produced by the `print-add-tree` benchmark of the
evaluation scripts: a `builtin.module` with N/2 pairs of `"test.test"() : () -> i32` and
`"arith.addi"(%c, %acc) : (i32, i32) -> i32`, i.e. about N operations. Times are the best of 3
runs on one machine; `mlir-opt` and the main-branch `veir-opt` always print their output and
were run with their verifiers disabled.

| N       | veir-parse, parse only | veir-parse, parse + print | main-branch veir-opt | mlir-opt |
|---------|-----------------------:|--------------------------:|---------------------:|---------:|
| 10 000  | 0.03 s                 | 0.05 s                    | 0.06 s               | 0.06 s   |
| 100 000 | 0.34 s                 | 0.47 s                    | 0.55 s               | 0.19 s   |
| 300 000 | 1.21 s                 | 1.60 s                    | 1.74 s               | 0.57 s   |

Peak resident memory at N = 300 000: 235 MB (`veir-parse`), 304 MB (main-branch `veir-opt`),
240 MB (`mlir-opt`). Of the 1.21 s parse time at N = 300 000, lexing the 3.9 M tokens takes
0.14 s and building the 300 000 operations in the buffered context takes about 0.03 s
(`buffed-benchmark add-fold-forwards 150000` reports its `create` time); the rest is spent in
the parser itself.

A `perf` profile of the N = 300 000 parse is flat: about a third of the samples are in
allocation and reference counting (`lean_dec_ref_cold`, `mi_malloc_small`, `mi_free`), the
largest single Lean symbol is the per-operation insertion into the `opLocations` table (5 %),
followed by byte-array comparison and hashing of value names, the name-table updates when
leaving a scope, the lexer (2 %) and the operation construction itself (1 %).
