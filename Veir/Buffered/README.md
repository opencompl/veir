# Buffered IR backend

The buffered implementation lives in modules and namespaces under `Veir.Buffered`.
The upstream unbuffered IR, dialect interfaces, parser, rewriter, passes, interpreter, and
CLI tools retain their `Veir` names. Both backends can be imported together; `UnitTest.Buffered`
checks this and the original parser safety API.

The buffered backend retains its capacity-aware logical model, packed-property opcode subset
(Arith, LLVM, Builtin, Func, and Test), erased simulation specifications, and static parser
liveness proofs. Merging main does not silently convert the upstream pass pipeline to buffered
storage or claim support for all of main's newer dialect operations in `veir-parse`.
Standard-library support lemmas and generic simp sets are shared with the upstream modules.

## Names and entry points after the merge

- Buffered modules previously under `Veir.IR`, `Veir.Rewriter`, and `Veir.Parser` are now under
  `Veir.Buffered.IR`, `Veir.Buffered.Rewriter`, and `Veir.Buffered.Parser`.
- Buffered simulated pointers are `Veir.Buffered.Sim.*`; the packed buffer is
  `Veir.Buffered.Buffed.IRBufContext`.
- Import `Veir.Buffered` for the backend. Import `Veir.Parser.Buffered` for compatibility
  exports `Veir.Parser.parseSourceString` and `Veir.Parser.parseSourceString_safe`.
- The upstream source-input API remains `Veir.Input.parseSourceString`.
- `buffed-benchmark`, `veir-parse`, `parser-tests`, `allocator-tests`, and `ir-reuse-tests`
  retain their executable names. Main's `veir-opt`, `veir-interpret`, `veir2mir`, and
  `run-benchmarks` are also built.
- The shared native ExArray implementation follows main's `ffi_static.cpp` → `ffi_static.c`
  rename, retaining zero-on-extension, explicit range clearing, allocation-reuse support,
  and the explicit bit-width argument required by `ExArray.read`'s native ABI.
- `ExArray/compiler` moved to `Tools/lean-clang`. Direnv, the Nix shell/apps, Make, and CI
  select it for full-LTO native builds. For a plain shell, set
  `export LEAN_CC="$PWD/Tools/lean-clang"` (Clang and GMP/pkg-config are required).

```sh
lake build buffed-benchmark veir-parse parser-tests allocator-tests ir-reuse-tests
lake exe parser-tests
lake exe allocator-tests
lake exe ir-reuse-tests
```

### Merge validation

After merging main `1fe869b8`, the default build, `lake test`, ExArray's native test, all
three buffered test executables, and the parser's standard-axiom audit pass. The native parser
test also imports and runs both backends in one executable. The filecheck suite reports
1,516 passes, two expected failures, and three unsupported tests. Five historical parser
fixtures retain identical output on identical inputs; the merged fixtures also round-trip.

A nine-sample alternating comparison against the frozen pre-merge `daeb068e` rewrite binary
(10,000 operations, 100% configuration, CPU 4, two warmups) puts all construction/rewrite
medians within 4% of pre-merge timings. The 100,000-operation SSA parse remains linear:
422.261 ms merged versus 515.816 ms for the previously benchmarked main `f9804b76`
(CPU 3, three warmups, nine alternating samples, parse-only timing). That parser baseline
is **not** the newer merge target. Raw results are in `/tmp/veir-merge-performance/`.

The benchmark results below predate the namespace relocation and identify their historical
baselines explicitly.

## Argument-only `buffed` wrappers

Import `Veir.Buffered.IR.Buffed.Meta` (or the narrower `ArgumentFlattening` module)
and write:

```lean
open Veir.Buffered

buffed (inline := false) def addressSim (p : Sim.OperationPtr) : UInt64 := p.impl
```

This keeps `addressSim` inline and generates:

- `addressInner p_impl p_spec' := addressSim ⟨p_impl, p_spec'⟩`, with one argument
  per field of each simulated context/pointer argument. `inline := false` makes
  this function noinline; `inline := true` (the default) makes it inline.
- Inline `address p := addressInner p.impl p.spec'`, with the original signature.
- `address.unfold : address p = p.impl`, rewriting to the original definition's body.

The generator threads dependencies through fields and subsequent arguments, preserves
`Erased` specifications and proof fields verbatim, and leaves results, ordinary arrays,
and ordinary options unchanged. It does **not** generate `Impl`/`Spec` functions, split
results, rewrite recursive calls, or require `Erased.map` to inline. Recursive unfolding
equations use the original recursion theorem; private helpers are expanded in theorem
statements so rewriting works across module boundaries. Safe definitions are supported,
including well-founded recursion and `partial_fixpoint` equations. Ordinary `partial def`
and unsafe definitions cannot supply this unfolding contract. A non-exported opaque computational helper must be made public
(or the source function kept private) rather than exposed by an unchecked rewrite.

`UnitTest.Buffed` covers the full pointer family, dependent contexts/results, polymorphism,
private definitions, recursion, attributes, and native execution. `UnitTest.BuffedImport`
checks exported equations. Run `python3 Tools/check-buffed-wrapper-codegen` to additionally
verify that generated C passes a raw scalar pointer/raw context directly to the noinline
inner function without constructing a `Sim` wrapper at the call site.

All **202** declarations marked `buffed` in `yqlxtmmr` (`4e230ff25`), including five
`protected buffed` declarations, now use this generator,
including the benchmark rewrites, IR accessors/setters, recycling, linked lists, construction,
and printer helpers. Their original `inline := ...` choices control the new inner functions.
`Tools/buffed-declarations.tsv` records the complete historical inventory;
`UnitTest.BuffedAdoption` checks the 169 production signatures, flattened arities, inline
and protected attributes, and generated equations' axioms. The codegen runner additionally
checks all 202 source declarations, including the 33 benchmark functions with pre-existing
proof placeholders. Proofs unfold `foo.unfold`; induction uses the original `fooSim` definition.

Flattening does not guarantee a speedup: matched pre-/post-adoption measurements (CPU
pinned, two warmups, nine alternating samples; 5k/10k operations) show 4–14% slower
millisecond-scale rewrites and 16–30% slower construction with these historical inline
choices, while the repeated-reuse-first rewrite is about 20% faster. No result/spec
splitting or speculative inline-policy tuning is included in this adoption.

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

## Reusing deleted IR storage

The buffered context has an exact-size free list. Erasing an operation, block,
or region releases its complete byte allocation; subsequent rewriter
construction reuses a free allocation of the same size before extending the
arena. Operation allocations include the results preceding the operation header
and all reserved capacity. Live pointers do not move.

Free-list lookup, insertion, and removal take expected amortized O(1) time.
Reallocation clears the reused range with `memset`, taking O(allocation size),
then initializes its header and properties. Deletion does not scan or compact
the arena. The existing operand/use unlinking costs still apply to operation
erasure. As with other persistent buffer mutations, keeping an old context
snapshot can require copying the backing buffer on the next write.

`Rewriter.eraseOp` now releases storage after detaching the operation and its
operands. `Rewriter.eraseBlock` and `Rewriter.eraseRegion` release detached
containers; callers must first remove their contents and uses and supply the
`FieldsInBounds` proof ruling out dangling references. These APIs do not
recursively delete a subtree. Their well-formedness theorems, together with the
updated construction and replacement proofs, are exported by
`Veir.Buffered.Rewriter.WellFormed`.

The free-list invariant proves that free ranges are in bounds, mutually
disjoint, and disjoint from every live allocation. Allocation consumes its slot
and preserves the encoding of all other objects. These invariants and the
specification context are erased from the generated executable rewriter code.

This is arena reuse: memory is retained for future allocations, rather than
returned to the operating system. Free ranges are neither split nor coalesced,
so a workload that continually requests new sizes can still grow the arena.
The separate attribute table remains append-only.

Validation:

```sh
lake build Veir.Buffered.Rewriter.WellFormed allocator-tests ir-reuse-tests
lake exe allocator-tests
lake exe ir-reuse-tests
```

The tests cover slot clearing, neighboring bytes, shared snapshots, distinct
size classes, spare capacity, and 10,000 allocation/erasure cycles for each IR
object kind without arena growth after warmup.

## Parsing MLIR into the buffered IR

`veir-parse` parses a file in MLIR's generic operation form directly into the buffered
context (`Veir/Buffered/Parser/`). Its state and construction primitives carry `Sim.IRContext OpCode`
and simulated operation, block, region, and value pointers directly. Their specification
fields stay in `Erased`; operands, successors, and regions use ordinary pointer arrays.
`Veir/Buffered/Parser/StaticIR.lean` calls the rewriter directly, without generated `*Impl` wrappers,
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
reclaim exclusively owned placeholders. `Operations.lean` and `Bindings.lean` retain allocation,
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
in `Veir/Buffered/IR/Buffed/RawAccessors.lean`. Both use Lean 4.35.0, release `-O3`, full LTO, CPU 3
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
