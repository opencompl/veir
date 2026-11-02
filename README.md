# Verified Intermediate Representation

VeIR is a compiler infrastructure written in Lean that offers both an
[MLIR](https://mlir.llvm.org/)-style imperative design and
(optional) ITP-level verification.
VeIR connects with MLIR via the MLIR textual format, making it
easy to combine MLIR and VeIR tooling.

| VeIR Features                                         | Complete   | Verified |
|-------------------------------------------------------|------------| ---------|
| MLIR core data structures (block, operation, region)  | ✅         | 🔒        |
| define dialects                                       | ✅ (basic) |           |
| pass infrastructure                                   | ✅         |           |
| peephole rewriter                                     | ✅         |           |
| peephole rewriter (declarative)                       |            |           |
| interpreter framework                                 | ✅         |           |

## Testing

Our testing framework is split into two parts: unit tests written in Lean and
[FileCheck](https://llvm.org/docs/CommandGuide/FileCheck.html) tests for the
command line tool `veir-opt`.

### Unit Tests

Run the unit tests with:

```bash
lake test
```

### FileCheck Tests

FileCheck tests require [uv](https://docs.astral.sh/uv/) to be installed.

First, install dependencies:

```bash
uv sync
```

Then run the tests:

```bash
uv run lit Test/ -v
```

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

## From C to VeIR

This section gives an example showing how to run code through a VeIR
pass, starting from C code.

Prerequisite: An up-to-date MLIR bin directory in your PATH.

Start with a C function:
```bash
cat << _end_ > demorgan.c
unsigned d1(unsigned p, unsigned q) {
  return ~(~p & ~q);
}

unsigned short d2(unsigned short p, unsigned short q) {
  return ~(~p | ~q);
}
_end_
```

Compile to LLVM IR:
```bash
clang -cc1 -O0 -disable-O0-optnone -emit-llvm demorgan.c
```

Optimize it a little:
```bash
opt -passes=sroa demorgan.ll -S -o demorgan-opt.ll
```

Translate to MLIR:
```bash
mlir-translate --import-llvm demorgan-opt.ll | mlir-opt --mlir-print-op-generic --mlir-print-local-scope > demorgan-opt.mlir
```

Optimize using VeIR's InstCombine and DCE (dead code elimination) passes:
```bash
lake exec veir-opt -p=instcombine,dce demorgan-opt.mlir
```

Alternatively, you can batch up these commands using the provided
compiler driver and emit the optimized MLIR to stdout:
```bash
Tools/vcc demorgan.c --emit-mlir -O -o -
```

Without an explicit emit mode, `vcc` translates VeIR's output back to
LLVM IR and asks `clang` to produce an executable:
```bash
cat << _end_ > hello.c
#include <stdio.h>

int main(void) {
  printf("hello, world\n");
}
_end_

Tools/vcc hello.c -o hello
```

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
`Veir.Rewriter.WellFormed`.

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
lake build Veir.Rewriter.WellFormed allocator-tests ir-reuse-tests
lake exe allocator-tests
lake exe ir-reuse-tests
```

The tests cover slot clearing, neighboring bytes, shared snapshots, distinct
size classes, spare capacity, and 10,000 allocation/erasure cycles for each IR
object kind without arena growth after warmup.

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
