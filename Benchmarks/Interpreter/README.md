# CTree interpreter comparison

Build with `lake build`. Run either backend on an MLIR module containing a
zero-argument `@main`:

```sh
.lake/build/bin/veir-interpret Benchmarks/Interpreter/llvm-1000.mlir
.lake/build/bin/veir-interpret --ctree Benchmarks/Interpreter/llvm-1000.mlir
.lake/build/bin/veir-interpret --benchmark=1000 Benchmarks/Interpreter/llvm-1000.mlir
.lake/build/bin/veir-interpret --benchmark=1000 Benchmarks/Interpreter/arith-1000.mlir
```

Each `*-1000.mlir` input has exactly **1,000 executed operations**: two constants,
997 dependent additions, and one return. The surrounding module and function
are not counted. Both return `997 : i32` (`0x000003e5`). Generate other sizes with:

```sh
python3 Benchmarks/Interpreter/generate.py /tmp/llvm-5000.mlir --operations 5000
python3 Benchmarks/Interpreter/generate.py /tmp/arith-1000.mlir --dialect arith
```

The benchmark parses and verifies once, checks matching outputs, warms up each
backend ten times, then measures seven batches of N invocations using
`IO.monoNanosNow`. Backend order alternates between batches. Each invocation
creates a fresh variable/memory state and, for CTree, constructs and executes a
fresh tree. Native `execute` is marked `noinline`; the generated C calls it
inside the repetition loop. Parsing, verification, printing, and result
comparison are excluded from the timer. The ratio is median CTree batch time
divided by median normal batch time. All batch times are printed, so variation
is visible. These straight-line integer workloads do not predict the cost of
memory-heavy programs or deeply nested regions.

## Implementation

`Veir/Interpreter/CTree/Basic.lean` builds on the interpreter exercised by
`UnitTest/CTreeInterpreter.lean`. LLVM operations use the existing
`Llvm.interpretOpCTree`; other registered operations lift the normal operation
semantics. CFG traversal, memory, nested `scf.if`/`scf.yield`, failure, and UB are
represented by the CTree interpreter. SSA reads, result writes, block-argument
writes, and scope entry/exit are explicit effects in
`Veir/Interpreter/CTree/Effects.lean`. Tree continuations contain no SSA map;
the concrete runner owns the map and consumes it on each update. Reads return
only the requested runtime values. The effect family is indexed by the IR
context so a tree cannot accidentally run against a different context.
Unsupported operations still fail; this does not add support for all MLIR
dialects or function calls.

The executable runner in `Veir/Interpreter/CTree/Run.lean` resolves LLVM freeze
choices to zero, matching the normal interpreter's deterministic choice. It
consumes a finite approximation directly, threading the SSA map outside the
tree. Inherited region scopes save a snapshot and restore it on exit; function
scopes start empty and restore the caller on return. A snapshot can force a copy
on the first write inside a scope, but flat operation and CFG iteration retain
no previous maps. Each run starts with independent state. This uses ordinary
pure Lean code and its reference-counted copy-on-write optimization.

`--fuel=N` bounds observed tree nodes (default 1,000,000), including the new SSA
events; exhaustion is distinct from failure and UB. The same fuel value now
covers fewer operations than before. Memory is still threaded through trees;
this change specifically addresses SSA-map copying, not memory-heavy workloads.

Two execution fixes were needed before benchmarking:

- `CTree.iter` now delays recursion inside the tau continuation. The previous
  eager argument to `tau1` could evaluate an infinite loop before the runner
  had an opportunity to enforce its fuel limit.
- Function execution walks the CFG with one CTree iteration. Binding whole
  block trees inside region trees and then binding the function result caused
  repeated reconstruction in the approximation-based coinductive representation.
  Preliminary versions took seconds for 100 operations and exceeded 30–45 second
  limits for 1,000. The original measurements below include the flattened traversal
  and direct approximation runner, not that initial implementation.

Nested-region semantics remain recursive; the benchmark measures a flat CFG.

## Validation

- Project build and `UnitTest.CTreeInterpreter` (including nested conditionals,
  malformed input, UB/failure separation, fuel boundaries, an infinite tree,
  nested-region memory effects, scope restoration/isolation, and tree reuse).
- Differential run over all 387 pre-existing `Test/Interpreter` fixtures:
  identical stdout, stderr and exit status for normal and CTree backends.
- Eight CLI/FileCheck regressions: arithmetic, branch, freeze, memory, UB,
  fuel exhaustion, and benchmark output.

## Runner-owned SSA effects: new measurements (2026-09-28)

Native execution-only medians, seven alternating batches. All six cases
completed and returned the same results as the normal interpreter. The 100k
straight-line case has 99,994 operations in exactly 100,000 lines. Loop inputs
remain 17 lines with eight static operations and three basic blocks.

| Input | Normal now | CTree before | CTree now | CTree now / normal now |
| --- | ---: | ---: | ---: | ---: |
| Straight-line: 1k operations | 0.369 ms | 3.680 ms | 3.260 ms | 8.83× |
| Straight-line: 10k operations | 4.294 ms | 187.644 ms | 32.727 ms | 7.62× |
| Straight-line: 100k lines | 65.425 ms | 43,584.690 ms | 355.023 ms | 5.43× |
| Loop: 1k iterations | 0.813 ms | 1.819 ms | 8.176 ms | 10.06× |
| Loop: 10k iterations | 7.923 ms | 18.259 ms | 80.450 ms | 10.15× |
| Loop: 100k iterations | 81.716 ms | 180.501 ms | 801.567 ms | 9.81× |

The new straight-line CTree times scale approximately with operation count:
3.26 → 32.73 → 355.02 ms. The 100k case is about 123× faster than the previous
CTree measurement, and 10k is about 5.7× faster. This is evidence that the
repeated whole-map copying cost has been removed for flat execution, rather
than a formal complexity guarantee. Inspection of generated `Run.c` confirms
that the runner passes its store into result writes without incrementing the
store's reference count. Inherited scope entry intentionally retains a snapshot.

The tradeoff is higher fixed overhead from explicit read/write events and their
continuations. Loops already used a small, bounded map and did not suffer the
large-copy problem; they now take approximately 4.4–4.5× longer than the previous
CTree implementation. Both loop versions scale linearly with iteration count.
This implementation fixes ownership and large-program scaling; reducing the
number or interpretation cost of SSA events is a separate optimization.

The “before” values are the earlier saved runs below, not a simultaneous rerun
of the old binary. In particular, the old 100k CTree median uses six completed
samples, and the old 1k run had substantial host timing variation. Current
normal timings are remeasured alongside the new CTree implementation.

New runs per batch are 100/10/1 for both straight-line and loop sizes. Warmups
are three per backend except for the 100k-line input, which uses one. Default
fuel is 1,000,000 throughout. Parsing and verification are excluded; the new
100k-line command took 163.5 seconds wall time, mostly verification.

Reproduce with the commands in [ssa-effects-results.json](ssa-effects-results.json),
which also records exact medians, input hashes, and source/executable hashes.
Raw results:

- Straight-line: [1k](llvm-1000-ssa-effects-results.txt),
  [10k](llvm-10000-ssa-effects-results.txt),
  [100k lines](llvm-100000-lines-ssa-effects-results.txt).
- Loops: [1k](llvm-loop-1000-ssa-effects-results.txt),
  [10k](llvm-loop-10000-ssa-effects-results.txt),
  [100k](llvm-loop-100000-ssa-effects-results.txt).

## Original measurements before SSA effects (2026-09-28)

Local macOS arm64 host, Lean `v4.35.0-rc1`, Lake `buildType = "release"`.
Seven batches of 1,000 runs per backend, default fuel:

| 1,000-operation input | Normal median | CTree median | CTree / normal |
| --- | ---: | ---: | ---: |
| LLVM constants/adds | 0.833 ms | 3.680 ms | 4.42× |
| arith constants/adds | 0.385 ms | 2.445 ms | 6.36× |

Both backends returned `997` for both inputs. Raw batch measurements are saved
in [llvm-1000-results.txt](llvm-1000-results.txt) and
[arith-1000-results.txt](arith-1000-results.txt).
There was substantial timing variation on this shared host (LLVM normal batches
0.495–1.340 ms, CTree 2.661–5.884 ms; arith normal 0.368–0.900 ms, CTree
2.390–5.378 ms). Treat the result as roughly 4–6× overhead on these workloads,
not a precise estimate of relative dialect performance. An earlier 100-run
LLVM batch experiment gave 0.409 ms versus 2.429 ms (5.93×).


## Original 100,000-line program measurements

`llvm-100000-lines.mlir` is exactly **100,000 lines** (5,977,639 bytes),
including two comment lines and four module/function wrapper lines. It executes
99,994 operations: two constants, 99,991 dependent additions of one, and one
return. Its expected output is `99991 : i32` (`0x00018697`). This is the same
LLVM addition chain as the smaller benchmark.

```sh
python3 Benchmarks/Interpreter/generate.py Benchmarks/Interpreter/llvm-100000-lines.mlir --lines 100000
.lake/build/bin/veir-interpret --benchmark=1 --warmups=1 Benchmarks/Interpreter/llvm-100000-lines.mlir
```

The generator accepts either `--lines` (exact physical line count) or
`--operations` (executed operation count). The large benchmark retains the
same seven alternating batches, with one run per batch and one warmup per
backend. `--warmups` defaults to ten, preserving the smaller benchmark. The
default fuel of 1,000,000 is unchanged. Progress is printed to stderr after
verification and after every batch, outside the timed intervals.

Verification is expensive for this input: `OperationPtr.dominatesWithinBlock`
in `Veir/IR/Dominance.lean` scans the linked operation list from the definition
to its use. Reusing `%one` across the entire block therefore gives quadratic
verification work. Verification runs once before all timed invocations; its
cost is excluded from the execution results.


A one-second macOS `sample` of a preliminary large-file CTree warmup showed
183 of 436 active-thread samples in `lean_copy_expand_array` under the
variable-state hash-map insertion path, and 238 in reference-count cleanup
(`lean_del_core_other`) under CTree bind/unfold. This points to hash-map
copying and cleanup as the large-input execution bottleneck. The preliminary
run was interrupted to reduce its excessive warmup/repetition count; the
reported measurements use the command above and were not sampled.


### Large-input results (2026-09-28)

Execution-only medians, native release executable, one warmup per backend and
one execution per batch:

| Input | Normal | CTree | CTree / normal | Completed samples (normal / CTree) |
| --- | ---: | ---: | ---: | ---: |
| 10,000 operations (10,006 lines) | 4.6395 ms | 187.6435 ms | 40.44× | 7 / 7 |
| 100,000 lines (99,994 operations) | 70.1367 ms | 43.5847 s | 621.42× | 7 / 6 |

The 100,000-line run was interrupted at the user's request during the final
CTree sample. Its medians use all completed samples, with the conventional
average of the middle two for the six CTree samples. CTree samples ranged from
41.991 to 44.185 seconds; normal samples ranged from 56.236 to 88.877 ms.
Parsing and verification took approximately 170 seconds, excluded above.
The completed samples passed the benchmark's result-equality checks.

The 10,000-operation run completed all seven batches. Both backends returned
`9997 : i32` (`0x0000270d`). Reproduce it with:

```sh
python3 Benchmarks/Interpreter/generate.py Benchmarks/Interpreter/llvm-10000.mlir --operations 10000
.lake/build/bin/veir-interpret --benchmark=1 --warmups=1 Benchmarks/Interpreter/llvm-10000.mlir
```

Raw results and run metadata:

- [10,000 operations: timings](llvm-10000-results.txt), [metadata](llvm-10000-run.json)
- [100,000 lines: partial timings](llvm-100000-lines-results.txt), [metadata](llvm-100000-lines-run.json)


## Original small-program loop measurements (2026-09-28)

The `llvm-loop-1000.mlir`, `llvm-loop-10000.mlir`, and
`llvm-loop-100000.mlir` programs each have **17 lines, three basic blocks, and
eight static operations**, excluding the module/function wrappers. Only the
iteration-bound constant and comments differ. The entry block initializes
zero, one, and the bound, then branches into the loop. The loop increments its
block-argument counter, compares it with the bound using unsigned less-than,
and either branches back with the new counter or exits. The exit block returns
the counter. Positive trip counts execute exactly N loop iterations.

Each iteration executes three operations (`llvm.add`, `llvm.icmp`, and
`llvm.cond_br`), for **3N + 5 dynamic operations** overall. Both interpreters
passed full verification and returned the expected N at all three sizes.
Unlike the straight-line addition chain, the loop repeatedly updates the same
small set of SSA entries, so the variable-state map does not grow with N.

| Loop iterations | Dynamic operations | Normal median | CTree median | CTree / normal |
| --- | ---: | ---: | ---: | ---: |
| 1,000 | 3,005 | 0.824429 ms | 1.818607 ms | 2.205899× |
| 10,000 | 30,005 | 8.176467 ms | 18.258775 ms | 2.233089× |
| 100,000 | 300,005 | 80.864500 ms | 180.501291 ms | 2.232145× |

These are native execution-only timings using the same interpreter code and
release executable, excluding parsing and verification. Each case uses seven
alternating batches and three warmups per backend. Runs per batch are 100,
10, and 1 respectively, so each batch executes 100,000 total loop iterations.
The default fuel remains 1,000,000. All batches completed. Timing scales
approximately linearly here, with CTree staying about 2.2× slower; the much
larger slowdown of the straight-line input does not occur with a fixed-size
variable map.

```sh
python3 Benchmarks/Interpreter/generate_loop.py Benchmarks/Interpreter/llvm-loop-1000.mlir --iterations 1000
python3 Benchmarks/Interpreter/generate_loop.py Benchmarks/Interpreter/llvm-loop-10000.mlir --iterations 10000
python3 Benchmarks/Interpreter/generate_loop.py Benchmarks/Interpreter/llvm-loop-100000.mlir --iterations 100000
.lake/build/bin/veir-interpret --benchmark=100 --warmups=3 Benchmarks/Interpreter/llvm-loop-1000.mlir
.lake/build/bin/veir-interpret --benchmark=10 --warmups=3 Benchmarks/Interpreter/llvm-loop-10000.mlir
.lake/build/bin/veir-interpret --benchmark=1 --warmups=3 Benchmarks/Interpreter/llvm-loop-100000.mlir
```

Raw timings: [1k](llvm-loop-1000-results.txt),
[10k](llvm-loop-10000-results.txt), [100k](llvm-loop-100000-results.txt).
Commands, counts, and timing metadata: [llvm-loop-results.json](llvm-loop-results.json).
