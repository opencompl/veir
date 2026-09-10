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
lake exe run-benchmarks add-fold-worklist
```

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
