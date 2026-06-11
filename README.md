# Verified Intermediate Representation

> ⚠️ **Experimental fork — work in progress.**
> This is the `project-llzk` organization's fork of
> [opencompl/veir](https://github.com/opencompl/veir). It carries an
> experimental Lean port of [LLZK](https://github.com/Veridise/llzk-lib)'s
> Felt dialect that is not yet upstreamed and not for production use.
> The companion assurance infrastructure lives at
> [project-llzk/llzk-lean](https://github.com/project-llzk/llzk-lean).
>
> This fork's `main` has diverged from upstream `opencompl/veir`'s
> `main`. To sync upstream changes, fetch from `opencompl/veir`
> directly and merge as needed.

VeIR is a compiler infrastructure written in Lean that offers both an
[MLIR](https://mlir.llvm.org/)-style imperative design and
(optional) ITP-level verification.
VeIR connects with MLIR via the MLIR textual format, making it
easy to combine MLIR and VeIR tooling.

## LLZK Companion Pin

The current llzk-lean proof-basis pin is documented in
[`docs/harness/PINS.md`](docs/harness/PINS.md). For companion checks against a
neighboring llzk-lean checkout, run:

```bash
scripts/harness/verify-companion-pin.sh --companion-llzk-lean ../llzk-lean
```

This verifies that llzk-lean's Lake metadata uses the accepted
`project-llzk/veir` remote, that `rev` and `inputRev` identify the accepted
commit, and that `.lake/packages/VeIR` is clean at that commit.

The Felt drop-in replacement plan is tracked in
[`docs/drop-in-roadmap.md`](docs/drop-in-roadmap.md), with the project-wide
roadmap in the companion llzk-lean checkout at
`../llzk-lean/docs/drop-in-roadmap.md`.
Phase 9 and Phase 10 planning files live under [`docs/phases/`](docs/phases/).

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
