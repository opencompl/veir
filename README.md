# Verified Intermediate Representation

VeIR is compiler infrastructure written in Lean that mirrors
[MLIR](https://mlir.llvm.org/), designed to bring formal
verification to the compiler stack. It is compatible with MLIR
through its textual format, allowing interoperability with
existing MLIR tooling.

The project currently contains a formal verification of the MLIR
data structures, as well as a basic infrastructure to define
dialects, passes, peephole rewrites, and interpreters.

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

