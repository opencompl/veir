# Verified Intermediate Representation

VeIR is a compiler infrastructure written in Lean that offers both an
[MLIR](https://mlir.llvm.org/)-style imperative design and
(optional) ITP-level verification.
VeIR connects with MLIR via the MLIR textual format, making it
easy to combine MLIR and VeIR tooling.

VeIR currently offers the following features:

| Feature                                               | Complete | Verified |
|-------------------------------------------------------|----------| ---------|
| MLIR core data structures (block, operation, region)  | ✅       | 🔒        |
| define dialects                                       | ✅       |           |
| pass infrastructure                                   | ✅       |           |
| peephole rewriter                                     | ✅       |           |
| interpreter                                           | ✅       |           |

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

