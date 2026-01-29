# Supplementary material for "Fast and Correct Pointer-Based Data Structures in ITPs"

This directory contains the heap-based data structure of MLIR in Lean,
its formalization, as well as additional 

## Installation

To build the project, you need to install [Lean 4](https://lean-lang.org/install/).

The project can then be built and tested using
```bash
lake build
lake test
```

Additionally, to run the [FileCheck](https://llvm.org/docs/CommandGuide/FileCheck.html)
tests, [uv](https://docs.astral.sh/uv/) needs to be installed. `FileCheck` is then
installed with

```bash
uv sync
```

and then the tests run with

```bash
uv run lit Test/ -v
```

## Contents

Here is a description of the main files in the `ChainMail/` directory, that are relevant to the
paper:

- `IR/`: Contains the low-level definitions and specifications of ChainMail IR.
  - `Basic.lean`: Definitions of the ChainMail data structures, including getters and setters.
  - `InBounds.lean`: Definitions and proofs related to in-bounds accesses.
  - `GetSet.lean`: Lemmas about the behavior of getters and setters.
  - `Fields.lean`: Definition of the `FieldInBounds` predicate and proof of preservation for setters.
  - `WellFormed.lean`: Definition of the `WellFormed` predicate and lemmas about it.
  - `DeallocLemmas.lean`: Well-formedness lemmas about `OperationPtr.dealloc`.
- `Rewriter/`: Contains high-level definitions of `Rewiter`, which contains user-facing IR mutation operations.
  - `InsertPoint.lean`: Definition of `InsertPoint`, which is used to specify where to insert
    new operations.
  - `LinkedList/`: Lower-level operations that directly mutate some doubly linked lists.
    Contains also proof of preservation of well-formedness. 
  - `Basic.lean`: Definitions of the `Rewriter` operations that mutates ChainMail data structures.
  - `GetSet.lean`: Lemmas about the behavior of getters and the `Rewriter` API.
  - `WellFormed/`: Proofs of preservation of `WellFormed` for the `Rewriter` API.
  - `InlineBlock.lean`: Definition of `inlineBlock`, with proof of preservation of well-formedness.
- `PatternRewriter/`: Contains a definition of `PatternRewriter`, which applies a pattern rewrite
  until convergence.
- `Parser/`: Parser from MLIR textual format to the `ChainMail` data structures.
- `Printer.lean`: Printer from the `ChainMail` data structures to MLIR textual format.
- `Benchmarks.lean`: The set of benchmarks used in the paper.
