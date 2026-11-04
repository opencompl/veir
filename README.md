# VeIR — verified buffered intermediate representation

This checkout contains the **buffer-backed VeIR implementation only**, with the scope of
its original buffered branch and the subsequent verification and generator improvements.
It provides an MLIR-style IR, verified construction and rewriting, allocation recycling,
and a parser/printer for generic MLIR syntax.

## Scope

- Packed buffer storage and simulated pointers with erased logical specifications.
- Capacity, bounds, ownership/liveness, and well-formedness proofs for supported operations.
- The `buffed` generator: raw inner arguments/results with checked public reconstruction.
- A static, registry-free parser and printer; registered opcode definitions for the
  supported Arith, LLVM, Builtin, Func, and Test subsets.
- Construction/rewrite benchmarks, allocator tests, parser tests, and code-generation audits.

The unbuffered backend, pass pipeline, interpreter, instruction selection, register
allocation, compiler drivers, and their tests are **not included**. Dialect definitions do
not imply support for the full upstream dialects or an executable compiler pipeline.

## Build and test

Install [Lean and Lake](https://lean-lang.org/install/), Clang, GMP development headers,
and `pkg-config` (or `pkgconf`). Use the checked-in `lean-toolchain` version. Full-LTO
native builds use the compiler wrapper:

```sh
export LEAN_CC="$PWD/Tools/lean-clang"
lake build
lake test
lake build parser-tests allocator-tests ir-reuse-tests
lake exe parser-tests
lake exe allocator-tests
lake exe ir-reuse-tests
python3 Tools/check-buffed-wrapper-codegen
python3 Tools/check-orphan-modules
python3 Tools/check-parser-cli
(cd ExArray && lake exe test)
```

`make build` and `make tests` wrap these tasks (`make tests` uses `uv` for Python).
Python 3.11 or newer is required; the audit/report scripts need no third-party packages.
`nix develop` supplies the development environment; direnv users can run `direnv allow`.
Nix apps expose `build`, `tests`, `veir-parse`, and `buffed-benchmark`.

## Entry points

Import `Veir`, or narrower modules under `Veir.IR`, `Veir.Rewriter`, and `Veir.Parser`.
The former `Veir.Buffered` namespace/directory has been promoted to `Veir`.

```sh
lake exe veir-parse input.mlir --print
lake exe buffed-benchmark add-fold-forwards 10000 100
```

Omit the filename to parse stdin. `Veir.Parser.parseSourceString` returns a verified static
context; `Veir.Parser.parseSourceString_safe` proves structural well-formedness and root
bounds on successful parses. This is not a proof of typing, dominance, dialect validity,
or complete MLIR-language correctness.

See [the implementation documentation](Veir/README.md) for detailed APIs, guarantees,
benchmark methodology, and historical performance results.

## Performance reports

The [current buffered VeIR vs MLIR report](artifacts/current-vs-mlir/index.html)
uses `../buffed-evaluation`'s runner and plotter on the six common workloads, serially.
[Methodology and raw-data guide](artifacts/current-vs-mlir/README.md).

The [current vs pre-Erased comparison](artifacts/pre-erased-comparison/index.html)
uses the runner and plotting code from `../buffed-evaluation`, with serial execution.
[Methodology and raw-data guide](artifacts/pre-erased-comparison/README.md).

The [HTML comparison](artifacts/buffed-vs-veir-mlir/index.html) and its adjacent raw data are
preserved historical measurements from the two-backend checkout. They are not measurements
of this namespace relocation. The HTML is self-contained and can be opened locally.

`Tools/compare-buffed-performance.pl` compares two supplied buffered binaries.
`Tools/generate-buffed-comparison.py --baseline-veir /path/to/run-benchmarks` compares this
backend with an **external** unbuffered VeIR executable and the MLIR benchmark from
`../buffed-evaluation`. It runs one benchmark process at a time. Use a new `--output`
directory for fresh measurements, or `--render artifacts/buffed-vs-veir-mlir/data.json`
to render the saved results without running benchmarks.
