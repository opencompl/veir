# Differential testing of the memory model against Alive2

`Tools/memfuzz` runs random memory-using programs under VeIR's interpreter and
under Alive2's `alive-exec`, and reports every case where the two disagree. It
is how the interpreter's memory model is checked against a reference that
already encodes LLVM's rules for provenance, liveness, alignment and poison.

## How a case is built

`Tools/memfuzz_generate.py` builds one program and prints it twice, once as
VeIR's generic LLVM-dialect MLIR and once as LLVM IR. There is no translation
step between the two, so a difference in the tools' answers is a difference in
their semantics rather than in a translator.

A program is a straight-line `@main` returning an `i64` folded from loaded
values, over objects addressed through `getelementptr`. What it may contain is
set by the generator's options, and their defaults track what the interpreter
models, so a run with the defaults is always one the interpreter is expected to
survive. Today that is `alloca`, `getelementptr` and integer loads and stores,
with out-of-bounds offsets, misalignment and null dereferences drawn at tunable
rates.

Everything past that is behind an option until the model catches up:
`--ptr-values` for storing and loading pointers, and the `--w-` weights for
the heap family, the memory intrinsics and the pointer/integer casts. Raising
one before the interpreter implements it is how you see what is missing.

## Running

Build the two tools first. `veir-interpret` comes from `lake build
veir-interpret`. `alive-exec` comes from an Alive2 build configured with
`-DBUILD_TV=1` against the same LLVM release the repository targets; Alive2
tracks LLVM main, so a checkout contemporary with that release is needed.

One shard on one machine:

```
Tools/memfuzz run --run-id today --shard 0 --cases 500 \
    --out memfuzz-out --alive /path/to/alive-exec
```

A hundred machines, over ssh or SLURM, writing into a shared directory:

```
Tools/memfuzz farm --run-id today --shards 100 --cases 500 \
    --out /shared/memfuzz --hosts hosts.txt --chdir /work/veir \
    --alive /opt/alive2/alive-exec
Tools/memfuzz farm --run-id today --shards 100 --cases 500 \
    --out /shared/memfuzz --slurm --chdir /work/veir
```

Then merge the reports and rank what turned up:

```
Tools/memfuzz collect --out /shared/memfuzz
```

Work is split by seed rather than by handing programs around. Case `n` of a run
is generated from a seed derived from the run identifier and `n` alone, so
shard `i` covers the block `[i * cases, (i + 1) * cases)` that no other shard
touches, and any case can be rebuilt anywhere from its index:

```
Tools/memfuzz repro --run-id today --index 41735
```

Adding machines means raising `--shards`; nothing else changes, and the shards
never communicate.

## Verdicts

Four of them are findings, listed worst first by `collect`:

- `value-mismatch`, the two tools return different values.
- `veir-ub-only`, VeIR calls a program undefined that the reference runs.
- `alive-ub-only`, VeIR runs a program the reference calls undefined, so the
  model is missing an undefined-behaviour condition.
- `veir-poison-only`, VeIR loses a value the reference defines.

The rest are not:

- `alive-imprecise`, VeIR returns a defined value and Alive2 returns poison
  with the same bits. Poison stands for any value, so this is a refinement of
  the reference. Alive2 reaches poison through the granularity of its byte
  encoding, which a concrete interpreter does not share.
- `skipped`, the reference declined to answer, usually an SMT timeout.
- `agree`.

## Questions the generator does not ask

Some questions have different answers under a concrete interpreter and under a
verifier that reasons over every layout a program could have. Asking them
produces noise rather than findings, so the generator does not.

- **Object alignment is never below eight.** An access that claims more
  alignment than its object declares is undefined to Alive2, which must assume
  the worst layout, and fine in VeIR, which picks one. Misalignment is reached
  through odd offsets instead, on which the two agree.
- **Addresses never reach the result.** They differ between the two models by
  construction, so only differences within one object are used.

`Test/Tools/memfuzz_smoke.mlir` checks the half of this that does not need
`alive-exec`, so a generator that stops matching the interpreter is caught by
the ordinary test suite.
