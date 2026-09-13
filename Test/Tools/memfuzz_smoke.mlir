// Smoke test for the memory-model fuzzing harness in Tools/.
//
// The harness proper compares veir-interpret against Alive2's alive-exec,
// which is not available here, so this checks only the half that lives in
// this repository: that the generator still produces programs the interpreter
// accepts, and that its two output forms stay in step. A broken generator
// would otherwise only show up on the machines running the full harness.

// Every generated program must interpret to a value, to poison, or to
// undefined behaviour. Anything else, such as an unsupported operation, means
// the generator and the interpreter have drifted apart.
// RUN: python3 Tools/memfuzz_generate.py --seed 1 --ops 14 --mlir %t.1.mlir --ll %t.1.ll
// RUN: python3 Tools/memfuzz_generate.py --seed 2 --ops 14 --mlir %t.2.mlir --ll %t.2.ll
// RUN: python3 Tools/memfuzz_generate.py --seed 3 --ops 14 --mlir %t.3.mlir --ll %t.3.ll
// RUN: python3 Tools/memfuzz_generate.py --seed 4 --ops 14 --mlir %t.4.mlir --ll %t.4.ll
// RUN: veir-interpret %t.1.mlir | filecheck %s --check-prefix=INTERP
// RUN: veir-interpret %t.2.mlir | filecheck %s --check-prefix=INTERP
// RUN: veir-interpret %t.3.mlir | filecheck %s --check-prefix=INTERP
// RUN: veir-interpret %t.4.mlir | filecheck %s --check-prefix=INTERP
// INTERP: {{Program output|Undefined behavior}}

// The MLIR and the LLVM IR come from one program, so they must contain the
// same number of stores; a mismatch means one emitter was changed without the
// other.
// RUN: python3 Tools/memfuzz_generate.py --seed 42 --ops 20 --mlir %t.a.mlir --ll %t.a.ll
// RUN: grep -c "llvm.store" %t.a.mlir > %t.counts
// RUN: grep -c "^  store " %t.a.ll >> %t.counts
// RUN: sort -u %t.counts | filecheck %s --check-prefix=STORES
// STORES-COUNT-1: {{^[0-9]+$}}
// STORES-NOT: {{^[0-9]+$}}

// A fixed seed is a fixed program, which is what lets any case be reproduced
// from its index on any machine.
// RUN: python3 Tools/memfuzz_generate.py --seed 7 --ops 12 --mlir %t.r1.mlir --ll %t.r1.ll
// RUN: python3 Tools/memfuzz_generate.py --seed 7 --ops 12 --mlir %t.r2.mlir --ll %t.r2.ll
// RUN: diff %t.r1.mlir %t.r2.mlir
// RUN: diff %t.r1.ll %t.r2.ll

// The driver must stay runnable and keep its subcommands.
// RUN: python3 Tools/memfuzz --help | filecheck %s --check-prefix=HELP
// HELP: {{run.*collect.*repro.*farm}}

"builtin.module"() ({
}) : () -> ()
