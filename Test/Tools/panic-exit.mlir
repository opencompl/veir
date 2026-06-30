// RUN: not run-benchmarks no-such-benchmark 2>&1 | filecheck %s

// CHECK: PANIC
// CHECK: Unsupported benchmark
