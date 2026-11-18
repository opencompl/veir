// Check that (1) the custom input split marker is used instead of the default
// one, (2) the output split marker is still the default one and (3) the input
// is rejected if `--split-input-file` is not given.

// The extra quotes stop veir-opt from splitting this run command itself!
// See https://github.com/llvm/llvm-project/blob/main/mlir/test/mlir-translate/split-markers.mlir
// RUN: veir-opt %s --split-input-file="// ""SPLIT" | filecheck %s
// RUN: not veir-opt %s 2>&1 | filecheck %s --check-prefix=NOSPLIT

// CHECK:        "builtin.module"{{.*}}
// CHECK-NEXT:   // -----
// CHECK-NEXT:   "builtin.module"{{.*}}
// CHECK-NOT:    {{.}}
// NOSPLIT: split-markers.mlir:[[# @LINE + 8]]:1: error: unexpected trailing input after top-level operation

"builtin.module"() ({
// -----
}) : () -> ()

// SPLIT

"builtin.module"() ({}) : () -> ()
