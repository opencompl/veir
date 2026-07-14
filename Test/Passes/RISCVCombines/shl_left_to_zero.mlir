// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `shl 0, x` is `0`: shifting zero left by any amount is still zero.

"builtin.module"() ({
  "func.func"() <{function_type = (i64) -> i64, sym_name = "foo"}> ({
  ^bb0(%x: i64):
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %r = "llvm.shl"(%zero, %x) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: the shifted value is 1, not 0, so the shift is not eliminated.
  "func.func"() <{function_type = (i64) -> i64, sym_name = "bar"}> ({
  ^bb0(%x: i64):
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %r = "llvm.shl"(%one, %x) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// The shift collapses to the zero constant, returned directly.
// CHECK:      ^{{.*}}(%[[X:.*]] : i64):
// CHECK:      %[[Z:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i64}> : () -> i64
// CHECK-NOT:  "llvm.shl"
// CHECK:      "func.return"(%[[Z]]) : (i64) -> ()

// Shifted value is nonzero: the shl survives.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i64):
// CHECK:      %[[NR:.*]] = "llvm.shl"(%{{.*}}, %[[NX]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[NR]]) : (i64) -> ()
