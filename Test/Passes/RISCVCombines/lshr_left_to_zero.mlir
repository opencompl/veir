// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `lshr 0, x` is `0`: logically shifting zero right by any amount is still zero.

"builtin.module"() ({
  "func.func"() <{function_type = (i64) -> i64, sym_name = "foo"}> ({
  ^bb0(%x: i64):
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %r = "llvm.lshr"(%zero, %x) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: the shifted value is 1, not 0, so the shift is not eliminated.
  "func.func"() <{function_type = (i64) -> i64, sym_name = "bar"}> ({
  ^bb0(%x: i64):
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %r = "llvm.lshr"(%one, %x) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// The shift collapses to the zero constant, returned directly.
// CHECK:      ^{{.*}}(%[[X:.*]] : i64):
// CHECK:      %[[Z:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i64}> : () -> i64
// CHECK-NOT:  "llvm.lshr"
// CHECK:      "func.return"(%[[Z]]) : (i64) -> ()

// Shifted value is nonzero: the lshr survives.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i64):
// CHECK:      %[[NR:.*]] = "llvm.lshr"(%{{.*}}, %[[NX]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[NR]]) : (i64) -> ()
