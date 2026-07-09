// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `mul 0, x` is `0`: multiplying by zero is always zero.

"builtin.module"() ({
  "func.func"() <{function_type = (i64) -> i64}> ({
  ^bb0(%x: i64):
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %r = "llvm.mul"(%zero, %x) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: the left factor is 1, not 0, so the multiply is not eliminated.
  "func.func"() <{function_type = (i64) -> i64}> ({
  ^bb0(%x: i64):
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %r = "llvm.mul"(%one, %x) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// The multiply collapses to the zero constant, returned directly.
// CHECK:      ^{{.*}}(%[[X:.*]] : i64):
// CHECK:      %[[Z:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i64}> : () -> i64
// CHECK-NOT:  "llvm.mul"
// CHECK:      "func.return"(%[[Z]]) : (i64) -> ()

// Left factor is nonzero: the mul survives.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i64):
// CHECK:      %[[NR:.*]] = "llvm.mul"(%{{.*}}, %[[NX]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[NR]]) : (i64) -> ()
