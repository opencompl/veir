// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `mul 0, x` is `0`: multiplying by zero is always zero.

"builtin.module"() ({
  "func.func"() <{function_type = (i64) -> i64}> ({
  ^bb0(%x: i64):
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %r = "llvm.mul"(%zero, %x) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: the left factor is 3, not 0, so the multiply is not eliminated.
  // (3 is not a power of two, so `mul_to_shl` does not fire either.)
  "func.func"() <{function_type = (i64) -> i64}> ({
  ^bb0(%x: i64):
    %three = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %r = "llvm.mul"(%three, %x) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// The multiply collapses to the zero constant, returned directly.
// CHECK:      ^{{.*}}(%[[X:.*]] : i64):
// CHECK:      %[[Z:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i64}> : () -> i64
// CHECK-NOT:  "llvm.mul"
// CHECK:      "func.return"(%[[Z]]) : (i64) -> ()

// Left factor is nonzero: the mul survives. `commute_const_mul` moves the
// constant `3` to the right, so the surviving mul is `mul x, 3`.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i64):
// CHECK:      %[[NR:.*]] = "llvm.mul"(%[[NX]], %{{.*}}) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[NR]]) : (i64) -> ()
