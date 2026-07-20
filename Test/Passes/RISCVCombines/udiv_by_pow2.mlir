// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `udiv x, 2^k` is `lshr x, k`: unsigned division by a power of two is a shift.

"builtin.module"() ({
  "func.func"() <{function_type = (i32) -> i32, sym_name = "foo"}> ({
  ^bb0(%x: i32):
    %c = "llvm.mlir.constant"() <{value = 8 : i32}> : () -> i32
    %r = "llvm.udiv"(%x, %c) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // Negative case: 6 is not a power of two, so the pattern does not fire.
  "func.func"() <{function_type = (i32) -> i32, sym_name = "bar"}> ({
  ^bb0(%x: i32):
    %c = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %r = "llvm.udiv"(%x, %c) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// udiv by 8 becomes lshr by 3.
// CHECK:      ^{{.*}}(%[[X:.*]] : i32):
// CHECK:      %[[K:.*]] = "llvm.mlir.constant"() <{"value" = 3 : i32}> : () -> i32
// CHECK:      %[[R:.*]] = "llvm.lshr"(%[[X]], %[[K]]) : (i32, i32) -> i32
// CHECK:      "func.return"(%[[R]]) : (i32) -> ()

// Non-power-of-two divisor: the udiv remains.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i32):
// CHECK:      %[[NR:.*]] = "llvm.udiv"(%[[NX]], %{{.*}}) : (i32, i32) -> i32
// CHECK:      "func.return"(%[[NR]]) : (i32) -> ()
