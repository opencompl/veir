// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `mul x, 2^k` is `shl x, k`: multiplication by a power of two is a shift.

"builtin.module"() ({
  "func.func"() <{function_type = (i32) -> i32, sym_name = "foo"}> ({
  ^bb0(%x: i32):
    %c = "llvm.mlir.constant"() <{value = 16 : i32}> : () -> i32
    %r = "llvm.mul"(%x, %c) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // Negative case: 3 is not a power of two, so the pattern does not fire.
  "func.func"() <{function_type = (i32) -> i32, sym_name = "bar"}> ({
  ^bb0(%x: i32):
    %c = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %r = "llvm.mul"(%x, %c) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// mul by 16 becomes shl by 4.
// CHECK:      ^{{.*}}(%[[X:.*]] : i32):
// CHECK:      %[[K:.*]] = "llvm.mlir.constant"() <{"value" = 4 : i32}> : () -> i32
// CHECK:      %[[R:.*]] = "llvm.shl"(%[[X]], %[[K]]) : (i32, i32) -> i32
// CHECK:      "func.return"(%[[R]]) : (i32) -> ()

// Non-power-of-two multiplier: the mul remains.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i32):
// CHECK:      %[[NR:.*]] = "llvm.mul"(%[[NX]], %{{.*}}) : (i32, i32) -> i32
// CHECK:      "func.return"(%[[NR]]) : (i32) -> ()
