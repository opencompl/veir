// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `urem x, 2^k` is `and x, (2^k - 1)`: unsigned remainder by a power of two is a
// bitmask.

"builtin.module"() ({
  "func.func"() <{function_type = (i32) -> i32, sym_name = "foo"}> ({
  ^bb0(%x: i32):
    %c = "llvm.mlir.constant"() <{value = 8 : i32}> : () -> i32
    %r = "llvm.urem"(%x, %c) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // Negative case: 6 is not a power of two, so the pattern does not fire.
  "func.func"() <{function_type = (i32) -> i32, sym_name = "bar"}> ({
  ^bb0(%x: i32):
    %c = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %r = "llvm.urem"(%x, %c) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// urem by 8 becomes and with the mask 7.
// CHECK:      ^{{.*}}(%[[X:.*]] : i32):
// CHECK:      %[[M:.*]] = "llvm.mlir.constant"() <{"value" = 7 : i32}> : () -> i32
// CHECK:      %[[R:.*]] = "llvm.and"(%[[X]], %[[M]]) : (i32, i32) -> i32
// CHECK:      "func.return"(%[[R]]) : (i32) -> ()

// Non-power-of-two modulus: the urem remains.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i32):
// CHECK:      %[[NR:.*]] = "llvm.urem"(%[[NX]], %{{.*}}) : (i32, i32) -> i32
// CHECK:      "func.return"(%[[NR]]) : (i32) -> ()
