// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `sub a, (mul x, C)` is `add a, (mul x, -C)` when C is a constant.

"builtin.module"() ({
  "func.func"() <{function_type = (i32, i32) -> i32, sym_name = "foo"}> ({
  ^bb0(%a: i32, %x: i32):
    %c = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %m = "llvm.mul"(%x, %c) : (i32, i32) -> i32
    %r = "llvm.sub"(%a, %m) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // Negative case: the mul's second operand is not a constant, so the pattern does not fire.
  "func.func"() <{function_type = (i32, i32, i32) -> i32, sym_name = "bar"}> ({
  ^bb0(%a: i32, %x: i32, %y: i32):
    %m = "llvm.mul"(%x, %y) : (i32, i32) -> i32
    %r = "llvm.sub"(%a, %m) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// The sub becomes add a, (mul x, -C).
// CHECK:      ^{{.*}}(%[[A:.*]] : i32, %[[X:.*]] : i32):
// CHECK:      %[[NC:.*]] = "llvm.mlir.constant"() <{"value" = -3 : i32}> : () -> i32
// CHECK:      %[[NM:.*]] = "llvm.mul"(%[[X]], %[[NC]]) : (i32, i32) -> i32
// CHECK:      %[[R:.*]] = "llvm.add"(%[[A]], %[[NM]]) : (i32, i32) -> i32
// CHECK:      "func.return"(%[[R]]) : (i32) -> ()

// Non-constant mul operand: the sub remains.
// CHECK:      ^{{.*}}(%[[NA:.*]] : i32, %[[NX:.*]] : i32, %[[NY:.*]] : i32):
// CHECK:      %[[NMM:.*]] = "llvm.mul"(%[[NX]], %[[NY]]) : (i32, i32) -> i32
// CHECK:      %[[NR:.*]] = "llvm.sub"(%[[NA]], %[[NMM]]) : (i32, i32) -> i32
// CHECK:      "func.return"(%[[NR]]) : (i32) -> ()
