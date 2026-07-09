// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `sub x, C` is `add x, -C` when the second operand is a constant.

"builtin.module"() ({
  "func.func"() <{function_type = (i32) -> i32}> ({
  ^bb0(%x: i32):
    %c = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %r = "llvm.sub"(%x, %c) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // Negative case: the second operand is not a constant, so the pattern does not fire.
  "func.func"() <{function_type = (i32, i32) -> i32}> ({
  ^bb0(%x: i32, %y: i32):
    %r = "llvm.sub"(%x, %y) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// The sub becomes an add against the negated constant.
// CHECK:      ^{{.*}}(%[[X:.*]] : i32):
// CHECK:      %[[NC:.*]] = "llvm.mlir.constant"() <{"value" = -7 : i32}> : () -> i32
// CHECK:      %[[R:.*]] = "llvm.add"(%[[X]], %[[NC]]) : (i32, i32) -> i32
// CHECK:      "func.return"(%[[R]]) : (i32) -> ()

// Non-constant second operand: the sub remains.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i32, %[[NY:.*]] : i32):
// CHECK:      %[[NR:.*]] = "llvm.sub"(%[[NX]], %[[NY]]) : (i32, i32) -> i32
// CHECK:      "func.return"(%[[NR]]) : (i32) -> ()
