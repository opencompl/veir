// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `(X & Y) | ~Y` is `X | ~Y`: the `& Y` is redundant once `~Y` is or'd in.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64) -> i64}> ({
  ^bb0(%x: i64, %y: i64):
    %m1 = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> i64
    %and = "llvm.and"(%x, %y) : (i64, i64) -> i64
    %noty = "llvm.xor"(%y, %m1) : (i64, i64) -> i64
    %r = "llvm.or"(%and, %noty) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: the xor constant is -2, not -1, so `noty` is not `~Y`.
  "func.func"() <{function_type = (i64, i64) -> i64}> ({
  ^bb0(%x: i64, %y: i64):
    %m2 = "llvm.mlir.constant"() <{value = -2 : i64}> : () -> i64
    %and = "llvm.and"(%x, %y) : (i64, i64) -> i64
    %noty = "llvm.xor"(%y, %m2) : (i64, i64) -> i64
    %r = "llvm.or"(%and, %noty) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// Rewritten to X | ~Y: the `or` now takes X directly, dropping the `and`.
// CHECK:      ^{{.*}}(%[[X:.*]] : i64, %[[Y:.*]] : i64):
// CHECK:      %[[NOTY:.*]] = "llvm.xor"(%[[Y]], %{{.*}}) : (i64, i64) -> i64
// CHECK:      %[[R:.*]] = "llvm.or"(%[[X]], %[[NOTY]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[R]]) : (i64) -> ()

// Not a real `~Y`: the `and` feeding the `or` survives.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i64, %[[NY:.*]] : i64):
// CHECK:      %[[NAND:.*]] = "llvm.and"(%[[NX]], %[[NY]]) : (i64, i64) -> i64
// CHECK:      %[[NR:.*]] = "llvm.or"(%[[NAND]], %{{.*}}) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[NR]]) : (i64) -> ()
