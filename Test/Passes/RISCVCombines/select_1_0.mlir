// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `select c, 1, 0` is exactly `zext c` (a boolean widened to the result type).

"builtin.module"() ({
  "func.func"() <{function_type = (i1) -> i64}> ({
  ^bb0(%c: i1):
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %r = "llvm.select"(%c, %one, %zero) : (i1, i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: arms are 2 and 0, not 1 and 0.
  "func.func"() <{function_type = (i1) -> i64}> ({
  ^bb0(%c: i1):
    %two = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %r = "llvm.select"(%c, %two, %zero) : (i1, i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// The select becomes a zext of the condition.
// CHECK:      ^{{.*}}(%[[C:.*]] : i1):
// CHECK:      %[[R:.*]] = "llvm.zext"(%[[C]]) : (i1) -> i64
// CHECK:      "func.return"(%[[R]]) : (i64) -> ()

// Non {1,0} arms: the select survives.
// CHECK:      ^{{.*}}(%[[NC:.*]] : i1):
// CHECK:      %[[NR:.*]] = "llvm.select"(%[[NC]],
// CHECK:      "func.return"(%[[NR]]) : (i64) -> ()
