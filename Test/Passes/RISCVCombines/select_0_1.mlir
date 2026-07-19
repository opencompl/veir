// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `select c, 0, 1` is `zext (not c)`: the condition is inverted, then widened.

"builtin.module"() ({
  "func.func"() <{function_type = (i1) -> i64, sym_name = "foo"}> ({
  ^bb0(%c: i1):
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %r = "llvm.select"(%c, %zero, %one) : (i1, i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: arms are 0 and 2, not 0 and 1.
  "func.func"() <{function_type = (i1) -> i64, sym_name = "bar"}> ({
  ^bb0(%c: i1):
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %two = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %r = "llvm.select"(%c, %zero, %two) : (i1, i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// The select becomes zext(not c).
// CHECK:      ^{{.*}}(%[[C:.*]] : i1):
// CHECK:      %[[M1:.*]] = "llvm.mlir.constant"() <{"value" = -1 : i1}> : () -> i1
// CHECK:      %[[NOT:.*]] = "llvm.xor"(%[[C]], %[[M1]]) : (i1, i1) -> i1
// CHECK:      %[[R:.*]] = "llvm.zext"(%[[NOT]]) : (i1) -> i64
// CHECK:      "func.return"(%[[R]]) : (i64) -> ()

// Non {0,1} arms: the select survives.
// CHECK:      ^{{.*}}(%[[NC:.*]] : i1):
// CHECK:      %[[NR:.*]] = "llvm.select"(%[[NC]],
// CHECK:      "func.return"(%[[NR]]) : (i64) -> ()
