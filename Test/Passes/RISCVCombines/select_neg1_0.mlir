// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `select c, -1, 0` is `sext c` (all-ones when true, zero when false).

"builtin.module"() ({
  "func.func"() <{function_type = (i1) -> i64}> ({
  ^bb0(%c: i1):
    %m1 = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> i64
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %r = "llvm.select"(%c, %m1, %zero) : (i1, i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: arms are 1 and 0, not -1 and 0 (that is select_1_0's shape).
  "func.func"() <{function_type = (i1) -> i64}> ({
  ^bb0(%c: i1):
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %r = "llvm.select"(%c, %one, %zero) : (i1, i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// The select becomes a sext of the condition.
// CHECK:      ^{{.*}}(%[[C:.*]] : i1):
// CHECK:      %[[R:.*]] = "llvm.sext"(%[[C]]) : (i1) -> i64
// CHECK:      "func.return"(%[[R]]) : (i64) -> ()

// Sibling-pattern check (not a no-op): `select c, 1, 0` is NOT this rule's shape,
// so `select_neg1_0` must not fire. The `select_1_0` rule handles it instead,
// yielding `zext c` -- crucially a `zext`, not the `sext` this rule emits.
// CHECK:      ^{{.*}}(%[[NC:.*]] : i1):
// CHECK:      %[[NR:.*]] = "llvm.zext"(%[[NC]]) : (i1) -> i64
// CHECK-NOT:  "llvm.sext"
// CHECK:      "func.return"(%[[NR]]) : (i64) -> ()
