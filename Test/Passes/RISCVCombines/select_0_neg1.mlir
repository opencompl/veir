// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `select c, 0, -1` is `sext (not c)`: invert the condition, then sign-extend.

"builtin.module"() ({
  "func.func"() <{function_type = (i1) -> i64, sym_name = "foo"}> ({
  ^bb0(%c: i1):
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %m1 = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> i64
    %r = "llvm.select"(%c, %zero, %m1) : (i1, i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: arms are 0 and 1, so this is select_0_1's shape (zext), not sext.
  "func.func"() <{function_type = (i1) -> i64, sym_name = "bar"}> ({
  ^bb0(%c: i1):
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %r = "llvm.select"(%c, %zero, %one) : (i1, i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// The select becomes sext(not c).
// CHECK:      ^{{.*}}(%[[C:.*]] : i1):
// CHECK:      %[[M1:.*]] = "llvm.mlir.constant"() <{"value" = -1 : i1}> : () -> i1
// CHECK:      %[[NOT:.*]] = "llvm.xor"(%[[C]], %[[M1]]) : (i1, i1) -> i1
// CHECK:      %[[R:.*]] = "llvm.sext"(%[[NOT]]) : (i1) -> i64
// CHECK:      "func.return"(%[[R]]) : (i64) -> ()

// Sibling-pattern check (not a no-op): `select c, 0, 1` is NOT this rule's shape,
// so `select_0_neg1` must not fire. The `select_0_1` rule handles it instead,
// yielding `zext (not c)` -- crucially a `zext`, not the `sext` this rule emits.
// CHECK:      ^{{.*}}(%[[NC:.*]] : i1):
// CHECK:      %[[NNOT:.*]] = "llvm.xor"(%[[NC]], %{{.*}}) : (i1, i1) -> i1
// CHECK:      %[[NR:.*]] = "llvm.zext"(%[[NNOT]]) : (i1) -> i64
// CHECK-NOT:  "llvm.sext"
// CHECK:      "func.return"(%[[NR]]) : (i64) -> ()
