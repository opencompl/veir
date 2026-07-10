// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `A - (B - C)` is `A + (C - B)`: distributing the outer negation over the inner
// subtraction turns the nested subtract into an add of the swapped difference.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64, i64) -> i64}> ({
  ^bb0(%a: i64, %b: i64, %c: i64):
    %inner = "llvm.sub"(%b, %c) : (i64, i64) -> i64
    %r = "llvm.sub"(%a, %inner) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: the inner op is an add, not a sub, so the identity does not apply.
  "func.func"() <{function_type = (i64, i64, i64) -> i64}> ({
  ^bb0(%a: i64, %b: i64, %c: i64):
    %inner = "llvm.add"(%b, %c) : (i64, i64) -> i64
    %r = "llvm.sub"(%a, %inner) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// Rewritten to A + (C - B).
// CHECK:      ^{{.*}}(%[[A:.*]] : i64, %[[B:.*]] : i64, %[[C:.*]] : i64):
// CHECK:      %[[CMB:.*]] = "llvm.sub"(%[[C]], %[[B]]) : (i64, i64) -> i64
// CHECK:      %[[R:.*]] = "llvm.add"(%[[A]], %[[CMB]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[R]]) : (i64) -> ()

// Inner op is an add: the outer sub survives.
// CHECK:      ^{{.*}}(%[[NA:.*]] : i64, %[[NB:.*]] : i64, %[[NC:.*]] : i64):
// CHECK:      %[[NINNER:.*]] = "llvm.add"(%[[NB]], %[[NC]]) : (i64, i64) -> i64
// CHECK:      %[[NR:.*]] = "llvm.sub"(%[[NA]], %[[NINNER]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[NR]]) : (i64) -> ()
