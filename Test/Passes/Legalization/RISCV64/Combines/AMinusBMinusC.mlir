// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// `A - (B - C)` is `A + (C - B)`: distributing the outer negation over the inner
// subtraction turns the nested subtract into an add of the swapped difference.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64, i64) -> i64, sym_name = "foo"}> ({
  ^bb0(%a: i64, %b: i64, %c: i64):
    %inner = "gmir.g_sub"(%b, %c) : (i64, i64) -> i64
    %r = "gmir.g_sub"(%a, %inner) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: the inner op is an add, not a sub, so the identity does not apply.
  "func.func"() <{function_type = (i64, i64, i64) -> i64, sym_name = "bar"}> ({
  ^bb0(%a: i64, %b: i64, %c: i64):
    %inner = "gmir.g_add"(%b, %c) : (i64, i64) -> i64
    %r = "gmir.g_sub"(%a, %inner) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// Rewritten to A + (C - B).
// CHECK:      func.func @foo(%[[A:.*]]: i64, %[[B:.*]]: i64, %[[C:.*]]: i64) -> i64 {
// CHECK:      %[[CMB:.*]] = "gmir.g_sub"(%[[C]], %[[B]]) : (i64, i64) -> i64
// CHECK:      %[[R:.*]] = "gmir.g_add"(%[[A]], %[[CMB]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[R]]) : (i64) -> ()

// Inner op is an add: the outer sub survives.
// CHECK:      func.func @bar(%[[NA:.*]]: i64, %[[NB:.*]]: i64, %[[NC:.*]]: i64) -> i64 {
// CHECK:      %[[NINNER:.*]] = "gmir.g_add"(%[[NB]], %[[NC]]) : (i64, i64) -> i64
// CHECK:      %[[NR:.*]] = "gmir.g_sub"(%[[NA]], %[[NINNER]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[NR]]) : (i64) -> ()
