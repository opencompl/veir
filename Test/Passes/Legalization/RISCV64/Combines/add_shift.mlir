// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// `A + shl(0 - B, C)` is `A - shl(B, C)`: negating before the shift then adding is
// the same as shifting then subtracting.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64, i64) -> i64, sym_name = "foo"}> ({
  ^bb0(%a: i64, %b: i64, %c: i64):
    %zero = "gmir.g_constant"() <{value = 0 : i64}> : () -> i64
    %negb = "gmir.g_sub"(%zero, %b) : (i64, i64) -> i64
    %sh = "gmir.g_shl"(%negb, %c) : (i64, i64) -> i64
    %r = "gmir.g_add"(%a, %sh) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: the shifted value is not a negation of anything (plain shl).
  "func.func"() <{function_type = (i64, i64, i64) -> i64, sym_name = "bar"}> ({
  ^bb0(%a: i64, %b: i64, %c: i64):
    %sh = "gmir.g_shl"(%b, %c) : (i64, i64) -> i64
    %r = "gmir.g_add"(%a, %sh) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// Rewritten to A - shl(B, C).
// CHECK:      func.func @foo(%[[A:.*]]: i64, %[[B:.*]]: i64, %[[C:.*]]: i64) -> i64 {
// CHECK:      %[[SH:.*]] = "gmir.g_shl"(%[[B]], %[[C]]) : (i64, i64) -> i64
// CHECK:      %[[R:.*]] = "gmir.g_sub"(%[[A]], %[[SH]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[R]]) : (i64) -> ()

// No negation: the add survives.
// CHECK:      func.func @bar(%[[NA:.*]]: i64, %[[NB:.*]]: i64, %[[NC:.*]]: i64) -> i64 {
// CHECK:      %[[NSH:.*]] = "gmir.g_shl"(%[[NB]], %[[NC]]) : (i64, i64) -> i64
// CHECK:      %[[NR:.*]] = "gmir.g_add"(%[[NA]], %[[NSH]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[NR]]) : (i64) -> ()
