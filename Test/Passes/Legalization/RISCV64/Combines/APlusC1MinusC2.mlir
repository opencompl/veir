// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// (A + C1) - C2 → A + (C1 - C2): when both offsets are constants, the two
// constant adjustments to A collapse into a single add of their difference.

"builtin.module"() ({
  "func.func"() <{function_type = (i64) -> i64, sym_name = "foo"}> ({
  ^bb0(%a: i64):
    %c1 = "gmir.g_constant"() <{value = 10 : i64}> : () -> i64
    %c2 = "gmir.g_constant"() <{value = 3 : i64}> : () -> i64
    %add = "gmir.g_add"(%a, %c1) : (i64, i64) -> i64
    %r = "gmir.g_sub"(%add, %c2) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: the subtracted operand is not a constant, so no fold.
  "func.func"() <{function_type = (i64, i64) -> i64, sym_name = "bar"}> ({
  ^bb0(%a: i64, %y: i64):
    %c1 = "gmir.g_constant"() <{value = 10 : i64}> : () -> i64
    %add = "gmir.g_add"(%a, %c1) : (i64, i64) -> i64
    %r = "gmir.g_sub"(%add, %y) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: the added operand is not a constant, so no fold.
  "func.func"() <{function_type = (i64, i64) -> i64, sym_name = "baz"}> ({
  ^bb0(%a: i64, %x: i64):
    %c2 = "gmir.g_constant"() <{value = 3 : i64}> : () -> i64
    %add = "gmir.g_add"(%a, %x) : (i64, i64) -> i64
    %r = "gmir.g_sub"(%add, %c2) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// Folds to A + (10 - 3) = A + 7.
// CHECK:      func.func @foo(%[[A:.*]]: i64) -> i64 {
// CHECK:      %[[C:.*]] = "gmir.g_constant"(){{.*}}value{{.*}}= 7 : i64{{.*}} : () -> i64
// CHECK:      %[[R:.*]] = "gmir.g_add"(%[[A]], %[[C]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[R]]) : (i64) -> ()

// Non-constant subtrahend: the pattern does not fire.
// CHECK:      func.func @bar(%[[NA:.*]]: i64, %[[NY:.*]]: i64) -> i64 {
// CHECK:      %[[NADD:.*]] = "gmir.g_add"(%[[NA]], %{{.*}}) : (i64, i64) -> i64
// CHECK:      %[[NR:.*]] = "gmir.g_sub"(%[[NADD]], %[[NY]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[NR]]) : (i64) -> ()

// Non-constant addend: `APlusC1MinusC2` does not fire, but `sub_to_add` rewrites `(A + X) - 3`
// into `(A + X) + (-3)`.
// CHECK:      func.func @baz(%[[MA:.*]]: i64, %[[MX:.*]]: i64) -> i64 {
// CHECK:      %[[MADD:.*]] = "gmir.g_add"(%[[MA]], %[[MX]]) : (i64, i64) -> i64
// CHECK:      %[[MC:.*]] = "gmir.g_constant"() <{"value" = -3 : i64}> : () -> i64
// CHECK:      %[[MR:.*]] = "gmir.g_add"(%[[MADD]], %[[MC]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[MR]]) : (i64) -> ()
