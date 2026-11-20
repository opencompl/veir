// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// `or (and x, y), x` is `x` (absorption law): the `and x, y` is subsumed by x.
// Here the `and` is the LEFT operand of the `or`.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64) -> i64, sym_name = "foo"}> ({
  ^bb0(%x: i64, %y: i64):
    %and = "gmir.g_and"(%x, %y) : (i64, i64) -> i64
    %r = "gmir.g_or"(%and, %x) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: neither `and` operand is the other `or` operand, so no absorption.
  "func.func"() <{function_type = (i64, i64, i64) -> i64, sym_name = "bar"}> ({
  ^bb0(%x: i64, %y: i64, %z: i64):
    %and = "gmir.g_and"(%x, %y) : (i64, i64) -> i64
    %r = "gmir.g_or"(%and, %z) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// The or/and collapse to x, which is returned directly.
// CHECK:      func.func @foo(%[[X:.*]]: i64, %[[Y:.*]]: i64) -> i64 {
// CHECK-NOT:  "gmir.g_or"
// CHECK:      "func.return"(%[[X]]) : (i64) -> ()

// No shared operand: the or/and survive.
// CHECK:      func.func @bar(%[[NX:.*]]: i64, %[[NY:.*]]: i64, %[[NZ:.*]]: i64) -> i64 {
// CHECK:      %[[NAND:.*]] = "gmir.g_and"(%[[NX]], %[[NY]]) : (i64, i64) -> i64
// CHECK:      %[[NR:.*]] = "gmir.g_or"(%[[NAND]], %[[NZ]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[NR]]) : (i64) -> ()
