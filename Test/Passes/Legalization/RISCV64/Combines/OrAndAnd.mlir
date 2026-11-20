// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// Distributing `or` through a shared masking `and`: `(X & Z) | (Y & Z)` equals `(X | Y) & Z`. Only fires when both inner `and`s share the same
// masking operand `Z`.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64, i64) -> i64, sym_name = "foo"}> ({
  ^bb0(%x: i64, %y: i64, %z: i64):
    %ax = "gmir.g_and"(%x, %z) : (i64, i64) -> i64
    %ay = "gmir.g_and"(%y, %z) : (i64, i64) -> i64
    %r = "gmir.g_or"(%ax, %ay) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: distinct masks, so the rule must not fire.
  "func.func"() <{function_type = (i64, i64, i64, i64) -> i64, sym_name = "bar"}> ({
  ^bb0(%x: i64, %y: i64, %z0: i64, %z1: i64):
    %ax = "gmir.g_and"(%x, %z0) : (i64, i64) -> i64
    %ay = "gmir.g_and"(%y, %z1) : (i64, i64) -> i64
    %r = "gmir.g_or"(%ax, %ay) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// The `or` now feeds a single masking `and`: (X or Y) & Z.
// CHECK:      func.func @foo(%[[X:.*]]: i64, %[[Y:.*]]: i64, %[[Z:.*]]: i64) -> i64 {
// CHECK:      %[[OUT:.*]] = "gmir.g_or"(%[[X]], %[[Y]]) : (i64, i64) -> i64
// CHECK-NEXT: %[[MASK:.*]] = "gmir.g_and"(%[[OUT]], %[[Z]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[MASK]]) : (i64) -> ()

// Distinct masks: nothing is combined.
// CHECK:      func.func @bar(%[[NX:.*]]: i64, %[[NY:.*]]: i64, %[[NZ0:.*]]: i64, %[[NZ1:.*]]: i64) -> i64 {
// CHECK:      %[[NAX:.*]] = "gmir.g_and"(%[[NX]], %[[NZ0]])
// CHECK:      %[[NAY:.*]] = "gmir.g_and"(%[[NY]], %[[NZ1]])
// CHECK:      %[[NR:.*]] = "gmir.g_or"(%[[NAX]], %[[NAY]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[NR]]) : (i64) -> ()
