// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// Distributing `and` through a shared left shift: `(X << Z) & (Y << Z)` equals
// `(X & Y) << Z`, since shifting in identical zero bits commutes with a bitwise
// `and`. Only fires when both shift amounts are the same value `Z`.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64, i64) -> i64, sym_name = "foo"}> ({
  ^bb0(%x: i64, %y: i64, %z: i64):
    %sx = "gmir.g_shl"(%x, %z) : (i64, i64) -> i64
    %sy = "gmir.g_shl"(%y, %z) : (i64, i64) -> i64
    %r = "gmir.g_and"(%sx, %sy) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: distinct shift amounts, so the rule must not fire.
  "func.func"() <{function_type = (i64, i64, i64, i64) -> i64, sym_name = "bar"}> ({
  ^bb0(%x: i64, %y: i64, %z0: i64, %z1: i64):
    %sx = "gmir.g_shl"(%x, %z0) : (i64, i64) -> i64
    %sy = "gmir.g_shl"(%y, %z1) : (i64, i64) -> i64
    %r = "gmir.g_and"(%sx, %sy) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// The `and` now feeds a single shift: (X & Y) << Z.
// CHECK:      func.func @foo(%[[X:.*]]: i64, %[[Y:.*]]: i64, %[[Z:.*]]: i64) -> i64 {
// CHECK:      %[[AND:.*]] = "gmir.g_and"(%[[X]], %[[Y]]) : (i64, i64) -> i64
// CHECK-NEXT: %[[SHL:.*]] = "gmir.g_shl"(%[[AND]], %[[Z]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[SHL]]) : (i64) -> ()

// Distinct shift amounts: the two shifts and the outer `and` are untouched.
// CHECK:      func.func @bar(%[[NX:.*]]: i64, %[[NY:.*]]: i64, %[[NZ0:.*]]: i64, %[[NZ1:.*]]: i64) -> i64 {
// CHECK:      %[[NSX:.*]] = "gmir.g_shl"(%[[NX]], %[[NZ0]])
// CHECK:      %[[NSY:.*]] = "gmir.g_shl"(%[[NY]], %[[NZ1]])
// CHECK:      %[[NR:.*]] = "gmir.g_and"(%[[NSX]], %[[NSY]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[NR]]) : (i64) -> ()
