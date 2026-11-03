// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// `zext (zext x)` collapses to a single `zext x` to the outer width.

"builtin.module"() ({
  "func.func"() <{function_type = (i8) -> i64, sym_name = "foo"}> ({
  ^bb0(%x: i8):
    %z0 = "gmir.g_zext"(%x) : (i8) -> i32
    %z1 = "gmir.g_zext"(%z0) : (i32) -> i64
    "func.return"(%z1) : (i64) -> ()
  }) : () -> ()

  // Negative case: a single zext is left alone.
  "func.func"() <{function_type = (i8) -> i64, sym_name = "bar"}> ({
  ^bb0(%x: i8):
    %z = "gmir.g_zext"(%x) : (i8) -> i64
    "func.return"(%z) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// The two zexts collapse to one from i8 straight to i64.
// CHECK:      func.func @foo(%[[X:.*]]: i8) -> i64 {
// CHECK:      %[[Z:.*]] = "gmir.g_zext"(%[[X]]) : (i8) -> i64
// CHECK-NOT:  "gmir.g_zext"
// CHECK:      "func.return"(%[[Z]]) : (i64) -> ()

// Single zext unchanged.
// CHECK:      func.func @bar(%[[NX:.*]]: i8) -> i64 {
// CHECK:      %[[NZ:.*]] = "gmir.g_zext"(%[[NX]]) : (i8) -> i64
// CHECK:      "func.return"(%[[NZ]]) : (i64) -> ()
