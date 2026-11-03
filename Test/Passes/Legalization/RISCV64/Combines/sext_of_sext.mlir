// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// `sext (sext x)` collapses to a single `sext x` to the outer width.

"builtin.module"() ({
  "func.func"() <{function_type = (i8) -> i64, sym_name = "foo"}> ({
  ^bb0(%x: i8):
    %s0 = "gmir.g_sext"(%x) : (i8) -> i32
    %s1 = "gmir.g_sext"(%s0) : (i32) -> i64
    "func.return"(%s1) : (i64) -> ()
  }) : () -> ()

  // Negative case: a single sext is left alone.
  "func.func"() <{function_type = (i8) -> i64, sym_name = "bar"}> ({
  ^bb0(%x: i8):
    %s = "gmir.g_sext"(%x) : (i8) -> i64
    "func.return"(%s) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// The two sexts collapse to one from i8 straight to i64.
// CHECK:      func.func @foo(%[[X:.*]]: i8) -> i64 {
// CHECK:      %[[S:.*]] = "gmir.g_sext"(%[[X]]) : (i8) -> i64
// CHECK-NOT:  "gmir.g_sext"
// CHECK:      "func.return"(%[[S]]) : (i64) -> ()

// Single sext unchanged.
// CHECK:      func.func @bar(%[[NX:.*]]: i8) -> i64 {
// CHECK:      %[[NS:.*]] = "gmir.g_sext"(%[[NX]]) : (i8) -> i64
// CHECK:      "func.return"(%[[NS]]) : (i64) -> ()
