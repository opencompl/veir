// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// `ashr 0, x` is `0`: arithmetically shifting zero right by any amount is still zero.

"builtin.module"() ({
  "func.func"() <{function_type = (i64) -> i64, sym_name = "foo"}> ({
  ^bb0(%x: i64):
    %zero = "gmir.g_constant"() <{value = 0 : i64}> : () -> i64
    %r = "gmir.g_ashr"(%zero, %x) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: the shifted value is 1, not 0, so the shift is not eliminated.
  "func.func"() <{function_type = (i64) -> i64, sym_name = "bar"}> ({
  ^bb0(%x: i64):
    %one = "gmir.g_constant"() <{value = 1 : i64}> : () -> i64
    %r = "gmir.g_ashr"(%one, %x) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// The shift collapses to the zero constant, returned directly.
// CHECK:      func.func @foo(%[[X:.*]]: i64) -> i64 {
// CHECK:      %[[Z:.*]] = "gmir.g_constant"() <{"value" = 0 : i64}> : () -> i64
// CHECK-NOT:  "gmir.g_ashr"
// CHECK:      "func.return"(%[[Z]]) : (i64) -> ()

// Shifted value is nonzero: the ashr survives.
// CHECK:      func.func @bar(%[[NX:.*]]: i64) -> i64 {
// CHECK:      %[[NR:.*]] = "gmir.g_ashr"(%{{.*}}, %[[NX]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[NR]]) : (i64) -> ()
