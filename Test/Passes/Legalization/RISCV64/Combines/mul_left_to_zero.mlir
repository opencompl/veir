// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// `mul 0, x` is `0`: multiplying by zero is always zero.

"builtin.module"() ({
  "func.func"() <{function_type = (i64) -> i64, sym_name = "foo"}> ({
  ^bb0(%x: i64):
    %zero = "gmir.g_constant"() <{value = 0 : i64}> : () -> i64
    %r = "gmir.g_mul"(%zero, %x) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: the left factor is 3, not 0, so the multiply is not eliminated.
  // (3 is not a power of two, so `mul_to_shl` does not fire either.)
  "func.func"() <{function_type = (i64) -> i64, sym_name = "bar"}> ({
  ^bb0(%x: i64):
    %three = "gmir.g_constant"() <{value = 3 : i64}> : () -> i64
    %r = "gmir.g_mul"(%three, %x) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// The multiply collapses to the zero constant, returned directly.
// CHECK:      func.func @foo(%[[X:.*]]: i64) -> i64 {
// CHECK:      %[[Z:.*]] = "gmir.g_constant"() <{"value" = 0 : i64}> : () -> i64
// CHECK-NOT:  "gmir.g_mul"
// CHECK:      "func.return"(%[[Z]]) : (i64) -> ()

// Left factor is nonzero: the mul survives, with the constant `3` moved to the right.
// CHECK:      func.func @bar(%[[NX:.*]]: i64) -> i64 {
// CHECK:      %[[NR:.*]] = "gmir.g_mul"(%[[NX]], %{{.*}}) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[NR]]) : (i64) -> ()
