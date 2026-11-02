// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// `0 - smin(X, 0 - X)` is `smax(X, 0 - X)`: negating the min of a value and its
// negation gives the max of the same pair. This is the smin input case of
// `simplify_neg_minmax`; the inner `0 - X` is rebuilt so the resulting `smax`
// consumes it directly.

"builtin.module"() ({
  "func.func"() <{function_type = (i64) -> i64, sym_name = "foo"}> ({
  ^bb0(%x: i64):
    %zero = "gmir.g_constant"() <{value = 0 : i64}> : () -> i64
    %sub = "gmir.g_sub"(%zero, %x) : (i64, i64) -> i64
    %min = "gmir.g_smin"(%x, %sub) : (i64, i64) -> i64
    %r = "gmir.g_sub"(%zero, %min) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: the min is `umin`, not `smin`, so the signed pattern does not fire.
  "func.func"() <{function_type = (i64) -> i64, sym_name = "bar"}> ({
  ^bb0(%x: i64):
    %zero = "gmir.g_constant"() <{value = 0 : i64}> : () -> i64
    %sub = "gmir.g_sub"(%zero, %x) : (i64, i64) -> i64
    %min = "gmir.g_umin"(%x, %sub) : (i64, i64) -> i64
    %r = "gmir.g_sub"(%zero, %min) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      func.func @foo(%[[X:.*]]: i64) -> i64 {
// CHECK-DAG:  %[[MAX:.*]] = "gmir.g_smax"(%[[X]], %[[SUB:.*]]) : (i64, i64) -> i64
// CHECK-DAG:  %[[SUB]] = "gmir.g_sub"(%{{.*}}, %[[X]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[MAX]]) : (i64) -> ()

// Unsigned min: the signed pattern does not fire, so no smax is produced.
// CHECK:      func.func @bar(%[[NX:.*]]: i64) -> i64 {
// CHECK-NOT:  "gmir.g_smax"
