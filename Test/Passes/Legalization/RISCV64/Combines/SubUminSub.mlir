// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// `0 - umin(X, 0 - X)` is `umax(X, 0 - X)`: the unsigned min input case of
// `simplify_neg_minmax`. The inner `0 - X` is rebuilt so the resulting `umax`
// consumes it directly.

"builtin.module"() ({
  "func.func"() <{function_type = (i64) -> i64, sym_name = "foo"}> ({
  ^bb0(%x: i64):
    %zero = "gmir.g_constant"() <{value = 0 : i64}> : () -> i64
    %sub = "gmir.g_sub"(%zero, %x) : (i64, i64) -> i64
    %min = "gmir.g_umin"(%x, %sub) : (i64, i64) -> i64
    %r = "gmir.g_sub"(%zero, %min) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: the min is `smin`, not `umin`, so the unsigned pattern does not fire.
  "func.func"() <{function_type = (i64) -> i64, sym_name = "bar"}> ({
  ^bb0(%x: i64):
    %zero = "gmir.g_constant"() <{value = 0 : i64}> : () -> i64
    %sub = "gmir.g_sub"(%zero, %x) : (i64, i64) -> i64
    %min = "gmir.g_smin"(%x, %sub) : (i64, i64) -> i64
    %r = "gmir.g_sub"(%zero, %min) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      func.func @foo(%[[X:.*]]: i64) -> i64 {
// CHECK-DAG:  %[[MAX:.*]] = "gmir.g_umax"(%[[X]], %[[SUB:.*]]) : (i64, i64) -> i64
// CHECK-DAG:  %[[SUB]] = "gmir.g_sub"(%{{.*}}, %[[X]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[MAX]]) : (i64) -> ()

// Signed min: the unsigned pattern does not fire, so no umax is produced.
// CHECK:      func.func @bar(%[[NX:.*]]: i64) -> i64 {
// CHECK-NOT:  "gmir.g_umax"
