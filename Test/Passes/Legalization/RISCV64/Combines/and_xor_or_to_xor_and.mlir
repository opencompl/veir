// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// `(X | Y) & ~Y` is `X & ~Y`: the `| Y` is redundant once `~Y` is and'd in.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64) -> i64, sym_name = "foo"}> ({
  ^bb0(%x: i64, %y: i64):
    %m1 = "gmir.g_constant"() <{value = -1 : i64}> : () -> i64
    %or = "gmir.g_or"(%x, %y) : (i64, i64) -> i64
    %noty = "gmir.g_xor"(%y, %m1) : (i64, i64) -> i64
    %r = "gmir.g_and"(%or, %noty) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: the xor constant is -2, not -1, so `noty` is not `~Y`.
  "func.func"() <{function_type = (i64, i64) -> i64, sym_name = "bar"}> ({
  ^bb0(%x: i64, %y: i64):
    %m2 = "gmir.g_constant"() <{value = -2 : i64}> : () -> i64
    %or = "gmir.g_or"(%x, %y) : (i64, i64) -> i64
    %noty = "gmir.g_xor"(%y, %m2) : (i64, i64) -> i64
    %r = "gmir.g_and"(%or, %noty) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// Rewritten to X & ~Y: the `and` now takes X directly, dropping the `or`.
// CHECK:      func.func @foo(%[[X:.*]]: i64, %[[Y:.*]]: i64) -> i64 {
// CHECK:      %[[NOTY:.*]] = "gmir.g_xor"(%[[Y]], %{{.*}}) : (i64, i64) -> i64
// CHECK:      %[[R:.*]] = "gmir.g_and"(%[[X]], %[[NOTY]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[R]]) : (i64) -> ()

// Not a real `~Y`: the `or` feeding the `and` survives.
// CHECK:      func.func @bar(%[[NX:.*]]: i64, %[[NY:.*]]: i64) -> i64 {
// CHECK:      %[[NOR:.*]] = "gmir.g_or"(%[[NX]], %[[NY]]) : (i64, i64) -> i64
// CHECK:      %[[NR:.*]] = "gmir.g_and"(%[[NOR]], %{{.*}}) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[NR]]) : (i64) -> ()
