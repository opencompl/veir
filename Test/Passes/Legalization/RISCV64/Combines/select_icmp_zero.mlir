// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// A `g_select` condition is true when nonzero, so comparing it against zero is redundant:
// `(v != 0) ? x : y` -> `v ? x : y` and `(v == 0) ? x : y` -> `v ? y : x`.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64, i64) -> i64, sym_name = "ne"}> ({
  ^bb0(%v: i64, %x: i64, %y: i64):
    %zero = "gmir.g_constant"() <{value = 0 : i64}> : () -> i64
    %c = "gmir.g_icmp"(%v, %zero) <{"predicate" = 1 : i64}> : (i64, i64) -> i64
    %r = "gmir.g_select"(%c, %x, %y) : (i64, i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (i64, i64, i64) -> i64, sym_name = "eq"}> ({
  ^bb0(%v: i64, %x: i64, %y: i64):
    %zero = "gmir.g_constant"() <{value = 0 : i64}> : () -> i64
    %c = "gmir.g_icmp"(%v, %zero) <{"predicate" = 0 : i64}> : (i64, i64) -> i64
    %r = "gmir.g_select"(%c, %x, %y) : (i64, i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      func.func @ne(%[[V:.*]]: i64, %[[X:.*]]: i64, %[[Y:.*]]: i64) -> i64 {
// CHECK:      "gmir.g_select"(%[[V]], %[[X]], %[[Y]])
// CHECK:      func.func @eq(%[[V2:.*]]: i64, %[[X2:.*]]: i64, %[[Y2:.*]]: i64) -> i64 {
// CHECK:      "gmir.g_select"(%[[V2]], %[[Y2]], %[[X2]])
