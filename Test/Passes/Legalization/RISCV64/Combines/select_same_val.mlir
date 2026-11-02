// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// `c ? x : x` is `x`, and a select of a constant condition picks an arm: a nonzero
// condition is true, so `2 ? x : y` is `x`, and `0 ? x : y` is `y`.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64, i64) -> (i64, i64, i64), sym_name = "foo"}> ({
  ^bb0(%c: i64, %x: i64, %y: i64):
    %two = "gmir.g_constant"() <{value = 2 : i64}> : () -> i64
    %zero = "gmir.g_constant"() <{value = 0 : i64}> : () -> i64
    %same = "gmir.g_select"(%c, %x, %x) : (i64, i64, i64) -> i64
    %true = "gmir.g_select"(%two, %x, %y) : (i64, i64, i64) -> i64
    %false = "gmir.g_select"(%zero, %x, %y) : (i64, i64, i64) -> i64
    "func.return"(%same, %true, %false) : (i64, i64, i64) -> ()
  }) : () -> ()

  // Negative case: the condition is not a constant and the arms differ.
  "func.func"() <{function_type = (i64, i64, i64) -> i64, sym_name = "bar"}> ({
  ^bb0(%c: i64, %x: i64, %y: i64):
    %r = "gmir.g_select"(%c, %x, %y) : (i64, i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @foo
// CHECK-SAME:  (%{{.*}}: i64, %[[X:.*]]: i64, %[[Y:.*]]: i64)
// CHECK-NOT:   "gmir.g_select"
// CHECK:       "func.return"(%[[X]], %[[X]], %[[Y]]) : (i64, i64, i64) -> ()

// CHECK-LABEL: func.func @bar
// CHECK-SAME:  (%[[C:.*]]: i64, %[[NX:.*]]: i64, %[[NY:.*]]: i64)
// CHECK-NEXT:  %[[R:.*]] = "gmir.g_select"(%[[C]], %[[NX]], %[[NY]]) : (i64, i64, i64) -> i64
// CHECK-NEXT:  "func.return"(%[[R]]) : (i64) -> ()
