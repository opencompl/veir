// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// The combines that read a select's condition as a boolean only match an `i1`
// condition: `(not c) ? x : y` is `c ? y : x`, and `c ? 1 : 0` is `c` at `i1`.

"builtin.module"() ({
  "func.func"() <{function_type = (i1, i64, i64) -> (i64, i1), sym_name = "foo"}> ({
  ^bb0(%c: i1, %x: i64, %y: i64):
    %ones = "gmir.g_constant"() <{value = -1 : i1}> : () -> i1
    %zero = "gmir.g_constant"() <{value = 0 : i1}> : () -> i1
    %nc = "gmir.g_xor"(%c, %ones) : (i1, i1) -> i1
    %swap = "gmir.g_select"(%nc, %x, %y) : (i1, i64, i64) -> i64
    %bool = "gmir.g_select"(%c, %ones, %zero) : (i1, i1, i1) -> i1
    "func.return"(%swap, %bool) : (i64, i1) -> ()
  }) : () -> ()

  // Negative case: an `i64` condition is true when it is nonzero, so `c ^ -1` is not
  // its negation.
  "func.func"() <{function_type = (i64, i64, i64) -> i64, sym_name = "bar"}> ({
  ^bb0(%c: i64, %x: i64, %y: i64):
    %ones = "gmir.g_constant"() <{value = -1 : i64}> : () -> i64
    %nc = "gmir.g_xor"(%c, %ones) : (i64, i64) -> i64
    %r = "gmir.g_select"(%nc, %x, %y) : (i64, i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative cases: the `g_zext` of an `i1` and the `g_xor` of `i1` that these would
  // become are not legal.
  "func.func"() <{function_type = (i1) -> (i64, i1), sym_name = "baz"}> ({
  ^bb0(%c: i1):
    %one = "gmir.g_constant"() <{value = 1 : i64}> : () -> i64
    %zero = "gmir.g_constant"() <{value = 0 : i64}> : () -> i64
    %t = "gmir.g_constant"() <{value = 1 : i1}> : () -> i1
    %f = "gmir.g_constant"() <{value = 0 : i1}> : () -> i1
    %zext = "gmir.g_select"(%c, %one, %zero) : (i1, i64, i64) -> i64
    %not = "gmir.g_select"(%c, %f, %t) : (i1, i1, i1) -> i1
    "func.return"(%zext, %not) : (i64, i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @foo
// CHECK-SAME:  (%[[C:.*]]: i1, %[[X:.*]]: i64, %[[Y:.*]]: i64)
// CHECK:       %[[SWAP:.*]] = "gmir.g_select"(%[[C]], %[[Y]], %[[X]]) : (i1, i64, i64) -> i64
// CHECK-NEXT:  "func.return"(%[[SWAP]], %[[C]]) : (i64, i1) -> ()

// CHECK-LABEL: func.func @bar
// CHECK-SAME:  (%[[NC:.*]]: i64, %[[NX:.*]]: i64, %[[NY:.*]]: i64)
// CHECK:       %[[NOT:.*]] = "gmir.g_xor"(%[[NC]], %{{.*}}) : (i64, i64) -> i64
// CHECK-NEXT:  %[[R:.*]] = "gmir.g_select"(%[[NOT]], %[[NX]], %[[NY]]) : (i64, i64, i64) -> i64
// CHECK-NEXT:  "func.return"(%[[R]]) : (i64) -> ()

// CHECK-LABEL: func.func @baz
// CHECK:       %[[ZEXT:.*]] = "gmir.g_select"(
// CHECK:       %[[NOTR:.*]] = "gmir.g_select"(
// CHECK-NEXT:  "func.return"(%[[ZEXT]], %[[NOTR]]) : (i64, i1) -> ()
