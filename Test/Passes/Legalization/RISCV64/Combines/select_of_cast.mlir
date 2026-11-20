// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// `cast (c ? x : y)` is `c ? (cast x) : (cast y)` for `g_zext` and `g_trunc`, when the
// new `g_select` is legal.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i32, i32) -> i64, sym_name = "foo"}> ({
  ^bb0(%c: i64, %x: i32, %y: i32):
    %s = "gmir.g_select"(%c, %x, %y) : (i64, i32, i32) -> i32
    %r = "gmir.g_zext"(%s) : (i32) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: a `g_select` of `i32` values is not legal.
  "func.func"() <{function_type = (i64, i64, i64) -> i32, sym_name = "bar"}> ({
  ^bb0(%c: i64, %x: i64, %y: i64):
    %s = "gmir.g_select"(%c, %x, %y) : (i64, i64, i64) -> i64
    %r = "gmir.g_trunc"(%s) : (i64) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @foo
// CHECK-SAME:  (%[[C:.*]]: i64, %[[X:.*]]: i32, %[[Y:.*]]: i32)
// CHECK-DAG:   %[[ZX:.*]] = "gmir.g_zext"(%[[X]]) : (i32) -> i64
// CHECK-DAG:   %[[ZY:.*]] = "gmir.g_zext"(%[[Y]]) : (i32) -> i64
// CHECK:       %[[R:.*]] = "gmir.g_select"(%[[C]], %[[ZX]], %[[ZY]]) : (i64, i64, i64) -> i64
// CHECK-NEXT:  "func.return"(%[[R]]) : (i64) -> ()

// CHECK-LABEL: func.func @bar
// CHECK-SAME:  (%[[NC:.*]]: i64, %[[NX:.*]]: i64, %[[NY:.*]]: i64)
// CHECK-NEXT:  %[[S:.*]] = "gmir.g_select"(%[[NC]], %[[NX]], %[[NY]]) : (i64, i64, i64) -> i64
// CHECK-NEXT:  %[[T:.*]] = "gmir.g_trunc"(%[[S]]) : (i64) -> i32
// CHECK-NEXT:  "func.return"(%[[T]]) : (i32) -> ()
