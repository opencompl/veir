// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// `(x pred y) ? x : y` is a min or max of `x` and `y`. The compared operands must be
// the select's arms, and the min or max must be legal for the type.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64) -> (i64, i64, i64, i64), sym_name = "foo"}> ({
  ^bb0(%x: i64, %y: i64):
    %ugt = "gmir.g_icmp"(%x, %y) <{predicate = 8 : i64}> : (i64, i64) -> i64
    %sge = "gmir.g_icmp"(%x, %y) <{predicate = 5 : i64}> : (i64, i64) -> i64
    %ult = "gmir.g_icmp"(%x, %y) <{predicate = 6 : i64}> : (i64, i64) -> i64
    %sle = "gmir.g_icmp"(%x, %y) <{predicate = 3 : i64}> : (i64, i64) -> i64
    %umax = "gmir.g_select"(%ugt, %x, %y) : (i64, i64, i64) -> i64
    %smax = "gmir.g_select"(%sge, %x, %y) : (i64, i64, i64) -> i64
    %umin = "gmir.g_select"(%ult, %x, %y) : (i64, i64, i64) -> i64
    %smin = "gmir.g_select"(%sle, %x, %y) : (i64, i64, i64) -> i64
    "func.return"(%umax, %smax, %umin, %smin) : (i64, i64, i64, i64) -> ()
  }) : () -> ()

  // Negative case: the compared operands are not the select's arms.
  "func.func"() <{function_type = (i64, i64, i64) -> i64, sym_name = "bar"}> ({
  ^bb0(%x: i64, %y: i64, %z: i64):
    %c = "gmir.g_icmp"(%x, %y) <{predicate = 8 : i64}> : (i64, i64) -> i64
    %r = "gmir.g_select"(%c, %x, %z) : (i64, i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: `g_umax` is not legal for `i32`.
  "func.func"() <{function_type = (i32, i32) -> i32, sym_name = "baz"}> ({
  ^bb0(%x: i32, %y: i32):
    %c = "gmir.g_icmp"(%x, %y) <{predicate = 8 : i64}> : (i32, i32) -> i64
    %r = "gmir.g_select"(%c, %x, %y) : (i64, i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @foo
// CHECK-SAME:  (%[[X:.*]]: i64, %[[Y:.*]]: i64)
// CHECK-DAG:   %[[UMAX:.*]] = "gmir.g_umax"(%[[X]], %[[Y]]) : (i64, i64) -> i64
// CHECK-DAG:   %[[SMAX:.*]] = "gmir.g_smax"(%[[X]], %[[Y]]) : (i64, i64) -> i64
// CHECK-DAG:   %[[UMIN:.*]] = "gmir.g_umin"(%[[X]], %[[Y]]) : (i64, i64) -> i64
// CHECK-DAG:   %[[SMIN:.*]] = "gmir.g_smin"(%[[X]], %[[Y]]) : (i64, i64) -> i64
// CHECK-NOT:   "gmir.g_select"
// CHECK:       "func.return"(%[[UMAX]], %[[SMAX]], %[[UMIN]], %[[SMIN]])

// CHECK-LABEL: func.func @bar
// CHECK:       %[[R:.*]] = "gmir.g_select"(
// CHECK-NEXT:  "func.return"(%[[R]]) : (i64) -> ()

// CHECK-LABEL: func.func @baz
// CHECK:       %[[R:.*]] = "gmir.g_select"(
// CHECK-NEXT:  "func.return"(%[[R]]) : (i32) -> ()
