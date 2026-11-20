// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// `(X != 0) | (Y != 0)` holds iff `(X | Y) != 0`, saving one comparison.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64) -> i1, sym_name = "foo"}> ({
  ^bb0(%x: i64, %y: i64):
    %z = "gmir.g_constant"() <{value = 0 : i64}> : () -> i64
    %cx = "gmir.g_icmp"(%x, %z) <{predicate = 1 : i64}> : (i64, i64) -> i1
    %cy = "gmir.g_icmp"(%y, %z) <{predicate = 1 : i64}> : (i64, i64) -> i1
    %r = "gmir.g_or"(%cx, %cy) : (i1, i1) -> i1
    "func.return"(%r) : (i1) -> ()
  }) : () -> ()

  // Negative case: comparisons are `eq`, not `ne`, so this rule does not apply.
  "func.func"() <{function_type = (i64, i64) -> i1, sym_name = "bar"}> ({
  ^bb0(%x: i64, %y: i64):
    %z = "gmir.g_constant"() <{value = 0 : i64}> : () -> i64
    %cx = "gmir.g_icmp"(%x, %z) <{predicate = 0 : i64}> : (i64, i64) -> i1
    %cy = "gmir.g_icmp"(%y, %z) <{predicate = 0 : i64}> : (i64, i64) -> i1
    %r = "gmir.g_or"(%cx, %cy) : (i1, i1) -> i1
    "func.return"(%r) : (i1) -> ()
  }) : () -> ()
}) : () -> ()

// Collapsed to (X | Y) != 0.
// CHECK:      func.func @foo(%[[X:.*]]: i64, %[[Y:.*]]: i64) -> i1 {
// CHECK:      %[[Z:.*]] = "gmir.g_constant"() <{"value" = 0 : i64}> : () -> i64
// CHECK:      %[[OR:.*]] = "gmir.g_or"(%[[X]], %[[Y]]) : (i64, i64) -> i64
// CHECK:      %[[R:.*]] = "gmir.g_icmp"(%[[OR]], %[[Z]]) <{"predicate" = 1 : i64}> : (i64, i64) -> i1
// CHECK:      "func.return"(%[[R]]) : (i1) -> ()

// `eq` comparisons ored together: the `or` rule does not fire, so the original
// `or` of the two i1 comparison results survives (type (i1, i1) -> i1). Had the
// rule fired, the `or` would instead be over the i64 inputs.
// CHECK:      func.func @bar(%[[NX:.*]]: i64, %[[NY:.*]]: i64) -> i1 {
// CHECK:      %[[NCX:.*]] = "gmir.g_icmp"(%[[NX]], %{{.*}}) <{"predicate" = 0 : i64}> : (i64, i64) -> i1
// CHECK:      %[[NCY:.*]] = "gmir.g_icmp"(%[[NY]], %{{.*}}) <{"predicate" = 0 : i64}> : (i64, i64) -> i1
// CHECK:      %[[NOR:.*]] = "gmir.g_or"(%[[NCX]], %[[NCY]]) : (i1, i1) -> i1
// CHECK:      "func.return"(%[[NOR]]) : (i1) -> ()
