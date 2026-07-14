// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `(X != 0) | (Y != 0)` holds iff `(X | Y) != 0`, saving one comparison.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64) -> i1, sym_name = "foo"}> ({
  ^bb0(%x: i64, %y: i64):
    %z = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %cx = "llvm.icmp"(%x, %z) <{predicate = 1 : i64}> : (i64, i64) -> i1
    %cy = "llvm.icmp"(%y, %z) <{predicate = 1 : i64}> : (i64, i64) -> i1
    %r = "llvm.or"(%cx, %cy) : (i1, i1) -> i1
    "func.return"(%r) : (i1) -> ()
  }) : () -> ()

  // Negative case: comparisons are `eq`, not `ne`, so this rule does not apply.
  "func.func"() <{function_type = (i64, i64) -> i1, sym_name = "bar"}> ({
  ^bb0(%x: i64, %y: i64):
    %z = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %cx = "llvm.icmp"(%x, %z) <{predicate = 0 : i64}> : (i64, i64) -> i1
    %cy = "llvm.icmp"(%y, %z) <{predicate = 0 : i64}> : (i64, i64) -> i1
    %r = "llvm.or"(%cx, %cy) : (i1, i1) -> i1
    "func.return"(%r) : (i1) -> ()
  }) : () -> ()
}) : () -> ()

// Collapsed to (X | Y) != 0.
// CHECK:      ^{{.*}}(%[[X:.*]] : i64, %[[Y:.*]] : i64):
// CHECK:      %[[OR:.*]] = "llvm.or"(%[[X]], %[[Y]]) : (i64, i64) -> i64
// CHECK:      %[[Z:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i64}> : () -> i64
// CHECK:      %[[R:.*]] = "llvm.icmp"(%[[OR]], %[[Z]]) <{"predicate" = 1 : i64}> : (i64, i64) -> i1
// CHECK:      "func.return"(%[[R]]) : (i1) -> ()

// `eq` comparisons ored together: the `or` rule does not fire, so the original
// `or` of the two i1 comparison results survives (type (i1, i1) -> i1). Had the
// rule fired, the `or` would instead be over the i64 inputs.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i64, %[[NY:.*]] : i64):
// CHECK:      %[[NCX:.*]] = "llvm.icmp"(%[[NX]], %{{.*}}) <{"predicate" = 0 : i64}> : (i64, i64) -> i1
// CHECK:      %[[NCY:.*]] = "llvm.icmp"(%[[NY]], %{{.*}}) <{"predicate" = 0 : i64}> : (i64, i64) -> i1
// CHECK:      %[[NOR:.*]] = "llvm.or"(%[[NCX]], %[[NCY]]) : (i1, i1) -> i1
// CHECK:      "func.return"(%[[NOR]]) : (i1) -> ()
