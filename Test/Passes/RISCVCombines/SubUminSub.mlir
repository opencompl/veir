// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `0 - umin(X, 0 - X)` is `umax(X, 0 - X)`: the unsigned min input case of
// `simplify_neg_minmax`. The inner `0 - X` is rebuilt so the resulting `umax`
// consumes it directly.

"builtin.module"() ({
  "func.func"() <{function_type = (i64) -> i64}> ({
  ^bb0(%x: i64):
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %sub = "llvm.sub"(%zero, %x) : (i64, i64) -> i64
    %min = "llvm.intr.umin"(%x, %sub) : (i64, i64) -> i64
    %r = "llvm.sub"(%zero, %min) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: the min is `smin`, not `umin`, so the unsigned pattern does not fire.
  "func.func"() <{function_type = (i64) -> i64}> ({
  ^bb0(%x: i64):
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %sub = "llvm.sub"(%zero, %x) : (i64, i64) -> i64
    %min = "llvm.intr.smin"(%x, %sub) : (i64, i64) -> i64
    %r = "llvm.sub"(%zero, %min) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      ^{{.*}}(%[[X:.*]] : i64):
// CHECK-DAG:  %[[MAX:.*]] = "llvm.intr.umax"(%[[X]], %[[SUB:.*]]) : (i64, i64) -> i64
// CHECK-DAG:  %[[SUB]] = "llvm.sub"(%{{.*}}, %[[X]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[MAX]]) : (i64) -> ()

// Signed min: the unsigned pattern does not fire, so no umax is produced.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i64):
// CHECK-NOT:  "llvm.intr.umax"
