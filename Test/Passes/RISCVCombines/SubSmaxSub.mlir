// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `0 - smax(X, 0 - X)` is `smin(X, 0 - X)`: negating the max of a value and its
// negation gives the min of the same pair. The inner `0 - X` is rebuilt so the
// resulting `smin` consumes it directly.

"builtin.module"() ({
  "func.func"() <{function_type = (i64) -> i64, sym_name = "foo"}> ({
  ^bb0(%x: i64):
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %sub = "llvm.sub"(%zero, %x) : (i64, i64) -> i64
    %max = "llvm.intr.smax"(%x, %sub) : (i64, i64) -> i64
    %r = "llvm.sub"(%zero, %max) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: the max is `umax`, not `smax`, so the signed pattern does not fire.
  "func.func"() <{function_type = (i64) -> i64, sym_name = "bar"}> ({
  ^bb0(%x: i64):
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %sub = "llvm.sub"(%zero, %x) : (i64, i64) -> i64
    %max = "llvm.intr.umax"(%x, %sub) : (i64, i64) -> i64
    %r = "llvm.sub"(%zero, %max) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      ^{{.*}}(%[[X:.*]] : i64):
// CHECK-DAG:  %[[MIN:.*]] = "llvm.intr.smin"(%[[X]], %[[SUB:.*]]) : (i64, i64) -> i64
// CHECK-DAG:  %[[SUB]] = "llvm.sub"(%{{.*}}, %[[X]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[MIN]]) : (i64) -> ()

// Unsigned max: the signed pattern does not fire, so no smin is produced.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i64):
// CHECK-NOT:  "llvm.intr.smin"
