// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `0 - umax(X, 0 - X)` is `umin(X, 0 - X)`: the unsigned analogue of
// `SubSmaxSub`. The inner `0 - X` is rebuilt so the resulting `umin` consumes it
// directly.

"builtin.module"() ({
  "func.func"() <{function_type = (i64) -> i64, sym_name = "foo"}> ({
  ^bb0(%x: i64):
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %sub = "llvm.sub"(%zero, %x) : (i64, i64) -> i64
    %max = "llvm.intr.umax"(%x, %sub) : (i64, i64) -> i64
    %r = "llvm.sub"(%zero, %max) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: the outer subtrahend is 1, not 0, so the negation identity does not apply.
  "func.func"() <{function_type = (i64) -> i64, sym_name = "bar"}> ({
  ^bb0(%x: i64):
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %sub = "llvm.sub"(%zero, %x) : (i64, i64) -> i64
    %max = "llvm.intr.umax"(%x, %sub) : (i64, i64) -> i64
    %r = "llvm.sub"(%one, %max) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      ^{{.*}}(%[[X:.*]] : i64):
// CHECK-DAG:  %[[MIN:.*]] = "llvm.intr.umin"(%[[X]], %[[SUB:.*]]) : (i64, i64) -> i64
// CHECK-DAG:  %[[SUB]] = "llvm.sub"(%{{.*}}, %[[X]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[MIN]]) : (i64) -> ()

// Outer subtrahend is nonzero: the pattern does not fire, so no umin is produced.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i64):
// CHECK-NOT:  "llvm.intr.umin"
