// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `llvm.sub x x` is always zero, so (at the i64 width the combine fires on) it folds to a constant
// zero. If the operand is poison the result poison is refined by the concrete constant, so the
// rewrite is sound.

"builtin.module"() ({
  // Positive case: i64 `sub x x` folds to constant 0.
  "func.func"() <{function_type = (i64) -> i64}> ({
  ^bb0(%x: i64):
    %r = "llvm.sub"(%x, %x) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: distinct operands, so the rule must not fire.
  "func.func"() <{function_type = (i64, i64) -> i64}> ({
  ^bb0(%x: i64, %y: i64):
    %r = "llvm.sub"(%x, %y) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// The i64 `sub` is replaced by a constant zero; the operand is now dead.
// CHECK:      "func.func"() <{"function_type" = (i64) -> i64}>
// CHECK:      %[[Z:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i64}> : () -> i64
// CHECK-NEXT: "func.return"(%[[Z]]) : (i64) -> ()

// Distinct operands: the `sub` survives untouched.
// CHECK:      "func.func"() <{"function_type" = (i64, i64) -> i64}>
// CHECK:      ^{{.*}}(%[[DX:.*]] : i64, %[[DY:.*]] : i64):
// CHECK-NEXT: %[[DR:.*]] = "llvm.sub"(%[[DX]], %[[DY]]) : (i64, i64) -> i64
// CHECK-NEXT: "func.return"(%[[DR]]) : (i64) -> ()
