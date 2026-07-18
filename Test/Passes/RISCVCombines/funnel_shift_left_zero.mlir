// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `fshl x, y, 0` is `x`: a funnel shift left by zero returns the high operand.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64) -> i64, sym_name = "foo"}> ({
  ^bb0(%x: i64, %y: i64):
    %z = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %r = "llvm.intr.fshl"(%x, %y, %z) : (i64, i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: the shift amount is nonzero, so the funnel shift stays.
  "func.func"() <{function_type = (i64, i64) -> i64, sym_name = "bar"}> ({
  ^bb0(%x: i64, %y: i64):
    %n = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %r = "llvm.intr.fshl"(%x, %y, %n) : (i64, i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// The funnel shift vanishes and x is returned.
// CHECK:      ^{{.*}}(%[[X:.*]] : i64, %[[Y:.*]] : i64):
// CHECK-NOT:  "llvm.intr.fshl"
// CHECK:      "func.return"(%[[X]]) : (i64) -> ()

// Nonzero amount: the funnel shift survives.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i64, %[[NY:.*]] : i64):
// CHECK:      %[[NR:.*]] = "llvm.intr.fshl"(%[[NX]], %[[NY]], %{{.*}}) : (i64, i64, i64) -> i64
// CHECK:      "func.return"(%[[NR]]) : (i64) -> ()
