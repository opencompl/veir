// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// Distributing `or` through a shared logical right shift: `(X >> Z) | (Y >> Z)` equals `(X | Y) >> Z`. Only fires when both logical right shifts share the same
// second operand `Z`.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64, i64) -> i64}> ({
  ^bb0(%x: i64, %y: i64, %z: i64):
    %sx = "llvm.lshr"(%x, %z) : (i64, i64) -> i64
    %sy = "llvm.lshr"(%y, %z) : (i64, i64) -> i64
    %r = "llvm.or"(%sx, %sy) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: distinct second operands, so the rule must not fire.
  "func.func"() <{function_type = (i64, i64, i64, i64) -> i64}> ({
  ^bb0(%x: i64, %y: i64, %z0: i64, %z1: i64):
    %sx = "llvm.lshr"(%x, %z0) : (i64, i64) -> i64
    %sy = "llvm.lshr"(%y, %z1) : (i64, i64) -> i64
    %r = "llvm.or"(%sx, %sy) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// The `or` now feeds a single `lshr`.
// CHECK:      ^{{.*}}(%[[X:.*]] : i64, %[[Y:.*]] : i64, %[[Z:.*]] : i64):
// CHECK:      %[[OUT:.*]] = "llvm.or"(%[[X]], %[[Y]]) : (i64, i64) -> i64
// CHECK-NEXT: %[[SH:.*]] = "llvm.lshr"(%[[OUT]], %[[Z]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[SH]]) : (i64) -> ()

// Distinct second operands: nothing is combined.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i64, %[[NY:.*]] : i64, %[[NZ0:.*]] : i64, %[[NZ1:.*]] : i64):
// CHECK:      %[[NSX:.*]] = "llvm.lshr"(%[[NX]], %[[NZ0]])
// CHECK:      %[[NSY:.*]] = "llvm.lshr"(%[[NY]], %[[NZ1]])
// CHECK:      %[[NR:.*]] = "llvm.or"(%[[NSX]], %[[NSY]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[NR]]) : (i64) -> ()
