// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// Distributing `and` through a shared arithmetic right shift: `(X >> Z) & (Y >> Z)` equals `(X & Y) >> Z` (the replicated sign bits agree bit-by-bit). Only fires when both arithmetic right shifts share the same
// second operand `Z`.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64, i64) -> i64, sym_name = "foo"}> ({
  ^bb0(%x: i64, %y: i64, %z: i64):
    %sx = "llvm.ashr"(%x, %z) : (i64, i64) -> i64
    %sy = "llvm.ashr"(%y, %z) : (i64, i64) -> i64
    %r = "llvm.and"(%sx, %sy) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: distinct second operands, so the rule must not fire.
  "func.func"() <{function_type = (i64, i64, i64, i64) -> i64, sym_name = "bar"}> ({
  ^bb0(%x: i64, %y: i64, %z0: i64, %z1: i64):
    %sx = "llvm.ashr"(%x, %z0) : (i64, i64) -> i64
    %sy = "llvm.ashr"(%y, %z1) : (i64, i64) -> i64
    %r = "llvm.and"(%sx, %sy) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// The `and` now feeds a single `ashr`.
// CHECK:      ^{{.*}}(%[[X:.*]] : i64, %[[Y:.*]] : i64, %[[Z:.*]] : i64):
// CHECK:      %[[OUT:.*]] = "llvm.and"(%[[X]], %[[Y]]) : (i64, i64) -> i64
// CHECK-NEXT: %[[SH:.*]] = "llvm.ashr"(%[[OUT]], %[[Z]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[SH]]) : (i64) -> ()

// Distinct second operands: nothing is combined.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i64, %[[NY:.*]] : i64, %[[NZ0:.*]] : i64, %[[NZ1:.*]] : i64):
// CHECK:      %[[NSX:.*]] = "llvm.ashr"(%[[NX]], %[[NZ0]])
// CHECK:      %[[NSY:.*]] = "llvm.ashr"(%[[NY]], %[[NZ1]])
// CHECK:      %[[NR:.*]] = "llvm.and"(%[[NSX]], %[[NSY]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[NR]]) : (i64) -> ()
