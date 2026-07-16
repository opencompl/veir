// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// Distributing `or` through a shared masking `and`: `(X & Z) | (Y & Z)` equals `(X | Y) & Z`. Only fires when both inner `and`s share the same
// masking operand `Z`.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64, i64) -> i64, sym_name = "foo"}> ({
  ^bb0(%x: i64, %y: i64, %z: i64):
    %ax = "llvm.and"(%x, %z) : (i64, i64) -> i64
    %ay = "llvm.and"(%y, %z) : (i64, i64) -> i64
    %r = "llvm.or"(%ax, %ay) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: distinct masks, so the rule must not fire.
  "func.func"() <{function_type = (i64, i64, i64, i64) -> i64, sym_name = "bar"}> ({
  ^bb0(%x: i64, %y: i64, %z0: i64, %z1: i64):
    %ax = "llvm.and"(%x, %z0) : (i64, i64) -> i64
    %ay = "llvm.and"(%y, %z1) : (i64, i64) -> i64
    %r = "llvm.or"(%ax, %ay) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// The `or` now feeds a single masking `and`: (X or Y) & Z.
// CHECK:      ^{{.*}}(%[[X:.*]] : i64, %[[Y:.*]] : i64, %[[Z:.*]] : i64):
// CHECK:      %[[OUT:.*]] = "llvm.or"(%[[X]], %[[Y]]) : (i64, i64) -> i64
// CHECK-NEXT: %[[MASK:.*]] = "llvm.and"(%[[OUT]], %[[Z]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[MASK]]) : (i64) -> ()

// Distinct masks: nothing is combined.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i64, %[[NY:.*]] : i64, %[[NZ0:.*]] : i64, %[[NZ1:.*]] : i64):
// CHECK:      %[[NAX:.*]] = "llvm.and"(%[[NX]], %[[NZ0]])
// CHECK:      %[[NAY:.*]] = "llvm.and"(%[[NY]], %[[NZ1]])
// CHECK:      %[[NR:.*]] = "llvm.or"(%[[NAX]], %[[NAY]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[NR]]) : (i64) -> ()
