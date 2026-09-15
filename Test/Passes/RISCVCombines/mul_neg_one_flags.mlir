// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// 1 * 255 is defined unsigned, but 0 - 1 underflows. Multiplication by all-ones
// can become negation only if nuw is dropped. Signed negation preserves nsw.
// overflowFlags: 1 = nsw (no signed wrap), 2 = nuw (no unsigned wrap), 3 = both.
"builtin.module"() ({
  "func.func"() <{sym_name = "mul_neg_one", function_type = (i8) -> (i8, i8, i8, i8)}> ({
  ^bb0(%x: i8):
    %unsigned = "llvm.mlir.constant"() <{value = 255 : i8}> : () -> i8
    %signed = "llvm.mlir.constant"() <{value = -1 : i8}> : () -> i8
    %a = "llvm.mul"(%x, %unsigned) <{overflowFlags = 2 : i32}> : (i8, i8) -> i8
    %b = "llvm.mul"(%x, %signed) <{overflowFlags = 2 : i32}> : (i8, i8) -> i8
    %c = "llvm.mul"(%x, %signed) <{overflowFlags = 1 : i32}> : (i8, i8) -> i8
    %d = "llvm.mul"(%x, %signed) <{overflowFlags = 3 : i32}> : (i8, i8) -> i8
    "func.return"(%a, %b, %c, %d) : (i8, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @mul_neg_one
// CHECK-SAME: (%[[X:.*]]: i8)
// CHECK-NEXT: %[[Z0:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i8}>
// CHECK-NEXT: %[[A:.*]] = "llvm.sub"(%[[Z0]], %[[X]]) : (i8, i8) -> i8
// CHECK-NEXT: %[[Z1:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i8}>
// CHECK-NEXT: %[[B:.*]] = "llvm.sub"(%[[Z1]], %[[X]]) : (i8, i8) -> i8
// CHECK-NEXT: %[[Z2:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i8}>
// CHECK-NEXT: %[[C:.*]] = "llvm.sub"(%[[Z2]], %[[X]]) <{"overflowFlags" = 1 : i32}> : (i8, i8) -> i8
// CHECK-NEXT: %[[Z3:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i8}>
// CHECK-NEXT: %[[D:.*]] = "llvm.sub"(%[[Z3]], %[[X]]) <{"overflowFlags" = 1 : i32}> : (i8, i8) -> i8
// CHECK-NEXT: "func.return"(%[[A]], %[[B]], %[[C]], %[[D]]) : (i8, i8, i8, i8) -> ()
