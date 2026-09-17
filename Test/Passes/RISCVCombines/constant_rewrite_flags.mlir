// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// Rewrites that replace an operation with an unrelated one must not hand its
// overflow flags to the replacement.
// overflowFlags: 1 = nsw (no signed wrap), 2 = nuw (no unsigned wrap), 3 = both.
"builtin.module"() ({
  "func.func"() <{sym_name = "constant_rewrite_flags", function_type = (i8, i8, i1, i1) -> (i8, i8, i8, i1, i1, i1, i8)}> ({
  ^bb0(%x: i8, %y: i8, %p: i1, %q: i1):
    %signed = "llvm.mlir.constant"() <{value = -1 : i8}> : () -> i8
    // Multiplication by all-ones becomes negation: 1 * 255 is defined unsigned,
    // but 0 - 1 underflows, so only nsw carries over.
    %mulNuw = "llvm.mul"(%x, %signed) <{overflowFlags = 2 : i32}> : (i8, i8) -> i8
    %mulNsw = "llvm.mul"(%x, %signed) <{overflowFlags = 1 : i32}> : (i8, i8) -> i8
    %mulBoth = "llvm.mul"(%x, %signed) <{overflowFlags = 3 : i32}> : (i8, i8) -> i8

    %true = "llvm.mlir.constant"() <{value = 1 : i1}> : () -> i1
    %narrow = "llvm.sub"(%p, %q) : (i1, i1) -> i1
    // At i1 the subtrahend is all-ones, so this is `sub x, -1` becoming
    // `add x, 1`: (1 - 0) - 1 is zero, but ~0 + 1 overflows both ways.
    %narrowNuw = "llvm.sub"(%narrow, %true) <{overflowFlags = 2 : i32}> : (i1, i1) -> i1
    %narrowNsw = "llvm.sub"(%narrow, %true) <{overflowFlags = 1 : i32}> : (i1, i1) -> i1
    %narrowBoth = "llvm.sub"(%narrow, %true) <{overflowFlags = 3 : i32}> : (i1, i1) -> i1

    %one = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    // (x - y) - 1 becomes (y ^ -1) + x. The unflagged inner subtraction may
    // wrap, so the addition can overflow where the outer subtraction did not:
    // (-128 - 1) - 1 is 126, but -128 + ~1 overflows signed arithmetic.
    %wide = "llvm.sub"(%x, %y) : (i8, i8) -> i8
    %wideBoth = "llvm.sub"(%wide, %one) <{overflowFlags = 3 : i32}> : (i8, i8) -> i8
    "func.return"(%mulNuw, %mulNsw, %mulBoth, %narrowNuw, %narrowNsw, %narrowBoth, %wideBoth) : (i8, i8, i8, i1, i1, i1, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @constant_rewrite_flags
// CHECK-SAME: (%[[X:.*]]: i8, %[[Y:.*]]: i8, %[[P:.*]]: i1, %[[Q:.*]]: i1)
// CHECK-NEXT: %[[Z0:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i8}>
// CHECK-NEXT: %[[M0:.*]] = "llvm.sub"(%[[Z0]], %[[X]]) : (i8, i8) -> i8
// CHECK-NEXT: %[[Z1:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i8}>
// CHECK-NEXT: %[[M1:.*]] = "llvm.sub"(%[[Z1]], %[[X]]) <{"overflowFlags" = 1 : i32}> : (i8, i8) -> i8
// CHECK-NEXT: %[[Z2:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i8}>
// CHECK-NEXT: %[[M2:.*]] = "llvm.sub"(%[[Z2]], %[[X]]) <{"overflowFlags" = 1 : i32}> : (i8, i8) -> i8
// CHECK-NEXT: %[[N:.*]] = "llvm.sub"(%[[P]], %[[Q]]) : (i1, i1) -> i1
// CHECK-NEXT: %[[O0:.*]] = "llvm.mlir.constant"() <{"value" = -1 : i1}>
// CHECK-NEXT: %[[N0:.*]] = "llvm.add"(%[[N]], %[[O0]]) : (i1, i1) -> i1
// CHECK-NEXT: %[[O1:.*]] = "llvm.mlir.constant"() <{"value" = -1 : i1}>
// CHECK-NEXT: %[[N1:.*]] = "llvm.add"(%[[N]], %[[O1]]) : (i1, i1) -> i1
// CHECK-NEXT: %[[O2:.*]] = "llvm.mlir.constant"() <{"value" = -1 : i1}>
// CHECK-NEXT: %[[N2:.*]] = "llvm.add"(%[[N]], %[[O2]]) : (i1, i1) -> i1
// CHECK-NEXT: %[[ONES:.*]] = "llvm.mlir.constant"() <{"value" = -1 : i8}>
// CHECK-NEXT: %[[XOR:.*]] = "llvm.xor"(%[[Y]], %[[ONES]]) : (i8, i8) -> i8
// CHECK-NEXT: %[[W:.*]] = "llvm.add"(%[[XOR]], %[[X]]) : (i8, i8) -> i8
// CHECK-NEXT: "func.return"(%[[M0]], %[[M1]], %[[M2]], %[[N0]], %[[N1]], %[[N2]], %[[W]]) : (i8, i8, i8, i1, i1, i1, i8) -> ()
