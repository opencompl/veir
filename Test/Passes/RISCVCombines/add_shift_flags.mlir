// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// a + ((0 - b) << c) becomes a - (b << c), in either operand order. Neither the
// negation's nor the shift's overflow flags carry over to the replacements:
// 0 - 1 is defined with nsw while -128 - (1 << 1) is not, and -1 << 7 is defined
// with nsw while the replacement 1 << 7 is not. Both must be dropped.
// overflowFlags: 1 = nsw (no signed wrap), 2 = nuw (no unsigned wrap), 3 = both.
"builtin.module"() ({
  "func.func"() <{sym_name = "add_shift_flags", function_type = (i8, i8, i8) -> (i8, i8, i8, i8)}> ({
  ^bb0(%a: i8, %b: i8, %c: i8):
    %zero = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %neg = "llvm.sub"(%zero, %b) <{overflowFlags = 1 : i32}> : (i8, i8) -> i8
    %shift = "llvm.shl"(%neg, %c) : (i8, i8) -> i8
    %shiftFlagged = "llvm.shl"(%neg, %c) <{overflowFlags = 3 : i32}> : (i8, i8) -> i8
    %negFlags = "llvm.add"(%a, %shift) : (i8, i8) -> i8
    %negFlagsCommute = "llvm.add"(%shift, %a) : (i8, i8) -> i8
    %shiftFlags = "llvm.add"(%a, %shiftFlagged) : (i8, i8) -> i8
    %shiftFlagsCommute = "llvm.add"(%shiftFlagged, %a) : (i8, i8) -> i8
    "func.return"(%negFlags, %negFlagsCommute, %shiftFlags, %shiftFlagsCommute) : (i8, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @add_shift_flags
// CHECK-SAME: (%[[A:.*]]: i8, %[[B:.*]]: i8, %[[C:.*]]: i8)
// CHECK-NEXT: %[[S0:.*]] = "llvm.shl"(%[[B]], %[[C]]) : (i8, i8) -> i8
// CHECK-NEXT: %[[R0:.*]] = "llvm.sub"(%[[A]], %[[S0]]) : (i8, i8) -> i8
// CHECK-NEXT: %[[S1:.*]] = "llvm.shl"(%[[B]], %[[C]]) : (i8, i8) -> i8
// CHECK-NEXT: %[[R1:.*]] = "llvm.sub"(%[[A]], %[[S1]]) : (i8, i8) -> i8
// CHECK-NEXT: %[[S2:.*]] = "llvm.shl"(%[[B]], %[[C]]) : (i8, i8) -> i8
// CHECK-NEXT: %[[R2:.*]] = "llvm.sub"(%[[A]], %[[S2]]) : (i8, i8) -> i8
// CHECK-NEXT: %[[S3:.*]] = "llvm.shl"(%[[B]], %[[C]]) : (i8, i8) -> i8
// CHECK-NEXT: %[[R3:.*]] = "llvm.sub"(%[[A]], %[[S3]]) : (i8, i8) -> i8
// CHECK-NEXT: "func.return"(%[[R0]], %[[R1]], %[[R2]], %[[R3]]) : (i8, i8, i8, i8) -> ()
