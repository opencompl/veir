// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// a + ((0 - b) << c) becomes a - (b << c), in either operand order. Neither the
// negation's nor the shift's overflow flags carry over to the replacements:
// 0 - 1 is defined with nsw while -128 - (1 << 1) is not, and -1 << 7 is defined
// with nsw while the replacement 1 << 7 is not. Both must be dropped.
// overflowFlags: 1 = nsw (no signed wrap), 2 = nuw (no unsigned wrap), 3 = both.
"builtin.module"() ({
  "func.func"() <{sym_name = "add_shift_flags", function_type = (i8, i8, i8) -> (i8, i8, i8, i8)}> ({
  ^bb0(%a: i8, %b: i8, %c: i8):
    %zero = "gmir.g_constant"() <{value = 0 : i8}> : () -> i8
    %neg = "gmir.g_sub"(%zero, %b) <{overflowFlags = 1 : i32}> : (i8, i8) -> i8
    %shift = "gmir.g_shl"(%neg, %c) : (i8, i8) -> i8
    %shiftFlagged = "gmir.g_shl"(%neg, %c) <{overflowFlags = 3 : i32}> : (i8, i8) -> i8
    %negFlags = "gmir.g_add"(%a, %shift) : (i8, i8) -> i8
    %negFlagsCommute = "gmir.g_add"(%shift, %a) : (i8, i8) -> i8
    %shiftFlags = "gmir.g_add"(%a, %shiftFlagged) : (i8, i8) -> i8
    %shiftFlagsCommute = "gmir.g_add"(%shiftFlagged, %a) : (i8, i8) -> i8
    "func.return"(%negFlags, %negFlagsCommute, %shiftFlags, %shiftFlagsCommute) : (i8, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @add_shift_flags
// CHECK-SAME: (%[[A:.*]]: i8, %[[B:.*]]: i8, %[[C:.*]]: i8)
// CHECK-NEXT: %[[S0:.*]] = "gmir.g_shl"(%[[B]], %[[C]]) : (i8, i8) -> i8
// CHECK-NEXT: %[[R0:.*]] = "gmir.g_sub"(%[[A]], %[[S0]]) : (i8, i8) -> i8
// CHECK-NEXT: %[[S1:.*]] = "gmir.g_shl"(%[[B]], %[[C]]) : (i8, i8) -> i8
// CHECK-NEXT: %[[R1:.*]] = "gmir.g_sub"(%[[A]], %[[S1]]) : (i8, i8) -> i8
// CHECK-NEXT: %[[S2:.*]] = "gmir.g_shl"(%[[B]], %[[C]]) : (i8, i8) -> i8
// CHECK-NEXT: %[[R2:.*]] = "gmir.g_sub"(%[[A]], %[[S2]]) : (i8, i8) -> i8
// CHECK-NEXT: %[[S3:.*]] = "gmir.g_shl"(%[[B]], %[[C]]) : (i8, i8) -> i8
// CHECK-NEXT: %[[R3:.*]] = "gmir.g_sub"(%[[A]], %[[S3]]) : (i8, i8) -> i8
// CHECK-NEXT: "func.return"(%[[R0]], %[[R1]], %[[R2]], %[[R3]]) : (i8, i8, i8, i8) -> ()
