// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// Rewrites that replace an operation with an unrelated one must not hand its
// overflow flags to the replacement.
// overflowFlags: 1 = nsw (no signed wrap), 2 = nuw (no unsigned wrap), 3 = both.
"builtin.module"() ({
  "func.func"() <{sym_name = "constant_rewrite_flags", function_type = (i8, i8) -> (i8, i8, i8, i8)}> ({
  ^bb0(%x: i8, %y: i8):
    %signed = "gmir.g_constant"() <{value = -1 : i8}> : () -> i8
    // Multiplication by all-ones becomes negation: 1 * 255 is defined unsigned,
    // but 0 - 1 underflows, so only nsw carries over.
    %mulNuw = "gmir.g_mul"(%x, %signed) <{overflowFlags = 2 : i32}> : (i8, i8) -> i8
    %mulNsw = "gmir.g_mul"(%x, %signed) <{overflowFlags = 1 : i32}> : (i8, i8) -> i8
    %mulBoth = "gmir.g_mul"(%x, %signed) <{overflowFlags = 3 : i32}> : (i8, i8) -> i8


    %one = "gmir.g_constant"() <{value = 1 : i8}> : () -> i8
    // (x - y) - 1 becomes (y ^ -1) + x. The unflagged inner subtraction may
    // wrap, so the addition can overflow where the outer subtraction did not:
    // (-128 - 1) - 1 is 126, but -128 + ~1 overflows signed arithmetic.
    %wide = "gmir.g_sub"(%x, %y) : (i8, i8) -> i8
    %wideBoth = "gmir.g_sub"(%wide, %one) <{overflowFlags = 3 : i32}> : (i8, i8) -> i8
    "func.return"(%mulNuw, %mulNsw, %mulBoth, %wideBoth) : (i8, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @constant_rewrite_flags
// CHECK-SAME: (%[[X:.*]]: i8, %[[Y:.*]]: i8)
// CHECK-NEXT: %[[Z0:.*]] = "gmir.g_constant"() <{"value" = 0 : i8}>
// CHECK-NEXT: %[[M0:.*]] = "gmir.g_sub"(%[[Z0]], %[[X]]) : (i8, i8) -> i8
// CHECK-NEXT: %[[Z1:.*]] = "gmir.g_constant"() <{"value" = 0 : i8}>
// CHECK-NEXT: %[[M1:.*]] = "gmir.g_sub"(%[[Z1]], %[[X]]) <{"overflowFlags" = 1 : i32}> : (i8, i8) -> i8
// CHECK-NEXT: %[[Z2:.*]] = "gmir.g_constant"() <{"value" = 0 : i8}>
// CHECK-NEXT: %[[M2:.*]] = "gmir.g_sub"(%[[Z2]], %[[X]]) <{"overflowFlags" = 1 : i32}> : (i8, i8) -> i8
// CHECK-NEXT: %[[ONES:.*]] = "gmir.g_constant"() <{"value" = -1 : i8}>
// CHECK-NEXT: %[[XOR:.*]] = "gmir.g_xor"(%[[Y]], %[[ONES]]) : (i8, i8) -> i8
// CHECK-NEXT: %[[W:.*]] = "gmir.g_add"(%[[XOR]], %[[X]]) : (i8, i8) -> i8
// CHECK-NEXT: "func.return"(%[[M0]], %[[M1]], %[[M2]], %[[W]]) : (i8, i8, i8, i8) -> ()
