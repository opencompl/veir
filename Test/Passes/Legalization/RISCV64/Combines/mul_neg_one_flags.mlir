// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// 1 * 255 is defined unsigned, but 0 - 1 underflows. Multiplication by all-ones
// can become negation only if nuw is dropped. Signed negation preserves nsw.
// overflowFlags: 1 = nsw (no signed wrap), 2 = nuw (no unsigned wrap), 3 = both.
"builtin.module"() ({
  "func.func"() <{sym_name = "mul_neg_one", function_type = (i8) -> (i8, i8, i8, i8)}> ({
  ^bb0(%x: i8):
    %unsigned = "gmir.g_constant"() <{value = 255 : i8}> : () -> i8
    %signed = "gmir.g_constant"() <{value = -1 : i8}> : () -> i8
    %a = "gmir.g_mul"(%x, %unsigned) <{overflowFlags = 2 : i32}> : (i8, i8) -> i8
    %b = "gmir.g_mul"(%x, %signed) <{overflowFlags = 2 : i32}> : (i8, i8) -> i8
    %c = "gmir.g_mul"(%x, %signed) <{overflowFlags = 1 : i32}> : (i8, i8) -> i8
    %d = "gmir.g_mul"(%x, %signed) <{overflowFlags = 3 : i32}> : (i8, i8) -> i8
    "func.return"(%a, %b, %c, %d) : (i8, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @mul_neg_one
// CHECK-SAME: (%[[X:.*]]: i8)
// CHECK-NEXT: %[[Z0:.*]] = "gmir.g_constant"() <{"value" = 0 : i8}>
// CHECK-NEXT: %[[A:.*]] = "gmir.g_sub"(%[[Z0]], %[[X]]) : (i8, i8) -> i8
// CHECK-NEXT: %[[Z1:.*]] = "gmir.g_constant"() <{"value" = 0 : i8}>
// CHECK-NEXT: %[[B:.*]] = "gmir.g_sub"(%[[Z1]], %[[X]]) : (i8, i8) -> i8
// CHECK-NEXT: %[[Z2:.*]] = "gmir.g_constant"() <{"value" = 0 : i8}>
// CHECK-NEXT: %[[C:.*]] = "gmir.g_sub"(%[[Z2]], %[[X]]) <{"overflowFlags" = 1 : i32}> : (i8, i8) -> i8
// CHECK-NEXT: %[[Z3:.*]] = "gmir.g_constant"() <{"value" = 0 : i8}>
// CHECK-NEXT: %[[D:.*]] = "gmir.g_sub"(%[[Z3]], %[[X]]) <{"overflowFlags" = 1 : i32}> : (i8, i8) -> i8
// CHECK-NEXT: "func.return"(%[[A]], %[[B]], %[[C]], %[[D]]) : (i8, i8, i8, i8) -> ()
