// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// LLVM's integer_reassoc_combines and sub_add_reg. The new operations have no flags, even when the
// matched ones do.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64, i64) -> (i64, i64, i64, i64), sym_name = "three_operands"}> ({
  ^bb0(%a: i64, %b: i64, %c: i64):
    // (a + (b - c)) - b
    %bc = "gmir.g_sub"(%b, %c) : (i64, i64) -> i64
    %abc = "gmir.g_add"(%a, %bc) : (i64, i64) -> i64
    %r0 = "gmir.g_sub"(%abc, %b) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    // (a - (b - c)) - c
    %abc2 = "gmir.g_sub"(%a, %bc) : (i64, i64) -> i64
    %r1 = "gmir.g_sub"(%abc2, %c) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    // (a - b) + (c - a)
    %ab = "gmir.g_sub"(%a, %b) : (i64, i64) -> i64
    %ca = "gmir.g_sub"(%c, %a) : (i64, i64) -> i64
    %r2 = "gmir.g_add"(%ab, %ca) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    // (a - b) + (b - c)
    %r3 = "gmir.g_add"(%ab, %bc) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    "func.return"(%r0, %r1, %r2, %r3) : (i64, i64, i64, i64) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (i64, i64, i64) -> (i64, i64), sym_name = "a_plus_b_minus_a_plus_c"}> ({
  ^bb0(%a: i64, %b: i64, %c: i64):
    // a + (b - (a + c))
    %ac = "gmir.g_add"(%a, %c) : (i64, i64) -> i64
    %s0 = "gmir.g_sub"(%b, %ac) : (i64, i64) -> i64
    %r0 = "gmir.g_add"(%a, %s0) : (i64, i64) -> i64
    // a + (b - (c + a))
    %ca = "gmir.g_add"(%c, %a) : (i64, i64) -> i64
    %s1 = "gmir.g_sub"(%b, %ca) : (i64, i64) -> i64
    %r1 = "gmir.g_add"(%a, %s1) : (i64, i64) -> i64
    "func.return"(%r0, %r1) : (i64, i64) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (i64, i64) -> (i64, i64, i64, i64, i64, i64), sym_name = "two_operands"}> ({
  ^bb0(%a: i64, %b: i64):
    %zero = "gmir.g_constant"() <{value = 0 : i64}> : () -> i64
    %na = "gmir.g_sub"(%zero, %a) : (i64, i64) -> i64
    %nb = "gmir.g_sub"(%zero, %b) : (i64, i64) -> i64
    // (0 - a) + b
    %r0 = "gmir.g_add"(%na, %b) : (i64, i64) -> i64
    // a + (0 - b)
    %r1 = "gmir.g_add"(%a, %nb) : (i64, i64) -> i64
    // a - (0 - b)
    %r2 = "gmir.g_sub"(%a, %nb) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    // a - (a - b)
    %ab = "gmir.g_sub"(%a, %b) : (i64, i64) -> i64
    %r3 = "gmir.g_sub"(%a, %ab) : (i64, i64) -> i64
    // a + (b - a) and (b - a) + a
    %ba = "gmir.g_sub"(%b, %a) : (i64, i64) -> i64
    %r4 = "gmir.g_add"(%a, %ba) : (i64, i64) -> i64
    %r5 = "gmir.g_add"(%ba, %a) : (i64, i64) -> i64
    "func.return"(%r0, %r1, %r2, %r3, %r4, %r5) : (i64, i64, i64, i64, i64, i64) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (i64) -> (i64, i64, i64), sym_name = "constants"}> ({
  ^bb0(%a: i64):
    %c1 = "gmir.g_constant"() <{value = 10 : i64}> : () -> i64
    %c2 = "gmir.g_constant"() <{value = 3 : i64}> : () -> i64
    // (a - 10) - 3
    %s0 = "gmir.g_sub"(%a, %c1) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %r0 = "gmir.g_sub"(%s0, %c2) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    // (10 - a) - 3
    %s1 = "gmir.g_sub"(%c1, %a) : (i64, i64) -> i64
    %r1 = "gmir.g_sub"(%s1, %c2) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    // (a - 10) + 3
    %r2 = "gmir.g_add"(%s0, %c2) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    "func.return"(%r0, %r1, %r2) : (i64, i64, i64) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (i64, i64) -> (i64, i64), sym_name = "or_and_xor_to_or"}> ({
  ^bb0(%x: i64, %y: i64):
    %ones = "gmir.g_constant"() <{value = -1 : i64}> : () -> i64
    %ny = "gmir.g_xor"(%y, %ones) : (i64, i64) -> i64
    // (x & ~y) | y
    %and = "gmir.g_and"(%x, %ny) : (i64, i64) -> i64
    %r0 = "gmir.g_or"(%and, %y) : (i64, i64) -> i64
    // (x | ~y) & y
    %or = "gmir.g_or"(%x, %ny) : (i64, i64) -> i64
    %r1 = "gmir.g_and"(%or, %y) : (i64, i64) -> i64
    "func.return"(%r0, %r1) : (i64, i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @three_operands
// CHECK-SAME:  (%[[A:.*]]: i64, %[[B:.*]]: i64, %[[C:.*]]: i64)
// CHECK-NEXT:  %[[R0:.*]] = "gmir.g_sub"(%[[A]], %[[C]]) : (i64, i64) -> i64
// CHECK-NEXT:  %[[R1:.*]] = "gmir.g_sub"(%[[A]], %[[B]]) : (i64, i64) -> i64
// CHECK-NEXT:  %[[R2:.*]] = "gmir.g_sub"(%[[C]], %[[B]]) : (i64, i64) -> i64
// CHECK-NEXT:  %[[R3:.*]] = "gmir.g_sub"(%[[A]], %[[C]]) : (i64, i64) -> i64
// CHECK-NEXT:  "func.return"(%[[R0]], %[[R1]], %[[R2]], %[[R3]])

// CHECK-LABEL: func.func @a_plus_b_minus_a_plus_c
// CHECK-SAME:  (%[[A:.*]]: i64, %[[B:.*]]: i64, %[[C:.*]]: i64)
// CHECK-NEXT:  %[[R0:.*]] = "gmir.g_sub"(%[[B]], %[[C]]) : (i64, i64) -> i64
// CHECK-NEXT:  %[[R1:.*]] = "gmir.g_sub"(%[[B]], %[[C]]) : (i64, i64) -> i64
// CHECK-NEXT:  "func.return"(%[[R0]], %[[R1]])

// CHECK-LABEL: func.func @two_operands
// CHECK-SAME:  (%[[A:.*]]: i64, %[[B:.*]]: i64)
// CHECK-NEXT:  %[[R0:.*]] = "gmir.g_sub"(%[[B]], %[[A]]) : (i64, i64) -> i64
// CHECK-NEXT:  %[[R1:.*]] = "gmir.g_sub"(%[[A]], %[[B]]) : (i64, i64) -> i64
// CHECK-NEXT:  %[[R2:.*]] = "gmir.g_add"(%[[A]], %[[B]]) : (i64, i64) -> i64
// CHECK-NEXT:  "func.return"(%[[R0]], %[[R1]], %[[R2]], %[[B]], %[[B]], %[[B]])

// The constants fold, and `sub_to_add` turns the remaining `a - 13` into `a + -13`.
// CHECK-LABEL: func.func @constants
// CHECK-SAME:  (%[[A:.*]]: i64)
// CHECK-NEXT:  %[[C0:.*]] = "gmir.g_constant"() <{"value" = -13 : i64}>
// CHECK-NEXT:  %[[R0:.*]] = "gmir.g_add"(%[[A]], %[[C0]]) : (i64, i64) -> i64
// CHECK-NEXT:  %[[C1:.*]] = "gmir.g_constant"() <{"value" = 7 : i64}>
// CHECK-NEXT:  %[[R1:.*]] = "gmir.g_sub"(%[[C1]], %[[A]]) : (i64, i64) -> i64
// CHECK-NEXT:  %[[C2:.*]] = "gmir.g_constant"() <{"value" = -7 : i64}>
// CHECK-NEXT:  %[[R2:.*]] = "gmir.g_add"(%[[A]], %[[C2]]) : (i64, i64) -> i64
// CHECK-NEXT:  "func.return"(%[[R0]], %[[R1]], %[[R2]])

// CHECK-LABEL: func.func @or_and_xor_to_or
// CHECK-SAME:  (%[[X:.*]]: i64, %[[Y:.*]]: i64)
// CHECK-NEXT:  %[[R0:.*]] = "gmir.g_or"(%[[X]], %[[Y]]) : (i64, i64) -> i64
// CHECK-NEXT:  %[[R1:.*]] = "gmir.g_and"(%[[X]], %[[Y]]) : (i64, i64) -> i64
// CHECK-NEXT:  "func.return"(%[[R0]], %[[R1]])
