// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// LLVM's integer_reassoc_combines. The new operations have no flags, even when the matched ones do.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64, i64) -> (i64, i64, i64, i64), sym_name = "foo"}> ({
  ^bb0(%a: i64, %b: i64, %c: i64):
    // (a + (b - c)) - b
    %bc = "gmir.g_sub"(%b, %c) : (i64, i64) -> i64
    %abc = "gmir.g_add"(%a, %bc) : (i64, i64) -> i64
    %r0 = "gmir.g_sub"(%abc, %b) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    // (0 - a) + b
    %zero = "gmir.g_constant"() <{value = 0 : i64}> : () -> i64
    %na = "gmir.g_sub"(%zero, %a) : (i64, i64) -> i64
    %r1 = "gmir.g_add"(%na, %b) : (i64, i64) -> i64
    // (10 - a) - 3
    %c1 = "gmir.g_constant"() <{value = 10 : i64}> : () -> i64
    %c2 = "gmir.g_constant"() <{value = 3 : i64}> : () -> i64
    %s = "gmir.g_sub"(%c1, %a) : (i64, i64) -> i64
    %r2 = "gmir.g_sub"(%s, %c2) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    // (a & ~b) | b
    %ones = "gmir.g_constant"() <{value = -1 : i64}> : () -> i64
    %nb = "gmir.g_xor"(%b, %ones) : (i64, i64) -> i64
    %and = "gmir.g_and"(%a, %nb) : (i64, i64) -> i64
    %r3 = "gmir.g_or"(%and, %b) : (i64, i64) -> i64
    "func.return"(%r0, %r1, %r2, %r3) : (i64, i64, i64, i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @foo
// CHECK-SAME:  (%[[A:.*]]: i64, %[[B:.*]]: i64, %[[C:.*]]: i64)
// CHECK-NEXT:  %[[R0:.*]] = "gmir.g_sub"(%[[A]], %[[C]]) : (i64, i64) -> i64
// CHECK-NEXT:  %[[R1:.*]] = "gmir.g_sub"(%[[B]], %[[A]]) : (i64, i64) -> i64
// CHECK-NEXT:  %[[C7:.*]] = "gmir.g_constant"() <{"value" = 7 : i64}>
// CHECK-NEXT:  %[[R2:.*]] = "gmir.g_sub"(%[[C7]], %[[A]]) : (i64, i64) -> i64
// CHECK-NEXT:  %[[R3:.*]] = "gmir.g_or"(%[[A]], %[[B]]) : (i64, i64) -> i64
// CHECK-NEXT:  "func.return"(%[[R0]], %[[R1]], %[[R2]], %[[R3]])
