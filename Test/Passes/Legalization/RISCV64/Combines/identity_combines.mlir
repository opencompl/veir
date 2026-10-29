// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// LLVM's identity_combines, and `-1 - x` → `x ^ -1`.

"builtin.module"() ({
  "func.func"() <{function_type = (i64) -> (i64, i64, i64, i64, i64), sym_name = "foo"}> ({
  ^bb0(%x: i64):
    %zero = "gmir.g_constant"() <{value = 0 : i64}> : () -> i64
    %one = "gmir.g_constant"() <{value = 1 : i64}> : () -> i64
    %ones = "gmir.g_constant"() <{value = -1 : i64}> : () -> i64
    %add = "gmir.g_add"(%x, %zero) : (i64, i64) -> i64
    %and = "gmir.g_and"(%x, %x) : (i64, i64) -> i64
    %sub = "gmir.g_sub"(%x, %x) : (i64, i64) -> i64
    %mul = "gmir.g_mul"(%x, %one) : (i64, i64) -> i64
    %not = "gmir.g_sub"(%ones, %x) : (i64, i64) -> i64
    "func.return"(%add, %and, %sub, %mul, %not) : (i64, i64, i64, i64, i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @foo
// CHECK-SAME:  (%[[X:.*]]: i64)
// CHECK-DAG:   %[[Z:.*]] = "gmir.g_constant"() <{"value" = 0 : i64}>
// CHECK-DAG:   %[[ONES:.*]] = "gmir.g_constant"() <{"value" = -1 : i64}>
// CHECK:       %[[NOT:.*]] = "gmir.g_xor"(%[[X]], %[[ONES]]) : (i64, i64) -> i64
// CHECK-NEXT:  "func.return"(%[[X]], %[[X]], %[[Z]], %[[X]], %[[NOT]])
