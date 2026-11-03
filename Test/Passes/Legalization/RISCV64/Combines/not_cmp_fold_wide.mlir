// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// After legalization, a `g_icmp` result is `i64` and is `0` or `1`, so its negation is `xor` with
// `1`, not with `-1`.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64) -> (i64, i64), sym_name = "foo"}> ({
  ^bb0(%x: i64, %y: i64):
    %one = "gmir.g_constant"() <{value = 1 : i64}> : () -> i64
    %ones = "gmir.g_constant"() <{value = -1 : i64}> : () -> i64
    %cmp = "gmir.g_icmp"(%x, %y) <{predicate = 8 : i64}> : (i64, i64) -> i64
    %not = "gmir.g_xor"(%cmp, %one) : (i64, i64) -> i64
    // `xor` with `-1` gives `-1` or `-2`, which is not a comparison result.
    %notAll = "gmir.g_xor"(%cmp, %ones) : (i64, i64) -> i64
    "func.return"(%not, %notAll) : (i64, i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @foo
// CHECK-SAME:  (%[[X:.*]]: i64, %[[Y:.*]]: i64)
// CHECK:       %[[UGT:.*]] = "gmir.g_icmp"(%[[X]], %[[Y]]) <{"predicate" = 8 : i64}> : (i64, i64) -> i64
// CHECK:       %[[ULE:.*]] = "gmir.g_icmp"(%[[X]], %[[Y]]) <{"predicate" = 7 : i64}> : (i64, i64) -> i64
// CHECK:       %[[NOTALL:.*]] = "gmir.g_xor"(%[[UGT]], %{{.*}}) : (i64, i64) -> i64
// CHECK:       "func.return"(%[[ULE]], %[[NOTALL]])
