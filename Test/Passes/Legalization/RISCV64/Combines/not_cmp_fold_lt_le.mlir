// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// Negating an `icmp` of `ult`, `ule`, `slt` or `sle` inverts the predicate to `uge`,
// `ugt`, `sge` or `sgt`.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64) -> (i1, i1, i1, i1), sym_name = "foo"}> ({
  ^bb0(%x: i64, %y: i64):
    %ult = "gmir.g_icmp"(%x, %y) <{predicate = 6 : i64}> : (i64, i64) -> i1
    %ule = "gmir.g_icmp"(%x, %y) <{predicate = 7 : i64}> : (i64, i64) -> i1
    %slt = "gmir.g_icmp"(%x, %y) <{predicate = 2 : i64}> : (i64, i64) -> i1
    %sle = "gmir.g_icmp"(%x, %y) <{predicate = 3 : i64}> : (i64, i64) -> i1
    %m1 = "gmir.g_constant"() <{value = -1 : i1}> : () -> i1
    %a = "gmir.g_xor"(%ult, %m1) : (i1, i1) -> i1
    %b = "gmir.g_xor"(%ule, %m1) : (i1, i1) -> i1
    %c = "gmir.g_xor"(%slt, %m1) : (i1, i1) -> i1
    %d = "gmir.g_xor"(%sle, %m1) : (i1, i1) -> i1
    "func.return"(%a, %b, %c, %d) : (i1, i1, i1, i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @foo
// CHECK-SAME:  (%[[X:.*]]: i64, %[[Y:.*]]: i64)
// CHECK-DAG:   %[[A:.*]] = "gmir.g_icmp"(%[[X]], %[[Y]]) <{"predicate" = 9 : i64}> : (i64, i64) -> i1
// CHECK-DAG:   %[[B:.*]] = "gmir.g_icmp"(%[[X]], %[[Y]]) <{"predicate" = 8 : i64}> : (i64, i64) -> i1
// CHECK-DAG:   %[[C:.*]] = "gmir.g_icmp"(%[[X]], %[[Y]]) <{"predicate" = 5 : i64}> : (i64, i64) -> i1
// CHECK-DAG:   %[[D:.*]] = "gmir.g_icmp"(%[[X]], %[[Y]]) <{"predicate" = 4 : i64}> : (i64, i64) -> i1
// CHECK-NOT:   "gmir.g_xor"
// CHECK:       "func.return"(%[[A]], %[[B]], %[[C]], %[[D]])
