// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

// `redundant_and` drops an outer mask that keeps every bit of an inner one, and an odd mask of a
// `g_select` between two `g_icmp`s.

"builtin.module"() ({
  "func.func"() <{function_type = (i64) -> i64, sym_name = "mask"}> ({
  ^bb0(%x: i64):
    %c31 = "gmir.g_constant"() <{value = 31 : i64}> : () -> i64
    %c255 = "gmir.g_constant"() <{value = 255 : i64}> : () -> i64
    %inner = "gmir.g_and"(%x, %c31) : (i64, i64) -> i64
    %r = "gmir.g_and"(%inner, %c255) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (i64, i64, i64) -> i64, sym_name = "select"}> ({
  ^bb0(%c: i64, %a: i64, %b: i64):
    %one = "gmir.g_constant"() <{value = 1 : i64}> : () -> i64
    %x = "gmir.g_icmp"(%a, %b) <{"predicate" = 2 : i64}> : (i64, i64) -> i64
    %y = "gmir.g_icmp"(%a, %b) <{"predicate" = 4 : i64}> : (i64, i64) -> i64
    %s = "gmir.g_select"(%c, %x, %y) : (i64, i64, i64) -> i64
    %r = "gmir.g_and"(%s, %one) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @mask
// CHECK:       %[[INNER:[^ ]*]] = "gmir.g_and"
// CHECK-NEXT:  "func.return"(%[[INNER]])

// CHECK-LABEL: func.func @select
// CHECK:       %[[S:[^ ]*]] = "gmir.g_select"
// CHECK-NEXT:  "func.return"(%[[S]])
