// RUN: veir-opt %s -p=prelegalizer-combiner-riscv64 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (i1) -> (), sym_name = "select_of_constants"}> ({
  ^bb0(%c: i1):
    %one = "gmir.g_constant"() <{value = 1 : i32}> : () -> i32
    %zero = "gmir.g_constant"() <{value = 0 : i32}> : () -> i32
    // c ? 1 : 0 -> zext c.
    // CHECK-LABEL: func.func @select_of_constants
    // CHECK:      %[[R:.*]] = "gmir.g_zext"(%{{.*}}) : (i1) -> i32
    // CHECK-NEXT: "test.test"(%[[R]])
    %r = "gmir.g_select"(%c, %one, %zero) : (i1, i32, i32) -> i32
    "test.test"(%r) : (i32) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
