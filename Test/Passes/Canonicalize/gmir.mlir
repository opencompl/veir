// RUN: veir-opt %s -p=canonicalize,dce | filecheck %s

// Folded GMIR operations are materialized as `gmir.g_constant`.
"builtin.module"() ({
  "func.func"() <{function_type = () -> i32, sym_name = "fold"}> ({
    %a = "gmir.g_constant"() <{value = 2 : i32}> : () -> i32
    %b = "gmir.g_constant"() <{value = 3 : i32}> : () -> i32
    // CHECK-NOT: "gmir.g_add"
    %sum = "gmir.g_add"(%a, %b) : (i32, i32) -> i32
    // CHECK: %[[RESULT:.*]] = "gmir.g_constant"() <{"value" = 5 : i32}> : () -> i32
    // CHECK-NEXT: "func.return"(%[[RESULT]]) : (i32) -> ()
    "func.return"(%sum) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
