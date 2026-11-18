// RUN: veir-opt %s -p=legalize-riscv64 | filecheck %s

// A narrow `g_freeze` freezes the any-extended value and truncates it back.

"builtin.module"() ({
  "func.func"() <{function_type = (i32) -> i32, sym_name = "freeze"}> ({
  ^bb0(%x : i32):
    // CHECK-LABEL: func.func @freeze
    // CHECK:       %[[E:.*]] = "gmir.g_anyext"(%{{.*}}) : (i32) -> i64
    // CHECK-NEXT:  %[[F:.*]] = "gmir.g_freeze"(%[[E]]) : (i64) -> i64
    // CHECK-NEXT:  %[[T:.*]] = "gmir.g_trunc"(%[[F]]) : (i64) -> i32
    // CHECK-NEXT:  "func.return"(%[[T]])
    %f = "gmir.g_freeze"(%x) : (i32) -> i32
    "func.return"(%f) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
