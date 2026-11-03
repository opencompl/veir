// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// Illegal operations are not selected.
"builtin.module"() ({
  "func.func"() <{function_type = (i32) -> (), sym_name = "main"}> ({
  ^bb0(%x: i32):
    %smax = "gmir.g_smax"(%x, %x) : (i32, i32) -> i32
    // CHECK:      "gmir.g_smax"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    %umin = "gmir.g_umin"(%x, %x) : (i32, i32) -> i32
    // CHECK-NEXT: "gmir.g_umin"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    %abs = "gmir.g_abs"(%x) : (i32) -> i32
    // CHECK-NEXT: "gmir.g_abs"(%{{.*}}) : (i32) -> i32
    "test.test"(%smax, %umin, %abs) : (i32, i32, i32) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
