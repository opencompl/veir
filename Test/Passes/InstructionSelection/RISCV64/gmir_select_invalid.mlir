// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// Illegal `g_select`s are not selected: the values and the condition must be `i64`.
"builtin.module"() ({
  "func.func"() <{function_type = (i64, i1, i8) -> (), sym_name = "main"}> ({
  ^bb0(%x: i64, %c: i1, %y: i8):
    %narrow_cond = "gmir.g_select"(%c, %x, %x) : (i1, i64, i64) -> i64
    // CHECK:      "gmir.g_select"(%{{.*}}, %{{.*}}, %{{.*}}) : (i1, i64, i64) -> i64
    %narrow = "gmir.g_select"(%x, %y, %y) : (i64, i8, i8) -> i8
    // CHECK-NEXT: "gmir.g_select"(%{{.*}}, %{{.*}}, %{{.*}}) : (i64, i8, i8) -> i8
    "test.test"(%narrow_cond, %narrow) : (i64, i8) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
