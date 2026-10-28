// RUN: veir-opt %s -p=legalize-riscv64 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i32, i8) -> (), sym_name = "main"}> ({
  ^bb0(%x_i64: i64, %x_i32: i32, %x_i8: i8):
    // `i64` is legal.
    %smax64 = "gmir.g_smax"(%x_i64, %x_i64) : (i64, i64) -> i64
    // CHECK:      "gmir.g_smax"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
    %smin64 = "gmir.g_smin"(%x_i64, %x_i64) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_smin"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
    %umax64 = "gmir.g_umax"(%x_i64, %x_i64) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_umax"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
    %umin64 = "gmir.g_umin"(%x_i64, %x_i64) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_umin"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64

    // Narrower widths are widened with sign extensions, which preserve both orders.
    %smax32 = "gmir.g_smax"(%x_i32, %x_i32) : (i32, i32) -> i32
    // CHECK-NEXT: %[[L:.*]] = "gmir.g_sext"(%{{.*}}) : (i32) -> i64
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_sext"(%{{.*}}) : (i32) -> i64
    // CHECK-NEXT: %[[M:.*]] = "gmir.g_smax"(%[[L]], %[[R]]) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"(%[[M]]) : (i64) -> i32
    %umin32 = "gmir.g_umin"(%x_i32, %x_i32) : (i32, i32) -> i32
    // CHECK-NEXT: %[[L:.*]] = "gmir.g_sext"(%{{.*}}) : (i32) -> i64
    // CHECK-NEXT: %[[R:.*]] = "gmir.g_sext"(%{{.*}}) : (i32) -> i64
    // CHECK-NEXT: %[[M:.*]] = "gmir.g_umin"(%[[L]], %[[R]]) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"(%[[M]]) : (i64) -> i32
    // The `i8` sign extensions are lowered to `g_sext_inreg`.
    %umax8 = "gmir.g_umax"(%x_i8, %x_i8) : (i8, i8) -> i8
    // CHECK:      "gmir.g_sext_inreg"(%{{.*}}) <{"sz" = 8 : i64}> : (i64) -> i64
    // CHECK:      "gmir.g_umax"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"(%{{.*}}) : (i64) -> i8

    // `abs` becomes `smax x (0 - x)`.
    %abs64 = "gmir.g_abs"(%x_i64) : (i64) -> i64
    // CHECK:      %[[ZERO:.*]] = "gmir.g_constant"() <{"value" = 0 : i64}> : () -> i64
    // CHECK-NEXT: %[[NEG:.*]] = "gmir.g_sub"(%[[ZERO]], %[[X:.*]]) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_smax"(%[[X]], %[[NEG]]) : (i64, i64) -> i64
    %abs32 = "gmir.g_abs"(%x_i32) : (i32) -> i32
    // CHECK-NEXT: %[[X:.*]] = "gmir.g_sext"(%{{.*}}) : (i32) -> i64
    // CHECK-NEXT: %[[ZERO:.*]] = "gmir.g_constant"() <{"value" = 0 : i64}> : () -> i64
    // CHECK-NEXT: %[[NEG:.*]] = "gmir.g_sub"(%[[ZERO]], %[[X]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[M:.*]] = "gmir.g_smax"(%[[X]], %[[NEG]]) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"(%[[M]]) : (i64) -> i32

    "test.test"(%smax64, %smin64, %umax64, %umin64, %abs64) : (i64, i64, i64, i64, i64) -> ()
    "test.test"(%smax32, %umin32, %abs32) : (i32, i32, i32) -> ()
    "test.test"(%umax8) : (i8) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
