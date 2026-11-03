// RUN: veir-opt %s -p=legalize-riscv64 | filecheck %s

// Funnel shifts narrower than `i64` are lowered to shifts by `z % w` and `w - 1 - z % w`, which
// are then widened like any other shift.

"builtin.module"() ({
  "func.func"() <{function_type = (i32, i8, i5, i3) -> (), sym_name = "main"}> ({
  ^bb0(%x32: i32, %x8: i8, %x5: i5, %n: i3):
    %fshl32 = "gmir.g_fshl"(%x32, %x32, %x32) : (i32, i32, i32) -> i32
    "test.test"(%fshl32) : (i32) -> ()
    // CHECK:      "gmir.g_constant"() <{"value" = 32 : i64}> : () -> i64
    // CHECK:      "gmir.g_constant"() <{"value" = 31 : i64}> : () -> i64
    // CHECK:      "riscv.remuw"
    // CHECK:      "riscv.subw"
    // CHECK:      "riscv.sllw"
    // CHECK:      "riscv.srlw"
    // CHECK:      "riscv.srlw"
    // CHECK:      "gmir.g_or"
    // CHECK:      "test.test"

    %fshr8 = "gmir.g_fshr"(%x8, %x8, %x8) : (i8, i8, i8) -> i8
    "test.test"(%fshr8) : (i8) -> ()
    // CHECK:      "gmir.g_constant"() <{"value" = 8 : i64}> : () -> i64
    // CHECK:      "gmir.g_constant"() <{"value" = 7 : i64}> : () -> i64
    // CHECK:      "riscv.remuw"
    // CHECK:      "gmir.g_sub"
    // CHECK:      "gmir.g_shl"
    // CHECK:      "gmir.g_shl"
    // CHECK:      "gmir.g_lshr"
    // CHECK:      "gmir.g_or"
    // CHECK:      "gmir.g_trunc"(%{{.*}}) : (i64) -> i8
    // CHECK-NEXT: "test.test"

    %fshl5 = "gmir.g_fshl"(%x5, %x5, %x5) : (i5, i5, i5) -> i5
    "test.test"(%fshl5) : (i5) -> ()
    // CHECK:      "gmir.g_constant"() <{"value" = 5 : i64}> : () -> i64
    // CHECK:      "gmir.g_constant"() <{"value" = 4 : i64}> : () -> i64
    // CHECK:      "riscv.remuw"
    // CHECK:      "gmir.g_or"
    // CHECK:      "gmir.g_trunc"(%{{.*}}) : (i64) -> i5
    // CHECK-NEXT: "test.test"

    // An amount narrower than the shifted values is first zero-extended, so that the width fits.
    %fshr8n = "gmir.g_fshr"(%x8, %x8, %n) : (i8, i8, i3) -> i8
    "test.test"(%fshr8n) : (i8) -> ()
    // CHECK:      "gmir.g_constant"() <{"value" = 7 : i64}> : () -> i64
    // CHECK-NEXT: "gmir.g_anyext"(%{{.*}}) : (i3) -> i64
    // CHECK-NEXT: "gmir.g_and"
    // CHECK:      "gmir.g_constant"() <{"value" = 8 : i64}> : () -> i64
    // CHECK:      "riscv.remuw"
    // CHECK:      "gmir.g_or"
    // CHECK:      "gmir.g_trunc"(%{{.*}}) : (i64) -> i8
    // CHECK-NEXT: "test.test"
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
