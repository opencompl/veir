// RUN: veir-opt %s -p=legalize-riscv64 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (i1, i8, i16, i32) -> (), sym_name = "main"}> ({
  ^bb0(%x_i1: i1, %x_i8: i8, %x_i16: i16, %x_i32: i32):
    // CHECK: func.func @main(%[[X_I1:.*]]: i1, %[[X_I8:.*]]: i8, %[[X_I16:.*]]: i16, %[[X_I32:.*]]: i32) {

    // Extensions from `i16` and `i32` are legal.
    %sext_i16_i32 = "gmir.g_sext"(%x_i16) : (i16) -> i32
    %sext_i16_i64 = "gmir.g_sext"(%x_i16) : (i16) -> i64
    %sext_i32_i64 = "gmir.g_sext"(%x_i32) : (i32) -> i64
    // CHECK-NEXT: %[[SEXT_I16_I32:.*]] = "gmir.g_sext"(%[[X_I16]]) : (i16) -> i32
    // CHECK-NEXT: %[[SEXT_I16_I64:.*]] = "gmir.g_sext"(%[[X_I16]]) : (i16) -> i64
    // CHECK-NEXT: %[[SEXT_I32_I64:.*]] = "gmir.g_sext"(%[[X_I32]]) : (i32) -> i64

    // Other extensions are lowered to `g_sext_inreg`.
    %sext_i1_i64 = "gmir.g_sext"(%x_i1) : (i1) -> i64
    // CHECK-NEXT: %[[EXT_I1_I64:.*]] = "gmir.g_anyext"(%[[X_I1]]) : (i1) -> i64
    // CHECK-NEXT: %[[SEXT_I1_I64:.*]] = "gmir.g_sext_inreg"(%[[EXT_I1_I64]]) <{"sz" = 1 : i64}> : (i64) -> i64

    // A narrower `g_sext_inreg` is then widened.
    %sext_i8_i32 = "gmir.g_sext"(%x_i8) : (i8) -> i32
    // CHECK-NEXT: %[[EXT_I8_I32:.*]] = "gmir.g_anyext"(%[[X_I8]]) : (i8) -> i64
    // CHECK-NEXT: %[[INREG_I8_I32:.*]] = "gmir.g_sext_inreg"(%[[EXT_I8_I32]]) <{"sz" = 8 : i64}> : (i64) -> i64
    // CHECK-NEXT: %[[SEXT_I8_I32:.*]] = "gmir.g_trunc"(%[[INREG_I8_I32]]) : (i64) -> i32

    // Extensions to other widths are lowered too.
    %sext_i16_i42 = "gmir.g_sext"(%x_i16) : (i16) -> i42
    // CHECK-NEXT: %[[EXT_I16_I42:.*]] = "gmir.g_anyext"(%[[X_I16]]) : (i16) -> i64
    // CHECK-NEXT: %[[INREG_I16_I42:.*]] = "gmir.g_sext_inreg"(%[[EXT_I16_I42]]) <{"sz" = 16 : i64}> : (i64) -> i64
    // CHECK-NEXT: %[[SEXT_I16_I42:.*]] = "gmir.g_trunc"(%[[INREG_I16_I42]]) : (i64) -> i42

    // CHECK-NEXT: "test.test"(%[[SEXT_I16_I32]], %[[SEXT_I16_I64]], %[[SEXT_I32_I64]], %[[SEXT_I1_I64]], %[[SEXT_I8_I32]], %[[SEXT_I16_I42]])
    "test.test"(%sext_i16_i32, %sext_i16_i64, %sext_i32_i64, %sext_i1_i64, %sext_i8_i32, %sext_i16_i42) : (i32, i64, i64, i64, i32, i42) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
