// RUN: veir-opt %s -p=legalize-riscv64 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (i1, i7, i8, i16, i32) -> (), sym_name = "main"}> ({
  ^bb0(%x_i1: i1, %x_i7: i7, %x_i8: i8, %x_i16: i16, %x_i32: i32):
    // CHECK: func.func @main(%[[X_I1:.*]]: i1, %[[X_I7:.*]]: i7, %[[X_I8:.*]]: i8, %[[X_I16:.*]]: i16, %[[X_I32:.*]]: i32) {

    // Extensions from `i16` and `i32` are legal.
    %zext_i16_i32 = "gmir.g_zext"(%x_i16) : (i16) -> i32
    %zext_i16_i64 = "gmir.g_zext"(%x_i16) : (i16) -> i64
    %zext_i32_i64 = "gmir.g_zext"(%x_i32) : (i32) -> i64
    // CHECK-NEXT: %[[ZEXT_I16_I32:.*]] = "gmir.g_zext"(%[[X_I16]]) : (i16) -> i32
    // CHECK-NEXT: %[[ZEXT_I16_I64:.*]] = "gmir.g_zext"(%[[X_I16]]) : (i16) -> i64
    // CHECK-NEXT: %[[ZEXT_I32_I64:.*]] = "gmir.g_zext"(%[[X_I32]]) : (i32) -> i64

    // Other extensions are lowered to a `g_and` with the mask of the source width.
    %zext_i1_i64 = "gmir.g_zext"(%x_i1) : (i1) -> i64
    // CHECK-NEXT: %[[EXT_I1_I64:.*]] = "gmir.g_anyext"(%[[X_I1]]) : (i1) -> i64
    // CHECK-NEXT: %[[MASK_I1_I64:.*]] = "gmir.g_constant"() <{"value" = 1 : i64}> : () -> i64
    // CHECK-NEXT: %[[ZEXT_I1_I64:.*]] = "gmir.g_and"(%[[EXT_I1_I64]], %[[MASK_I1_I64]]) : (i64, i64) -> i64

    // A narrower `g_and` is then widened.
    %zext_i8_i32 = "gmir.g_zext"(%x_i8) : (i8) -> i32
    // CHECK-NEXT: %[[MASK_I8_I32:.*]] = "gmir.g_constant"() <{"value" = 255 : i64}> : () -> i64
    // CHECK-NEXT: %[[EXT_I8_I32:.*]] = "gmir.g_anyext"(%[[X_I8]]) : (i8) -> i64
    // CHECK-NEXT: %[[AND_I8_I32:.*]] = "gmir.g_and"(%[[EXT_I8_I32]], %[[MASK_I8_I32]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[ZEXT_I8_I32:.*]] = "gmir.g_trunc"(%[[AND_I8_I32]]) : (i64) -> i32

    // The `nneg` flag is dropped.
    %zext_i7_i8 = "gmir.g_zext"(%x_i7) <{nneg}> : (i7) -> i8
    // CHECK-NEXT: %[[MASK_I7_I8:.*]] = "gmir.g_constant"() <{"value" = 127 : i64}> : () -> i64
    // CHECK-NEXT: %[[EXT_I7_I8:.*]] = "gmir.g_anyext"(%[[X_I7]]) : (i7) -> i64
    // CHECK-NEXT: %[[AND_I7_I8:.*]] = "gmir.g_and"(%[[EXT_I7_I8]], %[[MASK_I7_I8]]) : (i64, i64) -> i64
    // CHECK-NEXT: %[[ZEXT_I7_I8:.*]] = "gmir.g_trunc"(%[[AND_I7_I8]]) : (i64) -> i8

    // CHECK-NEXT: "test.test"(%[[ZEXT_I16_I32]], %[[ZEXT_I16_I64]], %[[ZEXT_I32_I64]], %[[ZEXT_I1_I64]], %[[ZEXT_I8_I32]], %[[ZEXT_I7_I8]])
    "test.test"(%zext_i16_i32, %zext_i16_i64, %zext_i32_i64, %zext_i1_i64, %zext_i8_i32, %zext_i7_i8) : (i32, i64, i64, i64, i32, i8) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
