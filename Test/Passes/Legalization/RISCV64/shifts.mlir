// RUN: veir-opt %s -p=legalize-riscv64 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    %x_i32 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %shl32 = "gmir.g_shl"(%x_i32, %x_i32) : (i32, i32) -> i32
    // CHECK:      "riscv.sllw"({{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %lshr32 = "gmir.g_lshr"(%x_i32, %x_i32) : (i32, i32) -> i32
    // CHECK:      "riscv.srlw"({{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %ashr32 = "gmir.g_ashr"(%x_i32, %x_i32) : (i32, i32) -> i32
    // CHECK:      "riscv.sraw"({{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg

    %x_i8 = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    %shl = "gmir.g_shl"(%x_i8, %x_i8) <{overflowFlags = 3 : i32}> : (i8, i8) -> i8
    // CHECK:      %[[X_I8:.*]] = "llvm.mlir.constant"() <{"value" = 1 : i8}> : () -> i8
    // CHECK-NEXT: %[[AMOUNT:.*]] = "gmir.g_zext"(%[[X_I8]]) : (i8) -> i64
    // CHECK-NEXT: %[[VALUE:.*]] = "gmir.g_anyext"(%[[X_I8]]) : (i8) -> i64
    // CHECK-NEXT: %[[SHL:.*]] = "gmir.g_shl"(%[[VALUE]], %[[AMOUNT]]) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"(%[[SHL]]) : (i64) -> i8
    %lshr = "gmir.g_lshr"(%x_i8, %x_i8) <{isExact}> : (i8, i8) -> i8
    // CHECK:      "gmir.g_zext"({{.*}}) : (i8) -> i64
    // CHECK-NEXT: "gmir.g_zext"({{.*}}) : (i8) -> i64
    // CHECK-NEXT: "gmir.g_lshr"({{.*}}) <{isExact}> : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"({{.*}}) : (i64) -> i8
    %ashr = "gmir.g_ashr"(%x_i8, %x_i8) : (i8, i8) -> i8
    // CHECK:      "gmir.g_zext"({{.*}}) : (i8) -> i64
    // CHECK-NEXT: "gmir.g_sext"({{.*}}) : (i8) -> i64
    // CHECK-NEXT: "gmir.g_ashr"({{.*}}) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"({{.*}}) : (i64) -> i8

    %x_i64 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    // Only the amount is widened.
    %shl_i64_by_i8 = "gmir.g_shl"(%x_i64, %x_i8) : (i64, i8) -> i64
    // CHECK:      %[[X_I64:.*]] = "llvm.mlir.constant"() <{"value" = 1 : i64}> : () -> i64
    // CHECK-NEXT: %[[AMOUNT:.*]] = "gmir.g_zext"(%[[X_I8]]) : (i8) -> i64
    // CHECK-NEXT: "gmir.g_shl"(%[[X_I64]], %[[AMOUNT]]) : (i64, i64) -> i64
    // The word shifts need an `i32` amount, so this is widened to `i64` instead.
    %shl_i32_by_i8 = "gmir.g_shl"(%x_i32, %x_i8) : (i32, i8) -> i32
    // CHECK:      "gmir.g_zext"({{.*}}) : (i8) -> i64
    // CHECK-NEXT: "gmir.g_anyext"({{.*}}) : (i32) -> i64
    // CHECK-NEXT: "gmir.g_shl"({{.*}}) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"({{.*}}) : (i64) -> i32

    "test.test"(%shl32, %lshr32, %ashr32, %shl, %lshr, %ashr, %shl_i64_by_i8, %shl_i32_by_i8) : (i32, i32, i32, i8, i8, i8, i64, i32) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
