// RUN: veir-opt %s -p=legalize-riscv64 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    // `i64` is legal.
    %x_i64 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %mul64 = "gmir.g_mul"(%x_i64, %x_i64) : (i64, i64) -> i64
    // CHECK:      "gmir.g_mul"({{.*}}) : (i64, i64) -> i64
    %sdiv64 = "gmir.g_sdiv"(%x_i64, %x_i64) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_sdiv"({{.*}}) : (i64, i64) -> i64
    %udiv64 = "gmir.g_udiv"(%x_i64, %x_i64) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_udiv"({{.*}}) : (i64, i64) -> i64
    %srem64 = "gmir.g_srem"(%x_i64, %x_i64) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_srem"({{.*}}) : (i64, i64) -> i64
    %urem64 = "gmir.g_urem"(%x_i64, %x_i64) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_urem"({{.*}}) : (i64, i64) -> i64

    // `i32` -> the RISC-V word variants (custom legalization), except for the signed remainder,
    // which is widened to `i64`.
    %x_i32 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %mul32 = "gmir.g_mul"(%x_i32, %x_i32) <{overflowFlags = 3 : i32}> : (i32, i32) -> i32
    // CHECK:      "riscv.mulw"({{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %sdiv32 = "gmir.g_sdiv"(%x_i32, %x_i32) : (i32, i32) -> i32
    // CHECK:      "riscv.divw"({{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %udiv32 = "gmir.g_udiv"(%x_i32, %x_i32) : (i32, i32) -> i32
    // CHECK:      "riscv.divuw"({{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %srem32 = "gmir.g_srem"(%x_i32, %x_i32) : (i32, i32) -> i32
    // CHECK:      "gmir.g_sext"({{.*}}) : (i32) -> i64
    // CHECK-NEXT: "gmir.g_sext"({{.*}}) : (i32) -> i64
    // CHECK-NEXT: "gmir.g_srem"({{.*}}) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"({{.*}}) : (i64) -> i32
    %urem32 = "gmir.g_urem"(%x_i32, %x_i32) : (i32, i32) -> i32
    // CHECK:      "riscv.remuw"({{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg

    // The high bits of the operands never reach the low bits of the product, so any extension is
    // fine, but the no-wrap flags are dropped.
    %lhs = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    %rhs = "llvm.mlir.constant"() <{value = 2 : i8}> : () -> i8
    %mul = "gmir.g_mul"(%lhs, %rhs) <{overflowFlags = 3 : i32}> : (i8, i8) -> i8
    // CHECK:      %[[LHS:.*]] = "llvm.mlir.constant"() <{"value" = 1 : i8}> : () -> i8
    // CHECK-NEXT: %[[RHS:.*]] = "llvm.mlir.constant"() <{"value" = 2 : i8}> : () -> i8
    // CHECK-NEXT: %[[WIDE_LHS:.*]] = "gmir.g_anyext"(%[[LHS]]) : (i8) -> i64
    // CHECK-NEXT: %[[WIDE_RHS:.*]] = "gmir.g_anyext"(%[[RHS]]) : (i8) -> i64
    // CHECK-NEXT: "gmir.g_mul"(%[[WIDE_LHS]], %[[WIDE_RHS]]) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"({{.*}}) : (i64) -> i8

    // Signed division and remainder sign-extend their operands. Division is widened to `i32` only,
    // and then custom-legalized.
    // TODO: Lower function call arguments / results before legalization.
    // This might reduce the amount of artifacts omitted here.
    %sdiv = "gmir.g_sdiv"(%lhs, %rhs) <{isExact}> : (i8, i8) -> i8
    // CHECK:      "gmir.g_anyext"({{.*}}) : (i8) -> i64
    // CHECK-NEXT: "gmir.g_sext_inreg"({{.*}}) <{"sz" = 8 : i64}> : (i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"({{.*}}) : (i64) -> i32
    // CHECK-NEXT: "gmir.g_anyext"({{.*}}) : (i8) -> i64
    // CHECK-NEXT: "gmir.g_sext_inreg"({{.*}}) <{"sz" = 8 : i64}> : (i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"({{.*}}) : (i64) -> i32
    // CHECK:      "riscv.divw"({{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    // CHECK:      "gmir.g_trunc"({{.*}}) : (i32) -> i8
    %srem = "gmir.g_srem"(%lhs, %rhs) : (i8, i8) -> i8
    // CHECK:      "gmir.g_anyext"({{.*}}) : (i8) -> i64
    // CHECK-NEXT: "gmir.g_sext_inreg"({{.*}}) <{"sz" = 8 : i64}> : (i64) -> i64
    // CHECK-NEXT: "gmir.g_anyext"({{.*}}) : (i8) -> i64
    // CHECK-NEXT: "gmir.g_sext_inreg"({{.*}}) <{"sz" = 8 : i64}> : (i64) -> i64
    // CHECK-NEXT: "gmir.g_srem"({{.*}}) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"({{.*}}) : (i64) -> i8

    // Unsigned division and remainder zero-extend their operands.
    %udiv = "gmir.g_udiv"(%lhs, %rhs) : (i8, i8) -> i8
    // CHECK:      "gmir.g_constant"() <{"value" = 255 : i64}> : () -> i64
    // CHECK-NEXT: "gmir.g_anyext"({{.*}}) : (i8) -> i64
    // CHECK-NEXT: "gmir.g_and"({{.*}}) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"({{.*}}) : (i64) -> i32
    // CHECK-NEXT: "gmir.g_constant"() <{"value" = 255 : i64}> : () -> i64
    // CHECK-NEXT: "gmir.g_anyext"({{.*}}) : (i8) -> i64
    // CHECK-NEXT: "gmir.g_and"({{.*}}) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"({{.*}}) : (i64) -> i32
    // CHECK:      "riscv.divuw"({{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    // CHECK:      "gmir.g_trunc"({{.*}}) : (i32) -> i8

    // Widths that are not a power of two are widened to `i32` directly.
    %x_i3 = "llvm.mlir.constant"() <{value = 1 : i3}> : () -> i3
    %urem3 = "gmir.g_urem"(%x_i3, %x_i3) : (i3, i3) -> i3
    // CHECK:      %[[MASK_LHS:.*]] = "gmir.g_constant"() <{"value" = 7 : i64}> : () -> i64
    // CHECK-NEXT: %[[EXT_LHS:.*]] = "gmir.g_anyext"({{.*}}) : (i3) -> i64
    // CHECK-NEXT: %[[AND_LHS:.*]] = "gmir.g_and"(%[[EXT_LHS]], %[[MASK_LHS]]) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"(%[[AND_LHS]]) : (i64) -> i32
    // CHECK-NEXT: %[[MASK_RHS:.*]] = "gmir.g_constant"() <{"value" = 7 : i64}> : () -> i64
    // CHECK-NEXT: %[[EXT_RHS:.*]] = "gmir.g_anyext"({{.*}}) : (i3) -> i64
    // CHECK-NEXT: %[[AND_RHS:.*]] = "gmir.g_and"(%[[EXT_RHS]], %[[MASK_RHS]]) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"(%[[AND_RHS]]) : (i64) -> i32
    // CHECK:      "riscv.remuw"({{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    // CHECK:      "gmir.g_trunc"({{.*}}) : (i32) -> i3

    "test.test"(%mul64, %sdiv64, %udiv64, %srem64, %urem64) : (i64, i64, i64, i64, i64) -> ()
    "test.test"(%mul32, %sdiv32, %udiv32, %srem32, %urem32) : (i32, i32, i32, i32, i32) -> ()
    "test.test"(%mul, %sdiv, %srem, %udiv, %urem3) : (i8, i8, i8, i8, i3) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
