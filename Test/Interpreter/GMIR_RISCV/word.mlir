// RUN: veir-interpret %s | filecheck %s

// The word operations read only the low 32 bits of their operands and sign-extend the 32-bit
// result. The word addition, subtraction and multiplication wrap. A word shift reads only the low
// 5 bits of its amount.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i64, i64, i64, i64, i64, i64, i64, i64, i64)}> ({
    // 0x00000000:00000001
    %one = "llvm.mlir.constant"() <{ "value" = 1 : i64 }> : () -> i64
    // 0x00000001:00000002
    %two = "llvm.mlir.constant"() <{ "value" = 4294967298 : i64 }> : () -> i64
    // 0x00000000:80000000
    %sign = "llvm.mlir.constant"() <{ "value" = 2147483648 : i64 }> : () -> i64
    // 0x00000000:0000001f
    %max = "llvm.mlir.constant"() <{ "value" = 31 : i64 }> : () -> i64
    // 0x00000000:00000021
    %over = "llvm.mlir.constant"() <{ "value" = 33 : i64 }> : () -> i64
    %addw = "gmir_riscv.g_addw"(%sign, %sign) : (i64, i64) -> i64
    %subw = "gmir_riscv.g_subw"(%one, %two) : (i64, i64) -> i64
    %mulw = "gmir_riscv.g_mulw"(%sign, %one) : (i64, i64) -> i64
    %divw = "gmir_riscv.g_divw"(%sign, %one) : (i64, i64) -> i64
    %divuw = "gmir_riscv.g_divuw"(%sign, %two) : (i64, i64) -> i64
    %remuw = "gmir_riscv.g_remuw"(%two, %two) : (i64, i64) -> i64
    %sllw = "gmir_riscv.g_sllw"(%one, %over) : (i64, i64) -> i64
    %srlw = "gmir_riscv.g_srlw"(%sign, %max) : (i64, i64) -> i64
    %sraw = "gmir_riscv.g_sraw"(%sign, %max) : (i64, i64) -> i64
    // The high word of the shifted value is not shifted into the low word.
    %srlw_high = "gmir_riscv.g_srlw"(%two, %one) : (i64, i64) -> i64
    "func.return"(%addw, %subw, %mulw, %divw, %divuw, %remuw, %sllw, %srlw, %sraw, %srlw_high)
        : (i64, i64, i64, i64, i64, i64, i64, i64, i64, i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000000#64, 0xffffffffffffffff#64, 0xffffffff80000000#64, 0xffffffff80000000#64, 0x0000000040000000#64, 0x0000000000000000#64, 0x0000000000000002#64, 0x0000000000000001#64, 0xffffffffffffffff#64, 0x0000000000000001#64]
