// RUN: veir-interpret %s | filecheck %s
// RUN: veir-interpret --ctree %s | filecheck %s

// `g_clzw` and `g_ctzw` count in the low 32 bits of their operand, so a zero low word counts 32,
// whatever the high word.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i64, i64, i64)}> ({
    // 0x00000001:00000000
    %high = "llvm.mlir.constant"() <{ "value" = 4294967296 : i64 }> : () -> i64
    // 0xffffffff:00000001
    %one = "llvm.mlir.constant"() <{ "value" = -4294967295 : i64 }> : () -> i64
    // 0x00000000:80000000
    %sign = "llvm.mlir.constant"() <{ "value" = 2147483648 : i64 }> : () -> i64
    %clzw_zero = "gmir_riscv.g_clzw"(%high) : (i64) -> i64
    %clzw_one = "gmir_riscv.g_clzw"(%one) : (i64) -> i64
    %ctzw_zero = "gmir_riscv.g_ctzw"(%high) : (i64) -> i64
    %ctzw_sign = "gmir_riscv.g_ctzw"(%sign) : (i64) -> i64
    "func.return"(%clzw_zero, %clzw_one, %ctzw_zero, %ctzw_sign) : (i64, i64, i64, i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000020#64, 0x000000000000001f#64, 0x0000000000000020#64, 0x000000000000001f#64]
