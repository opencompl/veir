// RUN: veir-interpret %s | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=isel-riscv64 | veir-interpret | filecheck %s

// The wide casts must preserve bit 100. Narrow casts can pass through a register:
// truncation discards bit 100, and any-extension may choose zero for new bits.
"builtin.module"() ({
  "func.func"() <{function_type = () -> (i128, i129, i64, i129), sym_name = "main"}> ({
    %wide129 = "llvm.mlir.constant"() <{value = 0x10000000000000000000000000 : i129}> : () -> i129
    %wide128 = "llvm.mlir.constant"() <{value = 0x10000000000000000000000000 : i128}> : () -> i128
    %low64 = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> i64
    %wide_trunc = "gmir.g_trunc"(%wide129) : (i129) -> i128
    %wide_ext = "gmir.g_anyext"(%wide128) : (i128) -> i129
    %narrow_trunc = "gmir.g_trunc"(%wide129) : (i129) -> i64
    %narrow_ext = "gmir.g_anyext"(%low64) : (i64) -> i129
    "func.return"(%wide_trunc, %wide_ext, %narrow_trunc, %narrow_ext) : (i128, i129, i64, i129) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000010000000000000000000000000#128, 0x000000010000000000000000000000000#129, 0x0000000000000000#64, 0x00000000000000000ffffffffffffffff#129]
