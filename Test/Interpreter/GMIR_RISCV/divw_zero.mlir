// RUN: veir-interpret %s | filecheck %s

// `g_divw` reads only the low 32 bits of its divisor, so a divisor with a zero low word is UB.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i64}> ({
    // 0x00000000:00000001
    %one = "llvm.mlir.constant"() <{ "value" = 1 : i64 }> : () -> i64
    // 0x00000001:00000000
    %high = "llvm.mlir.constant"() <{ "value" = 4294967296 : i64 }> : () -> i64
    %r = "gmir_riscv.g_divw"(%one, %high) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
