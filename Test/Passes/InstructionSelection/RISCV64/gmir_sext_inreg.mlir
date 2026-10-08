// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    %x = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %sext32 = "gmir.g_sext_inreg"(%x) <{sz = 32 : i64}> : (i64) -> i64
    // CHECK: "riscv.sextw"({{.*}}) : (!riscv.reg) -> !riscv.reg
    %sext16 = "gmir.g_sext_inreg"(%x) <{sz = 16 : i64}> : (i64) -> i64
    // CHECK: "riscv.sexth"({{.*}}) : (!riscv.reg) -> !riscv.reg
    %sext8 = "gmir.g_sext_inreg"(%x) <{sz = 8 : i64}> : (i64) -> i64
    // CHECK: "riscv.sextb"({{.*}}) : (!riscv.reg) -> !riscv.reg
    // Size 7 is not legal, so it is not selected.
    %sext7 = "gmir.g_sext_inreg"(%x) <{sz = 7 : i64}> : (i64) -> i64
    // CHECK: "gmir.g_sext_inreg"({{.*}}) <{"sz" = 7 : i64}> : (i64) -> i64
    "test.test"(%sext32, %sext16, %sext8, %sext7) : (i64, i64, i64, i64) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
