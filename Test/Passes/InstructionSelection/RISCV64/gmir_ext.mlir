// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    %x = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %sext = "gmir.g_sext"(%x) : (i32) -> i64
    // CHECK: "riscv.sextw"({{.*}}) : (!riscv.reg) -> !riscv.reg
    %zext = "gmir.g_zext"(%x) : (i32) -> i64
    // CHECK: "riscv.zextw"({{.*}}) : (!riscv.reg) -> !riscv.reg
    "test.test"(%sext, %zext) : (i64, i64) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
