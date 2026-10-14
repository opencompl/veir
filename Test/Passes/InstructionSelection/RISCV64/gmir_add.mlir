// RUN: veir-opt %s -p=llvm-to-gmir,legalize-riscv64,isel-riscv64,reconcile-cast | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    %x = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %add = "gmir.g_add"(%x, %x) : (i64, i64) -> i64
    // CHECK: "riscv.add"({{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "test.test"(%add) : (i64) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
