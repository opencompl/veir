// RUN: veir-opt %s -p=legalize-riscv64,isel-riscv64,reconcile-cast | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    %x = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    // An `i32` `g_add` is legalized to an `i64` `g_add` followed by `g_trunc` + `g_sext`, which is
    // selected as a single `addw`.
    %add = "gmir.g_add"(%x, %x) : (i32, i32) -> i32
    // CHECK: "riscv.addw"({{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    // CHECK-NOT: "riscv.sextw"
    "test.test"(%add) : (i32) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
