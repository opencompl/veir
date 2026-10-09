// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %x = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %slt = "gmir.g_icmp"(%x, %x) <{predicate = 2 : i64}> : (i64, i64) -> i64
    // CHECK: "riscv.slt"({{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %eqz = "gmir.g_icmp"(%x, %zero) <{predicate = 0 : i64}> : (i64, i64) -> i64
    // CHECK: "riscv.sltiu"({{.*}}) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
    // An `i1` result is not legal, so it is not selected.
    %i1 = "gmir.g_icmp"(%x, %x) <{predicate = 2 : i64}> : (i64, i64) -> i1
    // CHECK: "gmir.g_icmp"({{.*}}) <{"predicate" = 2 : i64}> : (i64, i64) -> i1
    "test.test"(%slt, %eqz, %i1) : (i64, i64, i1) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
