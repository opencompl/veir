// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    %x_i32 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %x = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %trunc = "gmir.g_trunc"(%x) : (i64) -> i32
    // CHECK:      "builtin.unrealized_conversion_cast"({{.*}}) : (i64) -> !riscv.reg
    // CHECK-NEXT: "builtin.unrealized_conversion_cast"({{.*}}) : (!riscv.reg) -> i32
    %anyext = "gmir.g_anyext"(%x_i32) : (i32) -> i64
    // CHECK:      "builtin.unrealized_conversion_cast"({{.*}}) : (i32) -> !riscv.reg
    // CHECK-NEXT: "builtin.unrealized_conversion_cast"({{.*}}) : (!riscv.reg) -> i64
    "test.test"(%trunc, %anyext) : (i32, i64) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
