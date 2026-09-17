// RUN: veir-opt %s -p=isel-sdag-riscv64 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "binop_constants", function_type = (i64, i32) -> (i64, i64, i64, i32)}> ({
  ^bb0(%x: i64, %y: i32):
    %minusOne = "llvm.mlir.constant"() <{value = 18446744073709551615 : i64}> : () -> i64
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %sum = "llvm.add"(%x, %minusOne) : (i64, i64) -> i64
    %masked = "llvm.and"(%x, %minusOne) : (i64, i64) -> i64
    %shifted = "llvm.shl"(%x, %one) : (i64, i64) -> i64
    %one32 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %sum32 = "llvm.add"(%y, %one32) : (i32, i32) -> i32
    "func.return"(%sum, %masked, %shifted, %sum32) : (i64, i64, i64, i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @binop_constants
// CHECK: "riscv.addi"({{.*}}) <{"value" = -1 : i64}>
// CHECK: "riscv.andi"({{.*}}) <{"value" = -1 : i64}>
// CHECK: "riscv.slli"({{.*}}) <{"value" = 1 : i64}>
// CHECK: "riscv.addiw"({{.*}}) <{"value" = 1 : i64}>
