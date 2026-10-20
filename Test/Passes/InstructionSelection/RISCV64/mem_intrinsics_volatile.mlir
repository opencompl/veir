// RUN: veir-opt %s -p=riscv | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    %dst = "llvm.mlir.zero"() : () -> !llvm.ptr
    %fill = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    %len = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    "llvm.intr.memset"(%dst, %fill, %len) <{isVolatile = true}> : (!llvm.ptr, i8, i64) -> ()
    // CHECK: "riscv.sb"({{.*}}) <{"value" = 0 : i64, volatile_}>
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
