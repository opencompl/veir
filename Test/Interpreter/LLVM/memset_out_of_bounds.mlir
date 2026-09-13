// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i64}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %nine = "llvm.mlir.constant"() <{value = 9 : i64}> : () -> i64
    %byte = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %a = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    "llvm.intr.memset"(%a, %byte, %nine) <{isVolatile = false}> : (!llvm.ptr, i8, i64) -> ()
    %r = "llvm.load"(%a) : (!llvm.ptr) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
