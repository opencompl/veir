// RUN: veir-interpret %s | filecheck %s

// A `llvm.intr.memset` that runs past the end of its object is UB.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %nine = "llvm.mlir.constant"() <{value = 9 : i64}> : () -> i64
    %byte = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    "llvm.intr.memset"(%p, %byte, %nine) <{isVolatile = false}> : (!llvm.ptr, i8, i64) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
