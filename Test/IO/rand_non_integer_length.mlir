// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    %len = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %buf = "llvm.alloca"(%len) <{elem_type = i8}> : (i64) -> !llvm.ptr
    "io.rand"(%buf, %buf) : (!llvm.ptr, !llvm.ptr) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: io.rand: Expected operand 1 to have integer type
