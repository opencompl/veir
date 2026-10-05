// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    %len = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %buf = "llvm.alloca"(%len) <{elem_type = i8}> : (i64) -> !llvm.ptr
    %n, %from = "io.recv"(%buf, %len) : (!llvm.ptr, i64) -> (i64, i32)
    // CHECK: io.recv: Expected result 1 to have !io.address type
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
