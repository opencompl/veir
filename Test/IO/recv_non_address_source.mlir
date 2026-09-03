// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    %len = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %buf = "llvm.alloca"(%len) <{elem_type = i8}> : (i64) -> !llvm.ptr
    %n = "io.recv"(%len, %buf, %len) : (i64, !llvm.ptr, i64) -> i64
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: io.recv: Expected operand 0 to have !io.address type
