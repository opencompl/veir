// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    %len = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %buf = "llvm.alloca"(%len) <{elem_type = i8}> : (i64) -> !llvm.ptr
    %dest = "arith.constant"() <{value = 7 : i32}> : () -> i32
    %n = "io.send"(%dest, %buf, %len) : (i32, !llvm.ptr, i64) -> i64
    // CHECK: io.send: Expected operand 0 to have !io.address type
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
