// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    %peer = "test.test"() : () -> !io.address
    %len = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %buf = "llvm.alloca"(%len) <{elem_type = i8}> : (i64) -> !llvm.ptr
    %n = "io.rand"(%peer, %buf, %len) : (!io.address, !llvm.ptr, i64) -> i64
    // CHECK: io.rand: Expected 2 operand(s)
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
