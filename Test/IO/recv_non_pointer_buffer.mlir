// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    %peer = "test.test"() : () -> !io.address
    %len = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %n = "io.recv"(%peer, %len, %len) : (!io.address, i64, i64) -> i64
    // CHECK: io.recv: Expected operand 1 to have !llvm.ptr type
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
