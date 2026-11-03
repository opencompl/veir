// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    %len = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %n, %from = "io.recv"(%len, %len) : (i64, i64) -> (i64, !io.address)
    // CHECK: io.recv: Expected operand 0 to have !llvm.ptr type
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
