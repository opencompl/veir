// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<i32 ()>, sym_name = "f"}> ({
    %0 = "llvm.mlir.constant"() <{value = 13 : i32}> : () -> i32
    "func.return"(%0) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: func.return: Expected func.return to be enclosed by func.func
