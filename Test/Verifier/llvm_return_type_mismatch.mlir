// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<i16 ()>, sym_name = "f"}> ({
    %0 = "llvm.mlir.constant"() <{value = 13 : i32}> : () -> i32
    "llvm.return"(%0) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.return operand 0 type does not match the function's declared result type
