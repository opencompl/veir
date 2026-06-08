// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i16}> ({
    %lhs = "llvm.mlir.constant"() <{ "value" = 3 : i8 }> : () -> i8
    %rhs = "llvm.mlir.constant"() <{ "value" = 5 : i8 }> : () -> i8
    %sum = "llvm.add"(%lhs, %rhs) : (i8, i8) -> i16
    "func.return"(%sum) : (i16) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.add: Expected result type to match operand type
