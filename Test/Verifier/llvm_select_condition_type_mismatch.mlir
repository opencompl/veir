// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i8}> ({
    %cond = "llvm.mlir.constant"() <{ "value" = 1 : i8 }> : () -> i8
    %lhs = "llvm.mlir.constant"() <{ "value" = 3 : i8 }> : () -> i8
    %rhs = "llvm.mlir.constant"() <{ "value" = 5 : i8 }> : () -> i8
    %sel = "llvm.select"(%cond, %lhs, %rhs) : (i8, i8, i8) -> i8
    "func.return"(%sel) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.select: Expected i1 condition
