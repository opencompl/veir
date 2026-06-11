// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i8}> ({
    %lhs = "llvm.mlir.constant"() <{ "value" = 3 : i8 }> : () -> i8
    %rhs = "llvm.mlir.constant"() <{ "value" = 5 : i8 }> : () -> i8
    %cmp = "llvm.icmp"(%lhs, %rhs) <{ predicate = 2 : i64 }> : (i8, i8) -> i8
    "func.return"(%cmp) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.icmp: Expected i1 result
