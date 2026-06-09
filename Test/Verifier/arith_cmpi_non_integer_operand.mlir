// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = () -> i1, sym_name = "main"}> ({
    %lhs = "llvm.mlir.constant"() <{ "value" = 1.0 : f64 }> : () -> f64
    %rhs = "llvm.mlir.constant"() <{ "value" = 1.0 : f64 }> : () -> f64
    %cmp = "arith.cmpi"(%lhs, %rhs) <{ predicate = 2 : i64 }> : (f64, f64) -> i1
    "func.return"(%cmp) : (i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: arith.cmpi: Expected operand 0 to have integer type
