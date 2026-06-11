// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = () -> i1, sym_name = "main"}> ({
    %lhs = "arith.constant"() <{ "value" = 3 : i32 }> : () -> i32
    %rhs = "llvm.mlir.constant"() <{ "value" = 1.0 : f64 }> : () -> f64
    %cmp = "arith.cmpi"(%lhs, %rhs) <{ predicate = 2 : i64 }> : (i32, f64) -> i1
    "func.return"(%cmp) : (i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: arith.cmpi: Expected operand 1 to have integer type
