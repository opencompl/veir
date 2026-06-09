// RUN: veir-opt %s | filecheck %s

// llvm.select accepts values of any type, including floats.

"builtin.module"() ({
  "func.func"() <{function_type = () -> f64, sym_name = "main"}> ({
    %cond = "arith.constant"() <{ "value" = 1 : i1 }> : () -> i1
    %lhs = "llvm.mlir.constant"() <{ "value" = 1.0 : f64 }> : () -> f64
    %rhs = "llvm.mlir.constant"() <{ "value" = 1.0 : f64 }> : () -> f64
    %sel = "llvm.select"(%cond, %lhs, %rhs) : (i1, f64, f64) -> f64
    "func.return"(%sel) : (f64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.select"(%{{.*}}, %{{.*}}, %{{.*}}) : (i1, f64, f64) -> f64
