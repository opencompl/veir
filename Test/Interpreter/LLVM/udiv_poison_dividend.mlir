// RUN: veir-interpret %s | filecheck %s

// Regression check: a poison dividend with a concrete safe (nonzero) divisor
// propagates as poison — NOT immediate UB.
"builtin.module"() ({
  %five = "llvm.mlir.constant"() <{ "value" = 5 : i32 }> : () -> i32
  %neg1 = "llvm.mlir.constant"() <{ "value" = -1 : i32 }> : () -> i32
  %one  = "llvm.mlir.constant"() <{ "value" = 1 : i32 }> : () -> i32
  %poison = "llvm.add"(%neg1, %one) <{nuw}> : (i32, i32) -> i32
  %y = "llvm.udiv"(%poison, %five) : (i32, i32) -> i32
  "func.return"(%y) : (i32) -> ()
}) : () -> ()

// CHECK: Program output: #[poison]
