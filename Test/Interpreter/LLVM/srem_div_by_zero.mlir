// RUN: veir-interpret %s | filecheck %s

// Signed remainder with a concrete zero divisor is immediate UB.
"builtin.module"() ({
  %lhs = "llvm.mlir.constant"() <{ "value" = 7 : i32 }> : () -> i32
  %zero = "llvm.mlir.constant"() <{ "value" = 0 : i32 }> : () -> i32
  %y = "llvm.srem"(%lhs, %zero) : (i32, i32) -> i32
  "func.return"(%y) : (i32) -> ()
}) : () -> ()

// CHECK: Undefined behavior
