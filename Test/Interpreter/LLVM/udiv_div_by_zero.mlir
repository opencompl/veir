// RUN: veir-interpret %s | filecheck %s

// Unsigned division with a concrete zero divisor is immediate UB.
"builtin.module"() ({
  %lhs = "llvm.mlir.constant"() <{ "value" = 130 : i32 }> : () -> i32
  %zero = "llvm.mlir.constant"() <{ "value" = 0 : i32 }> : () -> i32
  %y = "llvm.udiv"(%lhs, %zero) : (i32, i32) -> i32
  "func.return"(%y) : (i32) -> ()
}) : () -> ()

// CHECK: Undefined behavior
