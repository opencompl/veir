// RUN: veir-interpret %s | filecheck %s

// `srem intMin, -1` is immediate UB (signed overflow in the implicit division).
"builtin.module"() ({
  %intmin = "llvm.mlir.constant"() <{ "value" = -2147483648 : i32 }> : () -> i32
  %negone = "llvm.mlir.constant"() <{ "value" = -1 : i32 }> : () -> i32
  %y = "llvm.srem"(%intmin, %negone) : (i32, i32) -> i32
  "func.return"(%y) : (i32) -> ()
}) : () -> ()

// CHECK: Undefined behavior
