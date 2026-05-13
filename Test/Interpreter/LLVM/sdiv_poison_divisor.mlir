// RUN: veir-interpret %s | filecheck %s

// Signed division by a poison divisor is immediate UB.
"builtin.module"() ({
  %lhs  = "llvm.mlir.constant"() <{ "value" = 7 : i32 }> : () -> i32
  %neg1 = "llvm.mlir.constant"() <{ "value" = -1 : i32 }> : () -> i32
  %one  = "llvm.mlir.constant"() <{ "value" = 1 : i32 }> : () -> i32
  %poison = "llvm.add"(%neg1, %one) <{nuw}> : (i32, i32) -> i32
  %y = "llvm.sdiv"(%lhs, %poison) : (i32, i32) -> i32
  "func.return"(%y) : (i32) -> ()
}) : () -> ()

// CHECK: Undefined behavior
