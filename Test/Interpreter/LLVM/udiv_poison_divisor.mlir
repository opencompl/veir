// RUN: veir-interpret %s | filecheck %s

// Unsigned division by a poison divisor is immediate UB: the poison value
// could refine to 0, so the operation could be division by zero.
"builtin.module"() ({
  %lhs  = "llvm.mlir.constant"() <{ "value" = 130 : i32 }> : () -> i32
  %neg1 = "llvm.mlir.constant"() <{ "value" = -1 : i32 }> : () -> i32
  %one  = "llvm.mlir.constant"() <{ "value" = 1 : i32 }> : () -> i32
  // -1 + 1 with `nuw` on i32 unsigned-overflows -> poison i32.
  %poison = "llvm.add"(%neg1, %one) <{nuw}> : (i32, i32) -> i32
  %y = "llvm.udiv"(%lhs, %poison) : (i32, i32) -> i32
  "func.return"(%y) : (i32) -> ()
}) : () -> ()

// CHECK: Undefined behavior
