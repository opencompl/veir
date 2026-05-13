// RUN: veir-interpret %s | filecheck %s

// `sdiv intMin, -1` is immediate UB (signed overflow of the quotient).
"builtin.module"() ({
  %intmin = "llvm.mlir.constant"() <{ "value" = -2147483648 : i32 }> : () -> i32
  %negone = "llvm.mlir.constant"() <{ "value" = -1 : i32 }> : () -> i32
  %y = "llvm.sdiv"(%intmin, %negone) : (i32, i32) -> i32
  "func.return"(%y) : (i32) -> ()
}) : () -> ()

// CHECK: Undefined behavior
