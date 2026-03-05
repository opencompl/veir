// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %lhs = "arith.constant"() <{ "value" = 7 : i32 }> : () -> i32
  %rhs = "arith.constant"() <{ "value" = 2 : i32 }> : () -> i32
  %x = "arith.divui"(%lhs, %rhs) <{exact}> : (i32, i32) -> i32
  "func.return"(%x) : (i32) -> ()
}) : () -> ()

// CHECK: Program output: #[poison]
