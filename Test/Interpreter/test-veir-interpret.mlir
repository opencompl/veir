// RUN: veir-interpret %s | filecheck %s

// CHECK: Program output: #[0]
"builtin.module"() ({
  %lhs = "arith.constant"() : () -> i32
  %rhs = "arith.constant"() : () -> i32
  %x = "arith.addi"(%lhs, %rhs) : (i32, i32) -> i32
  "func.return"(%x) : (i32) -> ()
}) : () -> ()
