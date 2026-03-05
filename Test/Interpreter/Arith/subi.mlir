// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %lhs = "arith.constant"() <{ "value" = 5 : i32 }> : () -> i32
  %rhs = "arith.constant"() <{ "value" = 3 : i32 }> : () -> i32
  %x = "arith.subi"(%lhs, %rhs) : (i32, i32) -> i32
  "func.return"(%x) : (i32) -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000002#32]
