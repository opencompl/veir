// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %zero = "arith.constant"() <{ "value" = 0 : i32 }> : () -> i32
  %lhs = "arith.constant"() <{ "value" = 3 : i32 }> : () -> i32
  %rhs = "arith.constant"() <{ "value" = 2 : i32 }> : () -> i32
  %thirtytwo = "arith.constant"() <{ "value" = 32 : i32 }> : () -> i32
  %x = "arith.shli"(%lhs, %rhs) : (i32, i32) -> i32
  %p = "arith.shli"(%zero, %thirtytwo) : (i32, i32) -> i32
  "func.return"(%x, %p) : (i32, i32) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000c#32, poison]
