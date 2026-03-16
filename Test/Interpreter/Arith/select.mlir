// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %lhs = "arith.constant"() <{ "value" = 3 : i32 }> : () -> i32
  %rhs = "arith.constant"() <{ "value" = 0 : i32 }> : () -> i32
  %true = "arith.constant"() <{ "value" = 1 : i1 }> : () -> i1
  %false = "arith.constant"() <{ "value" = 0 : i1 }> : () -> i1
  %x = "arith.select"(%true, %lhs, %rhs) : (i1, i32, i32) -> i32
  %y = "arith.select"(%false, %lhs, %rhs) : (i1, i32, i32) -> i32
  "func.return"(%x, %y) : (i32, i32) -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000003#32, 0x00000000#32]
