// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %lhs = "arith.constant"() <{ "value" = 130 : i32 }> : () -> i32
  %rhs = "arith.constant"() <{ "value" = 3 : i32 }> : () -> i32
  %zero = "arith.constant"() <{ "value" = 0 : i32 }> : () -> i32
  %negthree = "arith.constant"() <{ "value" = -3 : i32 }> : () -> i32
  %negtwo = "arith.constant"() <{ "value" = -2 : i32 }> : () -> i32
  %x = "arith.divui"(%lhs, %rhs) : (i32, i32) -> i32
  %y = "arith.divui"(%lhs, %zero) : (i32, i32) -> i32
  %a = "arith.divui"(%negthree, %negtwo) : (i32, i32) -> i32
  "func.return"(%x, %y, %a) : (i32, i32, i32) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000002b#32, poison, 0x00000000#32]
