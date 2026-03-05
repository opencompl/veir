// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %lhs = "arith.constant"() <{ "value" = 7 : i32 }> : () -> i32
  %rhs = "arith.constant"() <{ "value" = 2 : i32 }> : () -> i32
  %zero = "arith.constant"() <{ "value" = 0 : i32 }> : () -> i32
  %negone = "arith.constant"() <{ "value" = -1 : i32 }> : () -> i32
  %negthree = "arith.constant"() <{ "value" = -3 : i32 }> : () -> i32
  %negtwo = "arith.constant"() <{ "value" = -2 : i32 }> : () -> i32
  %x = "arith.divsi"(%lhs, %rhs) : (i32, i32) -> i32
  %y = "arith.divsi"(%lhs, %zero) : (i32, i32) -> i32
  %z = "arith.divsi"(%lhs, %negone) : (i32, i32) -> i32
  %a = "arith.divsi"(%negthree, %negtwo) : (i32, i32) -> i32
  "func.return"(%x, %y, %z, %a) : (i32, i32, i32, i32) -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000003#32, poison, 0xfffffff9#32, 0x00000001#32]
