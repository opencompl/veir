// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %lhs = "arith.constant"() <{ "value" = 130 : i32 }> : () -> i32
  %rhs = "arith.constant"() <{ "value" = 3 : i32 }> : () -> i32
  %negthree = "arith.constant"() <{ "value" = -3 : i32 }> : () -> i32
  %negtwo = "arith.constant"() <{ "value" = -2 : i32 }> : () -> i32
  %x = "arith.remui"(%lhs, %rhs) : (i32, i32) -> i32
  %a = "arith.remui"(%negthree, %negtwo) : (i32, i32) -> i32
  "func.return"(%x, %a) : (i32, i32) -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000001#32, 0xfffffffd#32]
