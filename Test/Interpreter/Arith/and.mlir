// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %three = "arith.constant"() <{ "value" = 3 : i32 }> : () -> i32
  %five = "arith.constant"() <{ "value" = 5 : i32 }> : () -> i32
  %eight = "arith.constant"() <{ "value" = 8 : i32 }> : () -> i32
  %negseven = "arith.constant"() <{ "value" = -7 : i32 }> : () -> i32
  %x = "arith.andi"(%three, %five) : (i32, i32) -> i32
  %y = "arith.andi"(%eight, %negseven) : (i32, i32) -> i32
  %z = "arith.andi"(%three, %eight) : (i32, i32) -> i32
  "func.return"(%x, %y, %z) : (i32, i32, i32) -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000001#32, 0x00000008#32, 0x00000000#32]
