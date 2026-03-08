// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %three = "arith.constant"() <{ "value" = 3 : i32 }> : () -> i32
  %five = "arith.constant"() <{ "value" = 5 : i32 }> : () -> i32
  %eight = "arith.constant"() <{ "value" = 8 : i32 }> : () -> i32
  %negseven = "arith.constant"() <{ "value" = -7 : i32 }> : () -> i32
  %x = "arith.ori"(%three, %five) <{disjoint}> : (i32, i32) -> i32
  %y = "arith.ori"(%eight, %negseven) <{disjoint}> : (i32, i32) -> i32
  %z = "arith.ori"(%three, %eight) <{disjoint}> : (i32, i32) -> i32
  "func.return"(%x, %y, %z) : (i32, i32, i32) -> ()
}) : () -> ()

// CHECK: Program output: #[poison, poison, 0x0000000b#32]
