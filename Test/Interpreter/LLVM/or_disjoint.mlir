// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %three = "llvm.constant"() <{ "value" = 3 : i32 }> : () -> i32
  %five = "llvm.constant"() <{ "value" = 5 : i32 }> : () -> i32
  %eight = "llvm.constant"() <{ "value" = 8 : i32 }> : () -> i32
  %negseven = "llvm.constant"() <{ "value" = -7 : i32 }> : () -> i32
  %x = "llvm.or"(%three, %five) <{disjoint}> : (i32, i32) -> i32
  %y = "llvm.or"(%eight, %negseven) <{disjoint}> : (i32, i32) -> i32
  %z = "llvm.or"(%three, %eight) <{disjoint}> : (i32, i32) -> i32
  "func.return"(%x, %y, %z) : (i32, i32, i32) -> ()
}) : () -> ()

// CHECK: Program output: #[poison, poison, 0x0000000b#32]
