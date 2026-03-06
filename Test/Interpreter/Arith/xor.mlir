// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %three = "llvm.constant"() <{ "value" = 3 : i32 }> : () -> i32
  %five = "llvm.constant"() <{ "value" = 5 : i32 }> : () -> i32
  %eight = "llvm.constant"() <{ "value" = 8 : i32 }> : () -> i32
  %negseven = "llvm.constant"() <{ "value" = -7 : i32 }> : () -> i32
  %x = "llvm.xor"(%three, %five) : (i32, i32) -> i32
  %y = "llvm.xor"(%eight, %negseven) : (i32, i32) -> i32
  %z = "llvm.xor"(%three, %eight) : (i32, i32) -> i32
  "func.return"(%x, %y, %z) : (i32, i32, i32) -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000006#32, 0xfffffff1#32, 0x0000000b#32]
