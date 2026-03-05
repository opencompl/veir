// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %zero = "llvm.constant"() <{ "value" = 0 : i32 }> : () -> i32
  %lhs = "llvm.constant"() <{ "value" = 3 : i32 }> : () -> i32
  %rhs = "llvm.constant"() <{ "value" = 2 : i32 }> : () -> i32
  %thirtytwo = "llvm.constant"() <{ "value" = 32 : i32 }> : () -> i32
  %x = "llvm.shl"(%lhs, %rhs) : (i32, i32) -> i32
  %p = "llvm.shl"(%zero, %thirtytwo) : (i32, i32) -> i32
  "func.return"(%x, %p) : (i32, i32) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000c#32, poison]
