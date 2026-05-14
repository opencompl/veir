// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %lhs = "hw.constant"() <{ "value" = 3 : i32 }> : () -> i32
  %rhs = "hw.constant"() <{ "value" = 5 : i32 }> : () -> i32
  %x = "comb.add"(%lhs, %rhs) : (i32, i32) -> i32
  "func.return"(%x) : (i32) -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000008#32]
