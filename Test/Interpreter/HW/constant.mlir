// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %pos = "hw.constant"() <{ "value" = 3 : i32 }> : () -> i32
  %zero = "hw.constant"() <{ "value" = 0 : i32 }> : () -> i32
  %neg = "hw.constant"() <{ "value" = -4 : i32 }> : () -> i32
  "func.return"(%pos, %zero, %neg) : (i32, i32, i32) -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000003#32, 0x00000000#32, 0xfffffffc#32]
