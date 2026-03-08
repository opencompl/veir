// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %c255 = "llvm.constant"() <{ "value" = 255 : i8 }> : () -> i8
  %cneg = "llvm.constant"() <{ "value" = -1 : i8 }> : () -> i8
  %a = "llvm.zext"(%c255) : (i8) -> i32
  %b = "llvm.zext"(%cneg) : (i8) -> i32
  "func.return"(%a, %b) : (i32, i32) -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000ff#32, 0x000000ff#32]
