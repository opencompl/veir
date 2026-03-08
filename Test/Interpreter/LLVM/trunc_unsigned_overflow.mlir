// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  // 255 fits in i8 unsigned: zext(trunc(255)) == 255, no poison
  %c255 = "llvm.constant"() <{ "value" = 255 : i32 }> : () -> i32
  // 256 does not fit in i8 unsigned: zext(trunc(256)) == 0 != 256, poison
  %c256 = "llvm.constant"() <{ "value" = 256 : i32 }> : () -> i32
  %a = "llvm.trunc"(%c255) <{nuw}> : (i32) -> i8
  %b = "llvm.trunc"(%c256) <{nuw}> : (i32) -> i8
  "func.return"(%a, %b) : (i8, i8) -> ()
}) : () -> ()

// CHECK: Program output: #[0xff#8, poison]
